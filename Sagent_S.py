#Sagent_S_Agent - - - Python Serial (Time history) Analysis Agent 
#                   Part of Python the Iceberg Knowledge System
from tkinter import Tk,Canvas,Frame,BOTH,LEFT,TOP,Button,Text,Label,W,E,Entry
from tkinter import StringVar,OptionMenu,RIGHT,BOTTOM,Menu
from tkinter.filedialog import askopenfilename, asksaveasfile, asksaveasfilename
from datetime import datetime, timezone
import matplotlib.pyplot as plt
from sklearn import linear_model
import smtplib # for sending email
import csv, sys
import pandas as pd
import numpy as np
import scipy.signal as sps
import math
import statistics
import ctypes
import iceberg as ice
import pyautogui
import warnings
import time
import os
from pytz import UTC
import easygui
import json
import logging
import subprocess
import ntpath
#from references import ref_S
from pynput.mouse import Controller
from influxdb_client import InfluxDBClient
from influxdb_client.extras import pd, np

''' OS dependency do not work for exit need something like following
if os.name == 'nt':  #windows systems
    import win32api
    def on_exit(sig, func=None):
        print('Exiting Sagent_S')
    win32api.SetConsoleCtrlHandler( on_exit, True)
elif os.name == 'posix': # Linux systems
    import signal
    def on_exit(sig, func=None):
        print('Exiting Sagent_S')
    signal.signal(signal.SIGTERM, on_exit)
'''

# Enable InfluxDB logging for DataFrame serializer
loggerSerializer = logging.getLogger('influxdb_client.client.write.dataframe_serializer')
loggerSerializer.setLevel(level=logging.DEBUG)
handler = logging.StreamHandler()
handler.setFormatter(logging.Formatter('%(asctime)s | %(message)s'))
loggerSerializer.addHandler(handler)

the_mouse = Controller()
warnings.filterwarnings("ignore", category=DeprecationWarning)
  
Sagent_S_version=1.12 # current version Serial Smart Agent (Sagent_S)  
# Separator = '#'  # Tilda Separator used for referencing information in text streams
debugit = True # turn on/off debug printing  
if debugit:
    import pdb
pos_record = False  #trun on to record mouse pos in macros
auto_df = pd.DataFrame(columns=['proc','parm'], dtype=object)
SAGcommand='' #start in unsolicited mode
last_mark = 0  #last marker position set
text_id='none'
tbeg=0
wheel=0
tend=100
num_inserts=0
loaded=False
MAXFILT=1023
screen_text=[] #list of screen text items to add after plotting
macro=[]
chans=[]
filter_level=3   # 3=low rate (default) 2=mediun  1=high  0=brickwall
df_is_str=[]

WIDE = 3         # width in pixels of displayed channel data lines  was 3
NOM  =-999.111   # defines not to display a given Marker (no marker)
NOTOP=-1         # for when there is no displayed channels
top=NOTOP
Sagent_S_df=pd.DataFrame()
k=np.zeros(33) #K values (32 indexed) to use within Sagent_S, k[0]=<num loaded chans>
app_high = 750 #was 750
app_wide = 1280
xpix=[50,app_wide-35] #X dims draw canvas area [start,end,width]
ypix=[120,app_high-35] #Y dims draw canvas area [start,end,width]

wo = [0,0, 1000, 100]  #world coord canvas after tgrids(for x) & y_scale(for y)

ncolor = 16 #number of channel colors in cmap, last two are special
pp=[0,8,2,4,6,1,3,5,7,0,8,2,4,6,1,3,5,7,0,4,0,4,0,4] #xloc*130 positions of disp ch scale
chd=0 #num channels displayed
cnums_disp=[] #list of displayed chan names
bot_scale=[] #list of bottom grid scalings of chans
top_scale=[] #list of top grid scalings of  chans
markers=[NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,\
        NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM,NOM]
marker=NOM
ch=[]  #use in modeling "m" command for value at channel instantanious calculations
tidx=0
xchan=0
ychan=0
keywords={}  #keyword dictionary
num_keywords=0 #no keywords initially

def resamps( base, inc, time): # get adjustments to resample time
    last_time = len(time)-1
    #end is the reasonable last resampled time
    last_time = time[last_time]
    end=int((last_time-base+inc/2)/inc)*inc+base
    rem = end-last_time
    if rem< (inc/2): #last_new is negative so subtract rem
        x=1
def fix_ice_text( entry_text ): # replace `icenames` with icevalues
    i=0
    text=''
    while i < len(entry_text):
        if entry_text[i]=='`': #replace ice_name with ice_value
            ice_name=''
            i += 1
            ice_name = ''
            while entry_text[i] != '`' and i<len(entry_text):
                ice_name += entry_text[i]
                i += 1
            # now insert ice value into text
            ice_value = ice.ice[ice_name]
            for k in range(0,len(ice_value)):
                text += ice_value[k]
        else:
            text += entry_text[i]
        i += 1
    return( text)
def os_dependent(): #supports windows (nt) vs linux dependencies
    if os.name == 'nt':
        print('Windows code')
    elif os.name == 'posix':
        print('Linux code')
def process_proc_ref( procref, proctext):
    return( procref )
def process_parm_ref( parmref, parmtext ):
    refs = parmref.split(',')
    txt = parmtext.split(',')
    size = len(refs)
    newtxt=''
    for i in range(0,size):
        if i>0:
            newtxt = newtxt+','
        if refs[i] == '1':
            text = easygui.enterbox( 'enter: '+txt[i])
            newtxt = newtxt+text
        elif refs[i] == '3':
            fname=askopenfilename(filetypes=(("CSV files", "*.csv"),\
                            ("All files", "*.*")), title= txt[i])
            newtxt = newtxt+fname
        else:
            newtxt = newtxt+txt[i]
    return( parmref, newtxt )
def factor_cut( input, size, start, inc):
    for i in range(0, size):
        fv = (input[i]-start)/inc
        if fv >= 0:
            input[i]= fv
        else:
            input[i]= int(fv-1.0)
        input[i] = input[i]*inc + start + inc/2.0
    return( input)
# = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
#  Access layer for all Sagent_S processing, whether manual or automatic
# = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
def process_S( SAGcommand, txt, manual ): 
    global wheel, alocation, time_ch, chans, units
    global tend,tbeg,top,Sagent_S_df, tidx, xchan, samprate,topname
    global mymodel,order, model_type, ychan, indeps, depend,xsave, ysave
    global knumber, filter_level, num_inserts
    global loaded,  NOTOP, df_is_str, fpart

    if manual: #record event only if manual for later automatic processing
        text =fix_ice_text( txt)
        process_record( SAGcommand, txt)
    else: #automatic processing
        txt = fix_ice_text( txt)  # translate icenames to icevalues
        txt1 = SAGcommand.split(ice.Separator)
        SAGcommand = txt1[1]
        text = fix_ice_text( txt1[1])
        proc_ref = process_proc_ref( txt1[0], txt1[1])
        txt2 = txt.split(ice.Separator)
        if txt==ice.Separator:
            parm_ref=''
            text=''
        else:
            parm_ref, text = process_parm_ref( txt2[0], txt2[1])
    if SAGcommand=='scale_top':  #--------------------scale bottom, grid of top 
        tx = text.split(',') 
        bottom = float(tx[0]) 
        grids = float(tx[1]) 
        bot_scale[top-1]=bottom
        top_scale[top-1]=bot_scale[top-1]+6*grids
        ReDraw()  
    elif SAGcommand=='scale_time':           #--------------------scale_time
        tx = text.split(',') 
        tbeg = float(tx[0]) 
        tend = float(tx[1])    
        tgrids(tbeg,tend)
        ReDraw() 
    elif SAGcommand=='sort':                   #---Sort dataframe by a channel
        chlist = list(Sagent_S_df.columns)
        if text in chlist: #is channel in data?
            Sagent_S_df=Sagent_S_df.sort_values(by=text, ascending=True)
            ReDraw()
            message('Dataframe sorted by='+text)
        else:
            message('Error: Channel Name is not in dataframe')
    elif SAGcommand=='rename':                   #----------rename top channel
        size = len(chans)
        chlist = topname.split(',')
        ch_name = chlist[1]
        chnum = int(chlist[0])-1
        chans[chnum]= str(chnum+1)+','+text
        Sagent_S_df.rename(columns={ch_name:text}, inplace=True)
        delete_top()
        chan_select(str(chnum+1)+','+text)
        load_chans(chans) 
    elif SAGcommand=='grid_bot':               #----------- set bottom grid
        offset = float(text) - bot_scale[top-1]
        top_scale[top-1] += offset
        bot_scale[top-1]=float(text)
        ReDraw()   
    elif SAGcommand=='equation':                #--------------- Equation =
        message('result='+str(eval(text)))
    elif SAGcommand=='insert':                #--------------- Insert a channel
        samples = len(Sagent_S_df.index)
        last_chan = len(chans)
        new_list = [0]*samples # create a zerod list
        num_inserts += 1
        new_name = 'insert'+str(num_inserts)
        Sagent_S_df.insert( last_chan, new_name, new_list, True)
        full_name=str(last_chan+1)+','+new_name
        chan_select(full_name) # make it Top displayed
        chans = list(Sagent_S_df.columns)
        units.append('none')
        for i in range(0,len(chans)): # add numbers to chan names
            chans[i] = str(i+1)+','+str(chans[i]) 
        load_chans(chans)
        fix_dtypes( Sagent_S_df ) # inserted as a numeric, not string
    elif SAGcommand=='show_chan':              # ---- show channel command  
        if text.isdigit():
            if int(text) <= len(chans):
                chan_select( chans[int(text)-1])
                txt = 'Channel '+text+' is now the top channel.'
                message(txt)
            else:
                message('That channel number does not exist')
        else: # load a named channel
            for i in range( 0, len(chans)):
                [num,name] = chans[i].split(',')
                if name.lower() == text.lower():
                    txt = 'Channel '+text+' is now the top channel.'
                    message(txt)
                    chan_select( chans[i])
    elif SAGcommand=='regress':                   #------ regress altI
        tx = text.split(',')             
        indeps = get_ch_names( tx[0], Sagent_S_df)
        depend = get_ch_names( tx[1], Sagent_S_df)
        Sagent_S.reg_fit( indeps, depend)
        print(indeps,'-->',depend)
    elif SAGcommand=='relate':                          #-------- relate - B
        print('text=',text)
        tx = text.split(',') 
        xchan = int(tx[0]) -1
        ychan = int(tx[1]) -1                        
        order = int(tx[2])
        xnum,xname = channel_splits(xchan)
        ynum,yname = channel_splits(ychan)
        print('xname0=',xname[0],' yname0=',yname[0])
        print('len xname ',len(xname))
        x1 = getlist(xname)           
        y1 = getlist( yname)
        plt.xlabel(xname)
        plt.ylabel(yname)  
        plt.scatter( x1, y1, color='black') # plot it
        if order>0: # if model, create model fitting stuff in Red         
            [yprime,rstat,mymodel] = Sagent_S.get_model( x1, y1, order)
            model_title ='Model( order='+str(order)+' )= '+ice.strlist(mymodel)+\
                        '        R='+str(rstat)
            print(model_title)
            plt.title(model_title)
            print(mymodel)
            plt.grid()
            plt.plot( x1, yprime, color='red')
        else:
            plt.title('Relationship Between Channels'+xname+' and '+yname)
        plt.show()
    elif SAGcommand=='rolloff':                     #--------Set filter Rolloff     
        filter_level = int(text)  
        message('filter_level='+str(filter_level))
    elif SAGcommand=='filter':                     #---------- Lowpass filter      
        cutoff = float(text) 
        coef = get_coeff( filter_level, 'l', samprate, cutoff, 0.0)
        convolve_top(coef)
        ReDraw() 
        clear_status()
    elif SAGcommand=='notch':                     #---------- notch filter      
        cutoff = float(text) 
        coef = get_coeff( filter_level, 'l', samprate, cutoff, 0.0)
        convolve_top(coef)
        ReDraw() 
        clear_status()
    elif SAGcommand=='median':                     #----- median (width) filter      
        width = int(text) 
        median_filter( width )
        ReDraw() 
        clear_status()
    elif SAGcommand=='highpass':                   #---------- highpass filter      
        cutoff = float(text) 
        coef = get_coeff( filter_level, 'h', samprate, cutoff, 0.0)
        convolve_top(coef)
        ReDraw() 
        clear_status()                       
    elif SAGcommand=='correlate':                # ---------------- correlate
        tx = text.split(',')
        xchan = int(tx[0])-1                   
        xnum,name1 = channel_splits(xchan)
        ynum,name2 = channel_splits(int(tx[1])-1)
        x1 = Sagent_S_df[name1].values.tolist() # ref. data
        x2 = Sagent_S_df[name2].values.tolist() # shift data
        samples = len(x2)
        rvals=[0]*21
        xvals=[0]*21
        ref = []
        for j in range(10,samples-10): # create ref. minus 21 samples
            ref.append( x1[j] ) 
        rmax=0
        rshmax=0
        for xshift in range(-10,11): # create shifted from x2
            xsh = []
            for j in range(10,samples-10): # create shift data
                xsh.append( x2[j+xshift])
            rcoff = np.corrcoef(ref,xsh)
            rstat = round(rcoff[1,0],4)
            if rmax<rstat:
                rshmax = xshift 
                rmax = rstat
            rvals[xshift+10] = rstat
            xvals[xshift+10] = xshift
        plt.xlabel('Samples Shifting Amount')
        plt.ylabel('R') 
        plt.scatter(xvals,rvals)
        plt.title('Correlation of R given Xshift')
        plt.grid()
        plt.show()  
        fig = plt.gcf()
        fig.set_size_inches(11.0, 8.5)
        fig.savefig('correlate.png', dpi=100) 
        secs = ice.tidy(rshmax/samprate, 5)
        mesg = 'Shift seen was '+str(rshmax)+' samples='+str(secs)+' secs'  
        message( mesg )
    elif SAGcommand=='Delete':
        delete_top()
    elif SAGcommand=='Up':
        idiv = (top_scale[top-1]-bot_scale[top-1])/6
        bot_scale[top-1] += idiv
        top_scale[top-1] += idiv
        ReDraw()
    elif SAGcommand=='Down':
        idiv = (top_scale[top-1]-bot_scale[top-1])/6
        bot_scale[top-1] -= idiv
        top_scale[top-1] -= idiv
        ReDraw()  
    elif SAGcommand=='grid_space':              #------ set spacing of top grids 
        top_scale[top-1]=bot_scale[top-1]+6*float(text)
        ReDraw()  
    elif SAGcommand=='kval':                      # -------------------- kval
        tx = text.split(',') 
        knumber = int(tx[0]) 
        k[knumber]= float(tx[1])
    elif SAGcommand=='shift_top':               # ---------- time shift channel           
        if Sagent_S.shift_time( text ):
            ReDraw() 
            clear_status()
    elif SAGcommand=='set_samprate':                # ---------- set sample rate
        samprate = float( text )
        msg = 'Sample rate is now '+str(samprate)
        message( msg)
    elif SAGcommand=='edit_top':                      # --------------- edit top
        [xx,yy] = pyautogui.position() # get mouse position
        xsave2 = trans_xw( xx-9 )
        ysave2 = trans_yw( yy-38 ) # zz -38? why not same as click?
        ix1 = trans_xpos( xsave)
        ix2 = trans_xpos( xsave2)
        if ix2<=ix1: # single point edit for ix1
            Sagent_S_df.iloc[ ix1,top-1] = ysave
            ReDraw() 
        else: # edit interpelate a line of points from ix1 to ix2
            for ix in range(ix1,ix2):
                yval = (ysave*(ix2-ix) + ysave2*(ix-ix1))/(ix2-ix1)
                Sagent_S_df.iloc[ ix,top-1] = yval
            ReDraw() 
        clear_status()            
    elif SAGcommand=='model':                       #-------model the top channel
        for tidx in range(0,len(Sagent_S_df.index)):
            x =  time_ch[tidx] 
            y =  Sagent_S_df.iloc[tidx,top-1] 
            ch = [0] * (len(Sagent_S_df.columns)+1) # creat ch[] list
            for j in range(0,len(Sagent_S_df.columns)): 
                ch[j+1] = Sagent_S_df.iloc[tidx,j] # collect chan data at point
            Sagent_S_df.iloc[tidx,top-1]= float(eval(text)) # do eval
        clear_status() 
        ReDraw() 
    elif SAGcommand=='question':                       #----A question was asked
        result = ice.get_help( text)
        print_Sagent_help(  result )
        #message('Information for :     '+text)             
    elif SAGcommand=='factor':                         #----factor the top channel
        factor_top( text )
        ReDraw() 
        clear_status() 
    elif SAGcommand=='mark_time':            #----set a marker to a index position
        tx = text.split(',') 
        last_mark =  float(tx[1])
        markers[int(tx[0])] = last_mark                  
        ReDraw() 
        clear_status()         
    elif SAGcommand=='snapshot':                      #--------print the screen
        clear_status()
        fname = text+'.bmp'
        hwnd = win32gui.FindWindow( None, 'Sagent_S')
        wDC = win32gui.GetWindowDC(hwnd)
        dcObj=win32ui.CreateDCFromHandle(wDC)
        cDC=dcObj.CreateCompatibleDC()
        dataBitMap = win32ui.CreateBitmap()
        dataBitMap.CreateCompatibleBitmap(dcObj, app_wide+16,app_high+37)
        cDC.SelectObject(dataBitMap)
        cDC.BitBlt((0,0),(app_wide+16,app_high+37) , dcObj, (0,0), win32con.SRCCOPY)
        dataBitMap.SaveBitmapFile(cDC,fname)
        dcObj.DeleteDC()  # Free Resources
        cDC.DeleteDC()
        win32gui.ReleaseDC(hwnd, wDC)
        win32gui.DeleteObject(dataBitMap.GetHandle()) 
        message('Screenshot is '+fname)  
    elif SAGcommand=='overview':                      #--------==---time Overview  
        tbeg = time_ch[0]
        samples = len(Sagent_S_df.index)
        tend = 1./samprate*samples 
        message('Setting to overview')
        tgrids(tbeg,tend)
        ReDraw() 
    elif SAGcommand=='mouse1':                       #--------mouse1 left click 
        tx = text.split(',')
        if loaded and top!=NOTOP:
            xw = trans_xw( int(tx[0]))
            yw = trans_yw( int(tx[1]))
            idx = trans_p( xw)
            topname = chans[top-1]
            if wo[3]-wo[1]>10000:
                dig=0
            elif wo[3]-wo[1]>1000:
                dig=1
            elif wo[3]-wo[1]>100:
                dig=2
            else: # <= 100
                dig=3            
            valu = round( Sagent_S_df.iloc[idx,top-1], dig)
            if units[top-1]=='none':
                unit = ''
            else:
                unit = units[top-1]
            if  df_is_str[top-1]: # is it a string type channel?
                tex='x= '+str(round(xw,3))+'   y= '+str(round(yw,dig))+'     '+\
                    str(topname)+' [ '+str(idx)+' ] = '+keywords.get(int(valu))+' '+unit
            else:
                tex = 'x= '+str(round(xw,3))+'   y= '+str(round(yw,dig))+'     '+\
                            str(topname)+' [ '+str(idx)+' ] = '+str(valu)+'  '+unit
            message(tex)
    elif SAGcommand=='mouse2':                       #--------mouse2 middle click 
        tx = text.split(',') 
        new_perc = 1 - wheel/3000.0
        tbeg = wo[0]
        tend = wo[2]
        trange = ice.tidy(tend-tbeg,5)
        new_trange = ice.tidy(trange * new_perc,5)
        xtime = alocation[0]
        nbeg = ice.tidy(xtime - new_trange/2.0, 5)
        nend = ice.tidy( nbeg + new_trange, 5)
        tbeg = nbeg
        tend = nend
        tgrids( tbeg, tend)
        old_trange = top_scale[top-1] - bot_scale[top-1]
        new_trange = ice.tidy(old_trange * new_perc,5)
        bot_scale[top-1]=ice.tidy(alocation[1] - new_trange/2.0 , 5)
        grid_dist = ice.tidy(new_trange/6.0,5)     # calculate grid distance
        top_scale[top-1] = bot_scale[top-1]+6*grid_dist    # always 6 grid lines
        wheel = 0 # reset wheel value to 0
        ReDraw() 
    elif SAGcommand=='wheel':                      #--------mouse wheel event 
        tx = text.split(',')         
        wheel += int(tx[2])
        xtime = trans_xw( int(tx[0]))
        yval  = trans_yw( int(tx[1]))
        alocation = [xtime,yval]
        messg = 'Zoom = '+str(int(wheel/30))+' %\t\t(Press Middle to Activate)'
        message( messg )
    elif SAGcommand=='mouse3':                      #--------mouse3 right click 
        tx = text.split(',')
        message( 'Mouse3 event not implemented') 
    elif SAGcommand=='save_CSV':                    #---- save dataframe to file 
        savename = text
        Sagent_S_df.to_csv(savename, index=False, line_terminator='\n')
    elif SAGcommand=='autoscale':                   #------- autoscale top channel
        chlist = topname.split(',')
        idx=int(chlist[0])
        chan_name=chlist[1]
        ch_scale(chan_name,idx)
        ReDraw()
    elif SAGcommand=='open_CSV':                   #-------------open a CSV file 
        if loaded: # need to delete all Sagent_S_df data zzz
            print('starting over new df')
            Sagent_S_df=pd.DataFrame()
            chans=[]
            num_inserts=0
            tbeg=0
            tend=100
            top=NOTOP
            num_inserts=0
            print('All df data dropped')
        fname = text
        if fname[0]=='`': #replace as icename
            fname=''
            for i in range(1,len(text)):
                if text[i]=='`':
                    break;
                fname += text[i] 
            fname = ice.ice[fname]
        else:
            fname = text
        fpart = ntpath.basename( fname )
        [Sagent_S_df,chans, Sagent_app.units]=read_header_csv(fname) 
        fix_dtypes( Sagent_S_df )
        loaded=True
        samples = len(Sagent_S_df.index) 
        for i in range(0,len(chans)): # add other stuff to dataframe
            chans[i] = str(i+1)+','+chans[i] # add number to names                            
        c0 = list(Sagent_S_df.iloc[:,0])
        dsize = len(c0)
        delta1 = c0[1]-c0[0]
        if dsize<11:
            delta10=-1 # not enough data for calculating time channel
        else:
            delta10 = c0[10]-c0[0]
            delta1=delta10/10
        if delta1<=0 or delta10<=0:
            samprate=100
            rate_acc=1 # which means not a time channel
        else:
            samprate = ice.tidy(1.0/delta1,4)
            rate_acc = samprate -10/delta10
        rate_acc = abs(rate_acc)
        samprate = ice.tidy( samprate, 4)
        if rate_acc > .0001: # not fixed time channel, so create one 100hz
            [cnum,cname] = chans[0].split(',')
            if cname.lower()=='time':  #------if its named time, then fudge it
                trange = c0[len(c0)-1]-c0[0]
                samprate = ice.tidy(samples/trange, 4)
                print('channel "time" seen, sample rate set to ',samprate)
            else:
                samprate =100  # no choice, just set to 100hz
                if debugit:
                    print('Bad samprate, Setting samrate to',samprate,' SpS')
            time_ch = []
            for i in range(0, samples):
                time_ch.append( i/samprate)
            tbeg=0
            tend=samples/samprate
        elif rate_acc > .001: # ragged data, so time alline the data 
            if debugit:
                print('zz finish linearizing ragged data')
        else: # use the time data provided on channel index=1 (chnum==0)
            time_ch = list(Sagent_S_df.iloc[:,0]) 
            tbeg=c0[0]
            tend=c0[samples-1] 
            trange = tend-tbeg
            if trange <= 10:
                tbeg = math.floor(tbeg)
                tend = math.ceil( tend)
            elif trange<= 100:
                tbeg = math.floor(tbeg/5)*5
                tend = math.ceil( tend/5)*5
            elif trange<= 1000:
                tbeg = math.floor(tbeg/10)*10
                tend = math.ceil( tend/10)*10
            elif trange<= 10000:
                tbeg = math.floor(tbeg/100)*100
                tend = math.ceil( tend/100)*100 
            else:
                tbeg = math.floor(tbeg/1000)*1000
                tend = math.ceil( tend/1000)*1000 
            trange = tend-tbeg
        load_chans(chans) 
        tgrids(tbeg,tend)
        loaded=True
        message('samprate='+str(samprate)+' Samples='+str(samples)) 
    elif SAGcommand=='end_trigger':    #------ end macro if trigger fails -------
        tcom = text.split(',')                                
    elif SAGcommand=='marker':          #------------ Marker Commands ----------- 
        mcom = text.split(',')
        marker=int(mcom[0]) 
        if mcom[1] == 'use':
            markers[marker]=last_mark # set marker to last_mark position
        if mcom[1] == 'max':
            last_mark = top_max_pos()
            markers[marker] = last_mark
        if mcom[1] == 'min':
            last_mark = top_min_pos()
            markers[marker] = last_mark
        elif mcom[1] == 'put':
            if mcom[2]=='index':
                markers[marker]=int(mcom[3])
                last_mark = mcom[3]
            elif mcom[2]=='time':
                last_mark = trans_xpos( float(mcom[3]))
                markers[marker]=last_mark
            elif mcom[2]=='marker':  # set to another marker
                last_mark = markers[int(mcom[3])]
                markers[marker]=last_mark
            elif mcom[2]=='begin':  # set to begining
                last_mark = 0
                markers[marker]=last_mark
            elif mcom[2]=='end':  # set to ending
                last_mark = len(Sagent_S_df.index)-1
                markers[marker]=last_mark
        elif mcom[1] == 'off': # turn off a marker
            markers[marker]=NOM
        elif mcom[1] == 'right': # right movement commands
            if mcom[2]=='time':  # move by time
                last_mark = markers[marker] + trans_xpos( float(mcom[3]))
                markers[marker] = last_mark
            elif mcom[2]=='lmin': # to local min value
                last_mark = top_lmin_pos_right( markers[marker])
                markers[marker]=last_mark
            elif mcom[2]=='lmax':  # to local max value
                last_mark = top_lmax_pos_right( markers[marker])
                markers[marker]=last_mark
            elif mcom[2]=='above':  # until above value
                last_mark=top_above_pos_right( markers[marker], float(mcom[3]))
                markers[marker]=last_mark
            elif mcom[2]=='below':  # until below value
                last_mark=top_below_pos_right( markers[marker], float(mcom[3]))
                markers[marker]=last_mark    
        elif mcom[1] == 'left': # left movement commands
            if mcom[2]=='time':  # move by time
                last_mark = markers[marker] - trans_xpos( mcom[3])
                if last_mark < 0:
                    last_mark = 0
                markers[marker] = last_mark
            elif mcom[2]=='lmin': # to local min value
                last_mark = top_lmin_pos_left( markers[marker])
                markers[marker]=last_mark
            elif mcom[2]=='lmax':  # to local max value
                last_mark = top_lmax_pos_left( markers[marker])
                markers[marker]=last_mark
            elif mcom[2]=='above':  # until above value
                last_mark=top_above_pos_left( markers[marker], float(mcom[3]))
                markers[marker]=last_mark
            elif mcom[2]=='below':  # until below value
                last_mark=top_below_pos_left( markers[marker], float(mcom[3]))
                markers[marker]=last_mark  
        clear_status()
        Sagent_app.hentry.delete(0,99)
        ReDraw()
    elif SAGcommand=='to_influxdb':   #------ store dataframe to InfluxDB -----
        dt = datetime(2021, 11, 2)
        first = dt.replace(tzinfo=timezone.utc)
        _now = datetime.now(UTC)
        print('first=',first,' now=',_now)
        message("Ingesting DataFrame to InfluxDB named="+fpart+' ...') 
        org = ice.ice['influx_org']
        url = ice.ice['influx_url']
        token =  ice.ice['influx_token']
        bucket = ice.ice['influx_bucket']
        siz = len(Sagent_S_df['Date'])
        rng = pd.date_range(start=first, end=_now, periods=siz, tz='UTC')
        print('rng=',rng)
        Sagent_S_df.set_axis( rng, inplace=True)
        print(Sagent_S_df)
        with InfluxDBClient(url=url, token=token, org=org) as client:
            with client.write_api() as write_api:
                write_api.write(bucket=bucket, record=Sagent_S_df,
                                data_frame_tag_columns=['tag'],
                                data_frame_measurement_name=fpart)
        clear_status()
    elif SAGcommand=='run_python':   #----------------- run a python script
        # print('Python script un-implemented zz!')
        tx = text.split(',') 
        subprocess.call(['python.exe', tx[0] ] )
        ice.load_ice()  # re load ice after subprocess.call
    elif SAGcommand=='markers_off':   #--------------- turn off all markers        
        for i in range(0, len(markers)):
            markers[i]=NOM
    elif SAGcommand=='restore_top':   #--------------- restore the top list        
        restore_top()
    elif SAGcommand=='ice_marker': #--- insert ice from top marker position value
        tx = text.split(',') 
        index = markers[int(tx[1])]
        print('index=',index)
        value = Sagent_S_df.iloc[int(index),top-1]
        ice.put_ice( tx[0], value)
        ice.save_ice()        
    elif SAGcommand=='ice_insert':   #-----------insert ice value to ice.json 
        tx = text.split(',')
        if len(tx)>2:
            for i in range(2, len(tx)):
                tx[1]=tx[1]+','+tx[i]
        ice.put_ice( tx[0], tx[1])
        ice.save_ice()
        print('Inserting',tx[0],'=',tx[1])
    elif SAGcommand=='ice_dual_marker':   #----dual marker commands 
        tx = text.split(',')
        alist=toplist(False)
        icename = tx[0]
        mk1 = int(tx[1])
        mk2 = int(tx[2])
        oper=tx[3]
        if oper == 'average':
            value =  0
            num = 0
            for i in range(markers[mk1],markers[mk2]):
                value += alist[i]
                num += 1
            value = value/num
        elif oper == 'time':
            value = time_ch[markers[mk2]]-time_ch[markers[mk1]]
        elif oper == 'xbar': 
           print('xbar operation not implemented')
        ice.put_ice( icename, value)
        ice.save_ice()
    elif SAGcommand=='plot_text':   #----plot text on screen
        tx = text.split(',')
        screen_text.append( tx[0]+';'+tx[1]+';'+tx[2])
        ReDraw()  
    elif SAGcommand=='integrate':   #----integrate top channel
        integrate_simpsons_top( 1.0/samprate )
    elif SAGcommand=='derivative':  #----derivative of top channel
        dh = samprate/12.0
        coef = [dh, -8*dh, 0, 8*dh, -dh]
        convolve_top(coef)
    else: # unknown command
        print('unknown command: '+SAGcommand)

# = = = = = = = = = = = = = End of process_S() = = = = = = = = = = = = = = = =
def process_command(com_name):
    ref = ice.ref_S[com_name].split(ice.Separator) # ref[0]=num 1=params 2=text
    if ref[1]=='none': # no text command required
        process_S(com_name,ref[1],True)
    else:
         text_command( ref[2]+' - Enter: '+ref[1], com_name)
def s_error( number):
    print('Error',number)
def process_record( SAGcommand, text): # recording process for Sagent_S
    global pos_record, macro, auto_df
    if debugit:
        print('process=',SAGcommand,'  text=',text)
        print('reference=',ice.ref_S[SAGcommand])
    ref = ice.ref_S[SAGcommand].split(ice.Separator) # get process reference value
    if text=='':
        size=0
    else:
        tx = text.split(',') 
        size=len(tx)
    text2='0'
    for i in range(1,size):
        text2 = text2 +',0'
    text2 = text2+ice.Separator+text
    if pos_record:
        [xx,yy] = pyautogui.position()  # get mouse position
        xx =  xx-9 
        yy =  yy-38 
        msg='pos,'+str(xx)+','+str(yy)
        adf = pd.DataFrame( {'proc':['10'+ice.Separator+'pos'], 'parm':[msg]})
        auto_df = auto_df.append( adf, ignore_index=False)
    adf = pd.DataFrame( {'proc':[ref[0]+ice.Separator+SAGcommand], 'parm':[text2]})
    auto_df = auto_df.append( adf, ignore_index=True, sort=False)
# = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
def fix_dtypes( dframe ): # restructure to handle string data channel types 
    global df_is_str
    df_is_str = dframe.dtypes # save original data types for later use
    df_cols = dframe.columns
    for i in range(0,len(df_cols)):
        df_is_str[i]=isinstance( dframe.iloc[0,i], str)
        if  isinstance( dframe.iloc[0,i], str):
            slist = list(dframe.iloc[:,i]) # save old string list to convert       
            dframe[df_cols[i]] =\
                        pd.to_numeric(dframe[df_cols[i]],errors='coerce')
            for j in range(0,len(dframe[df_cols[i]])):
                dframe.iloc[j, i] = get_unique( slist[j])
def save_file():
    global fname, Sagent_S_df
    savename=asksaveasfile(mode='w',defaultextension=".csv")
    ('save_CSV',savename, True) 
def read_dict(fname):
    with open(fname,'r') as inf:
        help_dict= ast.literal_eval(inf.read())
def save_macro(): # save the stored analysis steps to Json file
    global fname, Sagent_S_df, auto_df
    json_name=asksaveasfilename(filetypes=[("Iceberg macro file", ".json")],\
                            defaultextension=".json")
    if json_name:  # user selected file
        auto_df.to_json(json_name,orient='records',lines=True)
    else: # user cancel the file browser window
        print("No file chosen")
def run_macro():
    global fname, Sagent_S_df, auto_df
    fname=askopenfilename(filetypes=(("Json files", "*.json"),\
                    ("All files", "*.*")))
    auto_df = pd.read_json( fname, orient='records', lines=True)
    size = len(auto_df.index)
    message('running json macro:  '+fname)
    for i in range(0,size):
        if debugit:
            time.sleep(1)
        proc = auto_df['proc'][i]
        parm = auto_df['parm'][i]
        process_S( proc, parm, False )
def run_process():
    global process_name
    print('running json macro=', process_name)
    auto_df = pd.read_json( process_name, orient='records', lines=True)
    size = len(auto_df.index)
    for i in range(0,size):
        if debugit:
            time.sleep(1)
        proc = auto_df['proc'][i]
        parm = auto_df['parm'][i]
        process_S( proc, parm, False )
    # exit after finished processing
    time.sleep(3.5)
    root.destroy()
def message( txt ):
    canvas.create_rectangle(app_wide-750,2,app_wide-10,18,\
                            outline=ice.cmap[17],fill=ice.cmap[17])     
    canvas.create_text( app_wide-430-len(txt)*3, 10, anchor=W,\
                                font="TkSmallCaptionFont",text=txt)                                   
    root.update() # so, otherwise status will not display for long run processing
    canvas.pack() 
def text_command( txt, mymode): # text_command() gets text into global text
    global SAGcommand,text_id       # then processing is from SA_Entry callback
    SAGcommand=mymode                # SAGcommand will be the processed command
    canvas.create_rectangle(app_wide-750,2,app_wide-10,18,\
                            outline=ice.cmap[17],fill=ice.cmap[17])     
    text_id=canvas.create_text( app_wide-430-len(txt)*3, 10, anchor=W,\
                                font="TkSmallCaptionFont",text=txt)                                   
    if mymode!='': 
        hent.focus()
    root.update() # so, otherwise status will not display for long run processing
    canvas.pack() 
def clear_status():
    canvas.create_rectangle(450,3,app_wide-2,19,outline=ice.cmap[17],fill=ice.cmap[17])
    SAGcommand='' # set to no mode
    root.focus_set()
def chan_select(chsel):
    global chd, DispMenu, TopVar,top,cnums_disp, topname,chan_name
    topname=chsel
    add_it=True
    for i in range(0,len(cnums_disp)):
        if cnums_disp[i]==chsel: # dont add something already there
            add_it=False
            ch_selected = i  # save the selection found
    if add_it: # ok to add it        
        if len(cnums_disp)>0:
            DispMenu.pack_forget()
            DispMenu.destroy()
        chlist = chsel.split(',')
        top=int(chlist[0])
        process_record('show_chan', chlist[1])
        chan_name=chlist[1]
        ch_plot(chan_name,top)
        txt = 'Displayed & Top Focus:'
        canvas.create_rectangle(270,2,449,20,outline=ice.cmap[17],fill=ice.cmap[17])     
        canvas.create_text(335, 10, anchor=W, font="TkSmallCaptionFont",text=txt)
        cnums_disp.append(chsel)
        chd=len(cnums_disp)
        TopVar = StringVar(canvas)            
        TopVar.set(cnums_disp[chd-1]) # default value  
        DispMenu = OptionMenu(canvas, TopVar, *cnums_disp,\
                            command=chan_display) 
        DispMenu.config(font=('TkSmallCaptionFont',(7)),width=24) 
        DispMenu.pack(side=TOP)     
        DispMenu.place( x=305,y=22)        
        canvas.pack()
    else: # channel already displayed, so bring it to Top 
        TopVar = StringVar(canvas)            
        TopVar.set(cnums_disp[ ch_selected]) # set top (default) value  
        DispMenu = OptionMenu(canvas, TopVar, *cnums_disp, command=chan_display) 
        DispMenu.config(font=('TkSmallCaptionFont',(7)),width=24) 
        DispMenu.pack(side=TOP)     
        DispMenu.place( x=305,y=22)        
        canvas.pack()
        chan_display(chsel) # set value to use in Sagent_S
def print_Sagent_help(  messg ):
    clear_status()
    clear_screen()
    canvas.create_text( xpix[0]+15, 397, anchor=W,\
                font="TkSmallCaptionFont",text=messg)
def display_ice( ):
    clear_status()
    clear_screen()
    yy=0
    header = '------- Iceberg Data (from ice.json) -------'
    the_font = ("Times", "12", "bold") # ('freemono bold',12)
    canvas.create_text( 600, 130, width=1000, font=the_font,text=header)
    for keyval, value in ice.ice.items():
        canvas.create_text( 60,200+yy,anchor=W, font=the_font, text=keyval+' : '+value)
        yy += 28
def print_Sagent_help2():
    canvas.create_text( xpix[0]+15, 300, anchor=W,\
                font="TkSmallCaptionFont",text=ice.Sagent_help2)
# = = = = = = = = = = = = = = = MATH Routines = = = = = = = = = = = = = = = = =
def integrate_top( h ): # trapazoid integration for now, zz to Simpsons instead
    alist=toplist(True)
    alen = len(alist)
    Sagent_S_df.iloc[0,top-1]=0
    last = alist[0]
    for tidx in range(1,alen):
        next = Sagent_S_df.iloc[tidx-1,top-1] + (alist[tidx]+last)/2 * h
        Sagent_S_df.iloc[tidx,top-1] = next
        print('next=',next,' ival=',(alist[tidx]+last)/2 * h)
        last = alist[tidx]
def integrate_simpsons_top( h ):     # integrate with simpsons rule */
    alist=toplist(True)   # get top list
    alen = len(alist)
    p1 = alist[0]
    alist[0]  = 0.        # assume zero starting point */
    for ix in range( 1, alen-1, 2):
        p2 = alist[ix]
        p3 = alist[ix+1]
        alist[ix]  = alist[ix-1] + (p1 + p2)/2. * h           # trapazoidal 
        alist[ix+1]= alist[ix-1] + (p1 + 4*p2 + p3)/3. * h    # simpson's 
        p1 = p3
    if (alen%2) == 0 :  # if even sized list, need to finish alen-1 value?
        alist[alen-1] = alist[alen-2] + (p1 + alist[alen-1])/2. * h        # trapazoidal 
    for tidx in range(0,alen):
        Sagent_S_df.iloc[tidx,top-1] = alist[tidx]          # put it back  
def p1_dif3( p1, p2, p3,  h):
    return( (4.*p2 - 3.*p1  - p3)/(2.*h) ) 
def p3_dif3( p1, p2, p3,  h):
    return( (p1 + 3.*p3 - 4.*p2)/(2.*h) )  
def cw_dif3( p1, p3,  h):
    return( (p3 - p1)/(2.*h) )  
def cw_dif5( p1, p2, p4, p5,  h):
    return( (p1 - 8.* p2 + 8.*p4 - p5)/(12.*h) )                        
def cw5_dif( alin, h):  # compute 5 point derivative of a channel of values
    s1=-1
    s2=-1
    s3=-1
    s4=-1
    bk1=0
    bk2=0
    bk3=0
    bk4=0
    sz=len(alin)
    if sz<2:
        return( alin)
    if sz==2:
        alin[0]=(alin[1]-alin[0])/h
        alin[1]=alin[0]
        return( alin)
    d1 = p1_dif3( alin[0], alin[1], alin[2], h)
    d2 = cw_dif3( alin[0], alin[2], h)
    e1 = p3_dif3( alin[sz-3], alin[sz-2], alin[sz-1], h)
    e2 = cw_dif3( alin[sz-3], alin[sz-1], h)
    if sz>4:
        w2 = 2
        for s in range(w2, sz-w2):
            if s4 != -1:
                alin[s4]=bk4
            s4=s3 
            bk4=bk3
            s3=s2 
            bk3=bk2
            s2=s1 
            bk2=bk1
            s1=s  
            bk1= cw_dif5(alin[s-2],alin[s-1],alin[s+1],alin[s+2],h)
        if s1>1 :
            alin[s1] = bk1
        if s2>1 :
            alin[s2] = bk2
        if s3>1 :
            alin[s3] = bk3
        if s4>1 :
            alin[s4] = bk4
    alin[0] = d1
    alin[1] = d2
    alin[sz-1] =e1
    alin[sz-2] =e2 
    return( alin)                    
def convolve_top( coef):
    alist=toplist(True)
    alen = len(alist)
    offset=int(len(coef)/2)
    for tidx in range(0,alen):
        tval=0
        for cidx in range(0, len(coef)):
            tloc = tidx-offset+cidx
            if tloc <0:
                tloc=0
            if tloc >= alen:
                tloc=alen-1
            tval += coef[cidx]*alist[tloc]
        Sagent_S_df.iloc[tidx,top-1]=tval
def interpb( px, px1,py1, px2,py2):
  return((py2-py1)*(px-px1)/(px2-px1) )
def pos( y):
    xbar = 0
    count=0
    size = len(y)
    for i in range(0,size): # find mean value
        xbar += y[i]
        count += 1
    xbar /= count
    for i in range(0,size):
        if y[i]<0:
            y[i]= - y[i]
    return(y)
def rms(  y):  # return the RMS of y
    size = len(y)
    if  y[0] > 0.:
        direct= 1.
    else:
        direct=-1.
    xbar = 0
    count=0
    for i in range(0,size): # find mean value
        xbar += y[i]
        count += 1
    xbar /= count
    for i in range(0,size): # remove the mean dc value
        y[i] -= xbar
    lastrms=0
    p2=0
    first = True
    while True:
        count=0.
        sum=0.
        p1=p2
        while (p2<size) and ((y[p2] * direct) >=0.):
            count += 1.
            sum += float(y[p2]) * float(y[p2]) # add the square value
            p2 += 1
        if count>0:
            rmsval = math.sqrt( sum/count)
        else:
            rmsval = 0
        for i in range(p1,p2):
            y[i]=  rmsval
        direct *= -1.
        if p2>= size:
            break
    return( y)

def LB_Clip( x0src,  y0src,  x1src,  y1src): # Draw  x/y clipping values for border
    global x0clip,y0clip,x1clip,y1clip       # Define the start and end points of the line.
    global x_max, y_max, x_min, y_min        # The output values, so declare these outside.
    t0 = 0
    t1 = 1
    xdelta = x1src-x0src
    ydelta = y1src-y0src
    for edge in range(0,4):    # Traverse through left, right, bottom, top edges.
        if (edge==0):
            p = -xdelta
            q = -(x_min-x0src)
        if (edge==1):
            p = xdelta
            q =  (x_max-x0src)
        if (edge==2):
            p = -ydelta
            q = -(y_min-y0src)
        if (edge==3):
            p = ydelta
            q =  (y_max-y0src)
        if p==0:
            p=.1
        r = q/p
        if  p==.1 and q<0:
            return False      # Don't draw line at all. (parallel line outside)
        if p < 0 :
            if r > t1 :
                return False  # Don't draw line at all.
            elif r > t0 :
                t0=r          # Line is clipped!
        elif p > 0 :
            if r < t0 :
                return False  # Don't draw line at all.
            elif r < t1 :
                t1=r          # Line is clipped!
    x0clip = round(x0src + t0*xdelta)
    y0clip = round(y0src + t0*ydelta)  # these are returned globals if clipped is True
    x1clip = round(x0src + t1*xdelta)
    y1clip = round(y0src + t1*ydelta)
    return True                 # (clipped) line is True
def clip_line( canvas, x1,y1,x2,y2, color, awidth):
    clipped = LB_Clip (  x1,y1,x2,y2 )
    if clipped:
        p = int(x0clip),int(y0clip),int(x1clip),int(y1clip)
        canvas.create_line( p, width=awidth, fill=color)
        return    
    return  # Not Clipped
def is_number(str):
    num=True
    for ch in str:
        if (ch.isnumeric() or ch=='.' or ch=='$' or ch=='-')==False:
            num=False
    return( num)
def check_csv_header( aname ):
    a_file = open( aname)
    hline=[True,True,True,True]
    hlen=[0,0,0,0]
    for i in range(0,4):
        line = a_file.readline()
        alist = line.split(",")
        hline[i] = not is_number(alist[0])
        hlen[i] = len(alist)
    a_file.close()
    hh=[]
    pos=0
    for i in range(0,3):
        if hlen[i]==0 and pos>0: # blank line not 1st line?
            pos += 1              # skip an inside blank line
        else:                     # not a blank line
            if hline[i] and hlen[i]>=hlen[i+1]:
                hh.append( pos)
                pos += 1
    return( hh )

def read_header_csv( aname ):
    global units
    hval = check_csv_header( aname)
    if len(hval)==0:
        df = pd.read_csv( aname )
        columns=[]
        for i in range(0, len(df.columns)): # rename colomns ch<n>
            columns.append('ch'+str(i+1))
    else:
        df = pd.read_csv( aname, header=hval )
        columns=list(df.columns)
        if len(hval)>1: # then units available
            mcol=list(df.columns)
            columns=[]
            units=[]
            for i in range(0,len(mcol)):
               columns.append(mcol[i][0])
               units.append(mcol[i][1])
        else:
            columns=list(df.columns)
            units=[]           
            for i in range(0,len(columns)):
                units.append('none') # no units specified                

    return( df, columns, units)
def get_key( val):   # return a numeric key for a dictionary string value
    global keywords  # reverse of dictionary lookup, for string values in dframe
    for key, value in keywords.items():
        if value == val:
            return key
    return 0  # 0 means not in dictionary
def get_unique( val):# return an integer for a unique val in keyword dictionary
    global keywords,num_keywords
    key = get_key( val) # if val does not exist, it is added to dictionary
    if key==0: # not there, so add new unique value to dictionary
        num_keywords += 1
        keywords[num_keywords]=val
        return num_keywords
    return key
def get_ch_names( text, df): # get channel number(s) or names into name list
    global chans
    lst = text.split(',')
    chans = list(df.columns)
    result=[]
    for i in range(0,len(lst)):        
        if lst[i].isnumeric():
            result.append( chans[ int(lst[i]) -1])
        else:
            result.append( lst[i])
    return( result ) 
def channel_splits( num): # given CHnum return bot CHnum,CHname
    global chans
    snum, chname = chans[num].split(',')
    chnum = int(snum)-1
    return chnum,chname 
def restore_top():
    global Sagent_S_df, last_top
    for tidx in range(0,len(last_top)):
        Sagent_S_df.iloc[tidx,top-1] = last_top[tidx]
def toplist( save_it ): # make a list from top channel
    global Sagent_S_df, last_top
    the_list=[]
    for tidx in range(0,len(Sagent_S_df.index)):
        the_list.append(Sagent_S_df.iloc[tidx,top-1])
    if save_it:
        last_top = the_list
    return( the_list)
def bessel0( x):
    kfact=1;
    k=1;
    thisx = x*x/4.
    last = thisx+1
    while k<100. and abs(thisx-last) > 1.0e-10:
        k += 1.
        kfact *= k
        last = thisx
        thisx += math.pow( 1./kfact * math.pow(x/2.,k), 2.)
    return 1.+thisx
def lippert(  num, roll, ripl ): # produce the Lippert window coefficients
    coef = [None] * (num+1)
    i=num/2;             # Note: a .0 ripl value nukes the edge coef.'s   
    beta = roll * math.sqrt( 1.-float(i)*float(i)/float(num)/float(num));
    side = bessel0(beta)/bessel0(roll);
    if side==0:
        side= NearZero;
    if ripl>=side:
        rip=1000.; # very high value will illiminate the effect 
    else:
        rip=.4;
        result = side *(rip+.5*math.cos(2.*math.pi*float(i)/float(num)))/(rip+.5)
        while result < ripl and rip<50:
            rip += .2
            result = side *(rip+.5*math.cos(2.*math.pi*float(i)/float(num)))/(rip+.5)
        for j in range(0, 20):
            rip -= .01
            result = side *(rip+.5*math.cos(2.*math.pi*float(i)/float(num)))/(rip+.5)
            if result<ripl:
                    break
        for j in range(0, 9):
            rip += .001;
            result = side *(rip+.5*math.cos(2.*math.pi*float(i)/float(num)))/(rip+.5)
            if result>ripl: 
                break
        for j in range(0, 9):
            rip += .0001
            result = side *(rip+.5*math.cos(2.*math.pi*float(i)/float(num)))/(rip+.5)
            if result<ripl:
                break
    coef[int(num/2)]=1.0
    for i in range(1, int(num/2)+1):
        beta = roll * math.sqrt( 1.-float(i)*float(i)/float(num)/float(num))
        coef[int(num/2)-i]= bessel0(beta)/bessel0(roll)\
                *(rip + .5*math.cos(2.*math.pi * float(i) / float(num)))/(rip+.5)
        coef[int(num/2)+i]= coef[int(num/2)-i]
    return coef
def median_filter( width):
    print( 'width of median filter was ', int(width))
    alist=toplist(True)
    alen = len(alist)
    halfwidth =int(int(width)/2.0)
    for tidx in range( halfwidth, alen-halfwidth):
        mean_val = 0
        for i in range(tidx-halfwidth, tidx+halfwidth+1):
            mean_val += alist[i]   # sum the filter section
        mean_val /= halfwidth*2+1  # to get xbar
        value = alist[tidx+halfwidth]
        for i in range(tidx-halfwidth, tidx+halfwidth):
            if abs(mean_val-value) > abs(mean_val-alist[i]): 
                value = alist[i] # set value to closest to xbar
        Sagent_S_df.iloc[tidx, top-1]=value 
        # zz need to fix ends acausally somehow   
# * * * * * * * * * * * * * * * * Drawing Routines  * * * * * * * * * * * * * * *
def autoscale( num): 
    if num==0:
        num=1
    num *= 1.1
    i=0
    if num<0:
        xunits = -1
        num = -num
    else:
        xunits =1
    while (num > 10) or (num<=.5) or (i>10): # calc xunits=xgrid values
        i += 1
        if num<=.5:                
            num *= 10
            xunits /= 10
        else:
            num /= 10
            xunits *= 10   
    if num > 5:
        num=10
    elif num>2.5:
        num=5
    elif num>2:
        num=2.5
    elif num>1:
        num=2
    else:
        num=1
    return num*xunits 
def ch_scaled( cname, cnum): # write prior scale
    global pp,chd, time_ch, Sagent_S_df
    set_world_scale( cnum)
    tlist = list(Sagent_S_df.iloc[:,cnum-1])
    tdiv=(top_scale[cnum-1]-bot_scale[cnum-1])/6
    tbot = bot_scale[cnum-1]
    y_scale( cname, tbot, tdiv, pp[chd], cnum) 
def ch_plot( cname, cnum):
    ch_scale(cname,cnum)
    ch_line(cname,cnum)
def top_min_pos(): # return absolute minimum index on top channel
    tlist = toplist( False)
    minval = tlist[0]
    j=0
    for i in range(1,len( tlist)):
        if minval > tlist[i]:
            j = i
            minval = tlist[i]
    return(j)
def top_max_pos(): # return absolute maximum index on top channel
    tlist = toplist( False)
    maxval = tlist[0]
    j=0
    for i in range(1,len( tlist)):
        if maxval < tlist[i]:
            j = i
            maxval = tlist[i]
    return(j)
def top_lmin_pos_left( pos): # return left local minimum index on top channel
    if pos==0:
        return(0)
    tlist = toplist( False)           # pos where start increasing again right
    minval = tlist[pos]
    j=pos       
    for i in range(pos-1,-1,-1):
        if minval >= tlist[i]:
            j = i
            minval = tlist[i]
        else: # the value increased so stop here at pos=i
            return(j)
    return(j)
def top_lmax_pos_left( pos): # return left local minimum index on top channel
    if pos==0:
        return(0)
    tlist = toplist( False)           # pos where start increasing again right
    maxval = tlist[pos]
    j=pos
    for i in range(pos-1,-1,-1):
        if maxval <= tlist[i]:
            j = i
            maxval = tlist[i]
        else: # the value decreased so stop here at pos=i
            return(j)
    return(j)
def top_lmin_pos_right( pos): # return right local minimum index on top channel
    tlist = toplist( False)           # pos where start increasing again right
    if pos==len( tlist)-1:
        return(pos)
    minval = tlist[pos]
    j=pos
    for i in range(pos+1,len( tlist)):
        if minval >= tlist[i]:
            j = i
            minval = tlist[i]
        else: # the value increased so stop here at pos=i
            return(j)
    return(j)
def top_lmax_pos_right( pos): # return right local minimum index on top channel
    tlist = toplist( False)           # pos where start increasing again right
    if pos==len( tlist)-1:
        return( pos)
    maxval = tlist[pos]
    j=pos
    for i in range( pos+1, len(tlist)):
        if maxval <= tlist[i]:
            j = i
            maxval = tlist[i]
        else: # the value decreased so stop here at pos=i
            return(j)
    return(j)
def top_above_pos_right( pos, value): # index for right until above value
    tlist = toplist( False)              # pos where start increasing again right
    if pos==len(tlist)-1:
        return(pos)
    for i in range(pos,len( tlist)):
        if tlist[i] > value:
            return(i)
    s_error(0x1000)
    return(pos)
def top_below_pos_right( pos, value): # index for right until below value
    tlist = toplist( False)              # pos where start increasing again right
    if pos==len(tlist)-1:
        return(pos)
    for i in range(pos,len( tlist)):
        if tlist[i] < value:
            return(i)
    s_error(0x2000)
    return(pos)
def top_above_pos_left( pos, value): # index for right until above value
    tlist = toplist( False)             # pos where start increasing again right
    if pos==0:
        return( pos)
    for i in range( pos,-1,-1):
        if tlist[i] > value:
            return(i)
    s_error(0x1000)
    return(pos)
def top_below_pos_left( pos, value): # index for right until below value
    tlist = toplist(False)             # pos where start increasing again right
    if pos==0:
        return(pos)
    for i in range(pos,-1,-1):
        if tlist[i] < value:
            return(i)
    s_error(0x2000)
    return(pos)
def top_min(): # return absolute minimum value on top channel
    tlist = toplist(False)
    return( min(tlist))
def top_max(): # return absolut minimum value on top channel
    tlist = toplist(False)
    return( max(tlist))
def ch_scale(cname,cnum): # calculate y scaling and write graph scale
    global pp,chd, time_ch, Sagent_S_df
    set_world_scale( cnum)
    tlist = list(Sagent_S_df.iloc[:,cnum-1])
    tmax=max(tlist)
    tmin=min(tlist)
    tdiv=autoscale((tmax-tmin)/5.5)
    tbot = round((tmin-tdiv)/tdiv)*tdiv
    if (tbot+tdiv)<= tmin:
        tbot += tdiv
    bot_scale[cnum-1]=tbot
    top_scale[cnum-1]=tbot+6*tdiv
    y_scale( cname, tbot, tdiv, pp[chd], cnum) 
def ch_line(cname,cnum):  # draw channel cnum on canvas
    global chd, Sagent_S_df, time_ch, WIDE 
    tlist = list(Sagent_S_df.iloc[:,cnum-1])
    set_world_scale( cnum)
    for i in range(0,len(tlist)-1):
        x1 = trans_x( time_ch[i] )
        x2 = trans_x( time_ch[i+1] )
        y1 = trans_y( tlist[i] )
        y2 = trans_y( tlist[i+1] )
        clip_line( canvas, x1,y1,x2,y2, ice.cmap[cnum%ncolor], WIDE)
def y_scale( cname, ybot, ygrid, loc, cnum):
    nmlen = len(cname)-int(len(cname)/4)
    xnloc = xpix[0] + loc*142 
    xshift = -5 
    lshift =0 
    fullname = str(cnum)+','+cname
    if loc==0:
            canvas.create_rectangle(0,ypix[0]-21,xpix[0]-1,app_wide,\
                    outline=ice.cmap[17],fill=ice.cmap[17])
            canvas.create_rectangle(0,ypix[0]-21,190,ypix[0]-8,\
                        outline=ice.cmap[17],fill=ice.cmap[17])
            xnloc -= 5
            lshift = 15
    elif loc==4:
            canvas.create_rectangle(app_wide-150,ypix[0]-25,app_wide-1,\
                        ypix[0]-5,outline=ice.cmap[17],fill=ice.cmap[17]) 
            canvas.create_rectangle(xpix[1]+1,ypix[0]-30,app_wide-1,\
                        ypix[1]+4,outline=ice.cmap[17],fill=ice.cmap[17]) 
            xshift= 40
            xnloc -= 22
            lshift =-int(nmlen*7/2)
    else:
        xshift = 8
        canvas.create_rectangle(xnloc-16,ypix[0]+1,xnloc+22,ypix[1],\
                                outline='white',fill='white') 
        canvas.create_rectangle(xnloc-70,ypix[0]-20,xnloc+70,ypix[0]-1,\
                                outline=ice.cmap[17],fill=ice.cmap[17]) 
        canvas.create_rectangle(xnloc-16,ypix[1]-1,xnloc+22,ypix[1]+4,\
                                outline=ice.cmap[17],fill=ice.cmap[17])
    x1 = xnloc+lshift+xshift-int(nmlen*7/2)-5
    y1 = ypix[0]-32
    canvas.create_rectangle(x1,y1,x1+50,y1+22,outline=ice.cmap[17],fill=ice.cmap[17]) 
    canvas.create_text(xnloc+lshift+xshift-int(nmlen*7/2),ypix[0]-20,anchor=W, \
            font='TkSmallCaptionFont 8 bold',text=fullname,fill=ice.cmap[cnum%ncolor])
    for i in range(0,7):
        ylab = ybot+ygrid*i
        yloc = ypix[1]-3-i*100  
        lname = str(ice.tidy(ylab,4))
        llen = len(lname)
        canvas.create_text(xnloc+2+xshift-int(llen*7/2),yloc,anchor=W,\
            font="TkSmallCaptionFont",text=lname,fill=ice.cmap[cnum%ncolor])
    canvas.pack()
def trans_p( tval): # translate time to point value
    global time_ch
    tidx=0
    tlast = time_ch[len(time_ch)-1]
    for i in range(1, len(time_ch)):
        if abs(time_ch[i]-time_ch[tidx]) > abs(time_ch[i]-tval):
            tidx = i  # find the closest time_ch value to tval
    if tval > tlast:
        tidx = len(time_ch)-1
    return( tidx)
def trans_x( xval): # translate world xval to xpixel 
    return int(xpix[0]+(xval-wo[0])/(wo[2]-wo[0])*(xpix[1]-xpix[0])+.5)
def trans_xpos( xtime): # determine alist index position given the time
    global samprate,Sagent_S_df
    nsamples = len(Sagent_S_df.index)
    pos = int(((xtime-wo[0])*samprate))
    if pos<0:
        pos=0
    if pos>= nsamples:
        pos=nsamples-1
    return( pos)
def trans_xw( xpixel): # translate xpixel to world time value
    return (wo[0] + (xpixel - xpix[0])/ (xpix[1]-xpix[0])*(wo[2]-wo[0]))
def trans_y( yval): # translate world yval to ypixel
    return int(ypix[1]-(yval-wo[1])/(wo[3]-wo[1])*(ypix[1]-ypix[0])+.5)  
def trans_yw( ypixel): # translate xpixel to world time value
    return (wo[3] - (ypixel - ypix[0])/ (ypix[1]-ypix[0])*(wo[3]-wo[1]))
def set_world_scale( cnum):
    wo[1]=bot_scale[cnum-1] # set bot world coord
    wo[3]=top_scale[cnum-1] # set top world coord
def clear_screen():
    canvas.create_rectangle(xpix[0],ypix[0]-2,xpix[1],ypix[1],\
                                    outline='black',fill='white') 
def tgrids( xbeg, xend):
    global xg,yg,xunits,tbeg,tend 
    wo[0] = xbeg
    wo[2] = xend
    tbeg = xbeg
    tend = xend
    xspace = ice.tidy(xend,4)-ice.tidy(xbeg,4)
    xunits = .1
    xsp = xspace
    while xsp > 2.5: # calc xunits=xgrid values
        xsp = ice.tidy(xsp/10, 4)
        xunits *= 10
    xfirst = int(xbeg/xunits)*xunits
    xpixels = xpix[1]-xpix[0]
    xdivisions = xspace/xunits
    if xdivisions==0:
        xdivisions=1
    xg = int(xpixels/xdivisions)  # xg is number of pixels per grid line
    yg = 100                     # y_pix is always 100 there are 6 yg grid lines
    tkpergr = 10
    xp = math.floor( xg/tkpergr)
    xg = xp * tkpergr
    ngrids = xspace/xunits
    extra = round(xunits * (xpixels-xg*ngrids)/xg, 4)
    wo[2] = xend + extra
    for iy in range(ypix[0]+100, ypix[1], 100): # horizontal grid tick marks
        for ix in range(0,xg,xp):             # ix = location of ticks
            for ig in range(xpix[0], xpix[1], xg):  # ig = location of grids
                if (ix+ig) < xpix[1]:
                    xpos =  ig+ix
                    canvas.create_line(xpos,iy-3,xpos,iy, width=1,fill=ice.cmap[16])
    canvas.create_rectangle(0,ypix[1]+1,app_wide,app_high,\
                                outline=ice.cmap[17],fill=ice.cmap[17]) 
    xnum = xfirst   
    # draw the verticle grid lines xg is increment in pixels
    for ix in range( xpix[0], xpix[1], xg):
        for iy in range(0,100,10):  # the 10 horizontal grids
            for ig in range( ypix[0], ypix[1], 100): # ig is verticle Y dimensions
                if (ix < xpix[1]) and (ix>xpix[0]):
                    canvas.create_line(ix-1,iy+ig-2,ix+2,iy+ig-2,width=1,fill=ice.cmap[16]) 
        mystr=str(round(xnum,3))
        xnum += xunits
        xnlen = len(mystr)            
        canvas.create_text(ix+2-int(xnlen*6/2),ypix[1]+10, \
                anchor=W,font="TkSmallCaptionFont",text=mystr)
    canvas.pack()
def get_coeff( filter_type, filt_type, sps, freq1, freq2):
    cutoff=freq1
    samp_freq = sps
    if  freq1>samp_freq/2. or freq1<=0. or freq2>samp_freq/2. or freq2< 0. :  
        coef = [1.0]
        return coef 
    freq1 = freq1 / samp_freq
    freq2 = freq2 / samp_freq    
    if filter_type==0:    #  brick-wall filter selected */
        n=MAXFILT 
    elif filter_type==1:# high quality sharp rolloff filter needs more coef's*/
        n=255 
    elif filter_type==2:  #  n size for medium filter types */
        n=127 
    else:  # ==3   default size for low quality filter type
        n=63
    coef = [0] * (n)
    if  sps >= 500:
        n = (n+1)*2 - 1  # double num coef. for high sample rates */
    if  n>MAXFILT:
        n=MAXFILT     
    m = (n + 1) / 2 
    q = 2 *  math.pi / float( n) 
    np1  = int(float( n * freq1 + 1.0)) 
    np2 = int(float( n * freq2 + 1.0)) 
    a =   [0] * int(m+1)
    lwin = [0] * int(n+1)
    if filt_type == 'h' or filt_type == 'l':  # ** set freq response ***/
        if filt_type == 'h':
            low  = 0.0
            high = 1.0
        else: # 'l'
            low  = 1.0
            high = 0.0
        for i in range(1,int(np1+1)):
            a[i] = low
        for i in range(int(np1+1),int(m+1)):
            a[i] = high   
    if filter_type==0:    # high quality sharp rolloff filter */
        ninc = float(sps)/12.5 
    elif filter_type==1:  # high quality sharp rolloff filter */
        ninc = float(sps)/50. 
    elif filter_type==2:  # default medium quality, low noise filter */
        ninc = float(sps)/200. 
    else:
        ninc = float(sps)/400. # slow type=3 very long rolloff */    
    if  filt_type=='h':
        nstart=-1. 
    else:  # lowpass */
        ninc= -ninc 
        nstart=1. 
    nval=nstart   # shape the roll off based on the ninc value */
    for i in range( 1, int(m+1)):      # ** Calculate coef array **
        xt = a[1] / 2.0 
        for j in range(2 , int(m+1)):
            xt += a[j] * math.cos(q * float(((m - i) * (j -1)))) 
        coef[i-1] = 2.0 * xt / float( n )
    for i in range(0  ,n ):
        lwin[i]=1.0         # no-window */ 
    for i in range(int( m+1), int( n+1)): # copy 1st n/2 coef to last n/2 coef
        coef[i-1] = coef[int(2*m)-i-1] 
    lwin = lippert( n, 1.0, .08 )    
    total=0
    for i in range( 0  , int(n) ):
        coef[i] *= lwin[i] 
        total += coef[i]     
    if  filt_type == 'l':         # normalize lowpass coef only */
        for i in range( 0  ,n ):
            coef[i] *= 1./total   # normalize so coefs sum to 1.0 */  
    return coef
def ReDraw():  # redraw the plot screen
    global chd, topname,tbeg,tend
    canvas.create_rectangle(xpix[0],ypix[0]-2,xpix[1],ypix[1],outline='black',\
                            fill='white')
    canvas.create_rectangle(0,ypix[0]-21,xpix[0]-1,app_wide,\
                        outline=ice.cmap[17],fill=ice.cmap[17])
    canvas.create_rectangle(xpix[0],ypix[0]-26,xpix[1]-1,ypix[0]-1,\
                        outline=ice.cmap[17],fill=ice.cmap[17])
    canvas.create_rectangle(0,ypix[0]-26,app_wide-1,ypix[0]-5,\
                            outline=ice.cmap[17],fill=ice.cmap[17]) 
    canvas.create_rectangle(xpix[1]+1,ypix[0]-30,app_wide-1,\
                        ypix[1]+4,outline=ice.cmap[17],fill=ice.cmap[17]) 
    tgrids(tbeg,tend)
    ilen=len(cnums_disp)
    itop=0
    chd=0
    for i in range(0,ilen):
        if cnums_disp[i]==topname:
            itop=i
        else:
            chlist = cnums_disp[i].split(',')
            idx=int(chlist[0])
            chan_name=chlist[1]
            ch_scaled( chan_name, idx)
            chd += 1
    if ilen>0: # draw top scale
        chlist = cnums_disp[itop].split(',')
        top=int(chlist[0])
        chan_name=chlist[1]
        ch_scaled( chan_name, top)
        chd += 1
    chd=0
    for i in range(0,ilen):
        if cnums_disp[i]==topname:
            itop=i
        else:
            chlist = cnums_disp[i].split(',')
            idx=int(chlist[0])
            chan_name=chlist[1]
            ch_line( chan_name, idx)
            chd += 1
    if ilen>0: # draw top line
        chlist = cnums_disp[itop].split(',')
        top=int(chlist[0])
        chan_name=chlist[1]
        ch_line( chan_name, top)
        chd += 1
    clear_status()
    display_markers()
    display_text()
def factor_top( timex):
    xfactor = float( timex)
    samples = len(Sagent_S_df.index)
    for tidx in range( 0, samples):
        val = int((Sagent_S_df.iloc[tidx, top-1]+xfactor/2)/xfactor)
        Sagent_S_df.iloc[tidx, top-1]= float(val)*xfactor             
    ReDraw() 
def display_text(): # display screen_text on screen, if any
    global markers,NOM
    for i in range(0, len(screen_text)):
        txt=screen_text[i].split(';')
        canvas.create_text( 55+int(txt[1])*14, 130+int(txt[2])*18, anchor=W,\
                    font=('Courier',14,'bold'),text=txt[0], fill='black')
def display_markers():
    global markers,NOM
    for i in range(0, len(markers)):
        if markers[i] != NOM:
            locx = trans_x( markers[i]+1)
            canvas.create_line( locx, ypix[0]+20, locx, ypix[1], dash=(5,5),\
                                width=1, fill='red')
            if i>9:
                shft = 9
            else:
                shft = 4
            if i<5:
                mtext = chr(65+i)
            else:
                mtext = str(i)
            canvas.create_rectangle(locx-shft-3,ypix[0]-2,locx+shft+3,ypix[0]+16,\
                                outline='red',fill='white') 
            canvas.create_text( locx-shft, ypix[0]+8, anchor=W,\
                    font="TkSmallCaptionFont",text=mtext, fill='red')
def delete_top():
    global DispMenu,topname,cnums_disp,top
    if len(cnums_disp)>0:
        ch_plot('',top) # unplot data
        cnums_disp.remove(topname)
    DispMenu.pack_forget()
    DispMenu.destroy()
    if len(cnums_disp)==0:   # remove words above optionmenu
        canvas.create_rectangle(232,2,445,20,outline=ice.cmap[17],fill=ice.cmap[17])
        top=NOTOP
    else:
        var4 = StringVar(canvas)            
        var4.set(cnums_disp[0]) # default value 
        topname=cnums_disp[0] 
        chlist = topname.split(',')
        top=int(chlist[0])
        chan_name=chlist[1]
        DispMenu = OptionMenu(canvas, var4, *cnums_disp,\
                    command=chan_display) 
        DispMenu.config(font=('TkSmallCaptionFont',(7)),width=24) 
        DispMenu.pack(side=TOP)     
        DispMenu.place( x=305,y=22)      
    canvas.pack()
    ReDraw()
def load_chans( chanlist):
    variable = StringVar(root)
    variable.set(chanlist[0]) # default value 
    txt = 'The Loaded Channels:'
    canvas.create_rectangle(80,2,249,20,outline=ice.cmap[17],fill=ice.cmap[17])     
    canvas.create_text(120, 10, anchor=W, font="TkSmallCaptionFont",text=txt)
    w = OptionMenu(root, variable, *chanlist, command=chan_select) 
    w.config(font=('TkSmallCaptionFont',(7)),width=24,)     
    w.pack(side=TOP)
    w.place( x=75,y=22)
def load_CSV():
    global chans, units, loaded, df_is_str
    global fname,fpart, Sagent_S_df,tbeg,tend,samprate, time_ch
    fname=askopenfilename(filetypes=(("CSV files", "*.csv"),\
                    ("All files", "*.*")))
    if len(fname)!= 0:
        fpart = ntpath.basename( fname )
        process_S('open_CSV',fname, True)
    else:
        message('No file loaded due to Cancel')
def chan_display(chsel): # select another channel as top focus channel
    global chan_name, topname,top
    topname=chsel
    chlist = chsel.split(',')
    top=int(chlist[0])
    chan_name=chlist[1]
    set_world_scale( top)
def set_clipping( xmin, ymin, xmax, ymax):
    global x_max, y_max, x_min, y_min
    x_max = xmax
    y_max = ymax
    x_min = xmin
    y_min = ymin
def getlist( name ): # get list of named channel w/ marker A to E interval option
    idx = list(Sagent_S_df.columns).index(name)
    if markers[0] == NOM:
        beg_idx = 0
    else:
        beg_idx = int(trans_xpos( markers[0]))
    if markers[4] == NOM:
        end_idx = len(Sagent_S_df.index)-1
    else:
        end_idx = int(trans_xpos( markers[4]))            
    return (Sagent_S_df.iloc[beg_idx:end_idx, idx].tolist())  
def close_it():
   root.destroy()
# - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
# - - - - - - - - - - - - - The Class Object  - - - - - - - - - - - - - - - - - -
# - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
class Sagent_S(Frame): 
    def __init__(self, parent):
        global hent,bot_scale,top_scale,ch
        Frame.__init__(self, parent)            
        self.parent = parent        
        self.initUI()
        self.master = parent
        self.init_menu()       
        self.canbut=Button(self, text="Reset",command=self.tcancel,width=6)
        self.canbut.pack( side=LEFT)
        self.canbut.place( x=app_wide-75, y=18)        
        hent=self.hentry=Entry(self,width=81,font="TkSmallCaptionFont") 
        self.hentry.pack( side=BOTTOM)
        self.hentry.place( x=545,y=25)
        self.hentry.bind('<Return>', self.SA_Entry)
        for i in range(0,300):
            bot_scale.append(0)
            top_scale.append(60)
            ch.append(0) 
    def init_menu(self):
        self.pack(fill=BOTH, expand=1)
        menu = Menu(self.master)
        self.master.config(menu=menu)
        filemenu = Menu(menu, tearoff=False)
        filemenu.add_command(label="Open..", command=load_CSV)
        filemenu.add_command(label="Save...", command=save_file)
        filemenu.add_separator()
        filemenu.add_command(label="Exit", command=close_it)
        menu.add_cascade(label="File", menu=filemenu)
        editmenu = Menu(menu, tearoff=False)
        editmenu.add_command(label="restore top (^z)", command=_restore_top)
        menu.add_cascade(label="Edit", menu=editmenu)
        viewmenu = Menu(menu, tearoff=False)
        viewmenu.add_command(label="autoscale top (a)", command=_autoscale)
        menu.add_cascade(label="View", menu=viewmenu)
        runmenu = Menu(menu, tearoff=False)
        runmenu.add_command(label="run a macro ...", command=run_macro)
        runmenu.add_command(label="run python script ...",command=_run_python)
        menu.add_cascade(label="Run", menu=runmenu)
        helpmenu = Menu(menu, tearoff=False)
        helpmenu.add_command(label="display commands (f1)", command=_commands_help)
        helpmenu.add_command(label="marker commands  (f2)",command=_marker_help)
        menu.add_cascade(label="Help", menu=helpmenu)
    def tcancel( self):
        clear_status()
        self.hentry.delete(0,99)
        ReDraw()
    def initUI(self):
        global canvas, stats
        self.parent.title('Sagent_S '+str(Sagent_S_version)+\
                    ' - - - Python Serial Analysis Agent  (Iceberg AGI)')
        self.pack(fill=BOTH, expand=1)
        canvas = Canvas(self, offset='0,50')
        rect= canvas.create_rectangle(xpix[0],ypix[0],xpix[1],ypix[1],outline="black",\
                                                fill="white")         
        canvas.pack(fill=BOTH, expand=1)          
        canvas.focus_force()               
        frame = Frame(canvas, width=100, height=100)
        canvas.bind("<Button-1>", mouse1) 
        canvas.bind("<Button-2>", mouse2) 
        canvas.bind("<Button-3>", mouse3)
        canvas.bind("<MouseWheel>", MouseWheel) 
        frame.bind_all('<Key>', keyup)           
    def nlist( n): # make a list from channel n channel
        alist=[]
        for tidx in range(0,len(Sagent_S_df.index)):
            alist.append(Sagent_S_df.iloc[tidx,n-1])
        return (alist)
    def chan_number( name): # get channel number of a name
        chans = list(Sagent_S_df.columns)
        for i in range(0,len(chans)):
            if chans[i]==name:
                return i+1
        return(0)
    def list_named( name): # make a list from channel name
        num = chan_number(name)
        return( nlist(num))

    def shift1(a,sh):
        sz=len(a)
        if sh > 0:
            last = a[sz-1]
            a=a[1:sz]
            a.append(last)
            return (a)
        else:
            first=[a[0]]
            first.extend(a[0:sz-1])
            return (first)    
    def shift_time( timex):
        xsamples = int(round(samprate * float(timex)))
        period = abs(xsamples)
        if abs(xsamples)<1:
            message('Time period was too short to shift data')
            return(False)
        alist=toplist()
        alen = len(alist)
        if xsamples > alen:
            xsamples = alen
        elif xsamples < (0-alen):
            xsamples = 0 - alen
        if xsamples>0:
            for tidx in range( 0, xsamples): # duplicate 1st value
                Sagent_S_df.iloc[tidx, top-1]= alist[0]        
            for tidx in range( xsamples, alen):
                Sagent_S_df.iloc[tidx, top-1]= alist[tidx - xsamples] 
        elif xsamples<0:       
            for tidx in range( 0, alen+xsamples):
                Sagent_S_df.iloc[tidx, top-1]= alist[tidx - xsamples] 
            for tidx in range( alen+xsamples, alen-1): # duplicate last value
                Sagent_S_df.iloc[tidx, top-1]= alist[alen-1]
        return(True)
    def reg_fit( x_names, y_name):
        global reg_model, Sagent_S_df            
        XX = Sagent_S_df[x_names].astype(float) 
        YY = Sagent_S_df[y_name].astype(float)
        reg_model = linear_model.LinearRegression()
        reg_model.fit(XX, YY)
        tex='Intercept:'+str(reg_model.intercept_)+' Coefficients:'+str(reg_model.coef_)
        message(tex)
        alist=[] # build list of predicted values
        for i in range(0,len(alist())):
            xvals=[]
            for j in range(0, len(x_names)):
                num = Sagent_S.chan_number( x_names[j])
                xvals.append(Sagent_S_df.iloc[i, num-1] )
            alist.append( reg_model.predict(xvals))
            
        New_Interest_Rate=2.0 # zz test code |--- save model, generalize with vars modeling
        New_Unemployment_Rate=5.6
        Prediction_result  = ('Predicted Stock Index Price: ', \
                    reg_model.predict([[New_Interest_Rate ,New_Unemployment_Rate]]))
        print(Prediction_result)                    
    def get_model( x1, y1, order):
        global mymodel, model_type
        mymodel = np.polyfit( x1, y1, order)
        model_type = 'polynomial'
        first=mymodel[order]
        for ord in range(0,order):
            first += mymodel[ord] * x1[0]**(order-ord)
        yprime=[first] 
        for i in range(1,len(x1)):
            val=mymodel[order]
            for ord in range(0,order):
                val += mymodel[ord] * x1[i] **(order-ord)
            yprime.append( val ) 
        # get R statistic
        rcoff = np.corrcoef(y1,yprime)
        rstat = round(rcoff[1,0],4)
        return(yprime, rstat, mymodel)

    def SA_Entry( self, text_event):
        global SAGcommand,tend,tbeg,top,Sagent_S_df, tidx, xchan, samprate,topname
        global mymodel,order, model_type, ychan, indeps, depend,xsave, ysave
        global knumber, filter_level
        text =  self.hentry.get() 
        self.hentry.delete(0,99)
        clear_status()
        if SAGcommand == '': # unsolicited assumes question mode
            result = ice.get_help(text)
            print_Sagent_help(  result )
            message('') 
        else:
            process_S( SAGcommand, text, True )  # Process the event
# * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
# * * * * * * * * * * * * * * * Keyboard Events * * * * * * * * * * * * * * * * *
def keyup(event):
    global topname,top,Sagent_S_df,num_inserts,xg,yg,xunits
    global units,df_is_str,xsave,ysave
    foc = root.focus_get().__class__
    hetype = type(hent)
    if foc==hetype:  # handle no key events if Entry is happening
        return 
    if event.char == event.keysym:
        ev_type = 'char_'+event.char
        if event.char=='0':
            text_command('Channel number or case arbitrary name :','show_chan')
        elif event.char=='a':
            process_command('autoscale')
        elif event.char=='b':              # set bottom grid to a value  
             process_command('grid_bot')
        elif event.char=='c':      
             process_command('correlate') 
        elif event.char=='d':  # derivative of top channel
            process_command('derivative')
            process_command('autoscale')
        elif event.char=='e':
            [xx,yy] = pyautogui.position() # get mouse position
            xsave = trans_xw( xx-9 )      # zz why is click different position()?
            ysave = trans_yw( yy-38 )
            text_command('2nd_pointer_click_return','edit_top')
        elif event.char=='f':      
             process_command('filter')
        elif event.char=='g':
            process_command('grid_space')
        elif event.char=='h':      
             process_command('highpass') 
        elif event.char=='i': # integrate top channel
            process_command('integrate')
            process_command('autoscale') 
        elif event.char=='j':
            alist=toplist(True)
            alen = len(alist)
            alist = rms(alist)
            for tidx in range(0,alen):
                Sagent_S_df.iloc[tidx,top-1] = alist[tidx]
            ReDraw()  
        elif event.char=='k':
             process_command('kval')
        elif event.char>='1' and event.char<='9': # load channel 1-9
            if (int(event.char))<= len(chans):
                chan_select( chans[int(event.char)-1])
                txt = 'Channel '+str(int(event.char))+' is now the top channel.'
                message(txt)
            else:
                message('That channel number does not exist')
        elif event.char=='m':      
             process_command('model')
        elif event.char=='n': # rename top channel
             process_command('rename')      
        elif event.char=='o':   # overvein shows all the data time wise 
            process_command('overview')
        elif event.char=='p':
             process_command('snapshot')
        elif event.char=='q':
             process_command('median')
        elif event.char=='r':
             process_command('relate')
        elif event.char=='s':
             process_command('scale_top')
        elif event.char=='t': #-----------------------Set a new sample Rate
             process_command('set_samprate')
        elif event.char=='w': #---------------------------write the macro
            save_macro()
        elif event.char=='x':
             process_command('shift_top')
        elif event.char=='z':  #---------------------zero grids of top channel
            idiv = (top_scale[top-1]-bot_scale[top-1])/6 #keep same divisions
            top_scale[top-1] = 6*idiv
            bot_scale[top-1]=0
            ReDraw()  
        elif event.char=='y':  #--------------------resample filter 111
            alin = toplist(True)
            message('Processing Average Filter (111)')                
            Sagent_S_df.iloc[0,top-1]=(alin[0]*2+alin[1])/3.0
            for idx in range(1, len(alin)-1):
                Sagent_S_df.iloc[idx,top-1]=(alin[idx-1]+alin[idx]+alin[idx+1])/3.0
            Sagent_S_df.iloc[len(alin)-1,top-1]= (alin[len(alin)-1]*2+alin[len(alin)-2])/3.0                
            ReDraw() 
        elif event.char=='u':   
            samples = len(Sagent_S_df.index)
            counts=[]
            last=Sagent_S_df.iloc[0,top-1]
            cnt=1
            for i in range(1,samples-1):
                if Sagent_S_df.iloc[i,top-1] != last:
                    counts.append(cnt)
                    last=Sagent_S_df.iloc[i,top-1] # new value
                    cnt=1
                else: # they are the same
                    cnt += 1
            min_cnt=counts[1]
            if len(counts)>3: # is it big enough?
                for i in range(2,len(counts)):
                    if counts[i]<min_cnt:
                        min_cnt=counts[i]
                num_cnts=0
                for i in range(0,len(counts)):
                    if counts[i]==min_cnt:
                        num_cnts += 1
                if num_cnts<2:
                    min_cnt=1
            else: # indeterminite due to small size
                    min_cnt=1 
            resamp_start=counts[0]
            while resamp_start-min_cnt>=0:
                resamp_start -= min_cnt
            factorable=True
            for i in range(1,len(counts)-1):
                if (counts[i]%min_cnt)!=0:
                    factorable=False
            if not factorable:
                min_cnt=1
            resamp_end=int((samples-min_cnt)/min_cnt)*min_cnt
            if min_cnt>1:
                for i in range(resamp_start, resamp_end, min_cnt):
                    for j in range(1,min_cnt):
                        b= j* Sagent_S_df.iloc[i+min_cnt,top-1]
                        a= (min_cnt-j)*Sagent_S_df.iloc[i,top-1]
                        Sagent_S_df.iloc[i+j,top-1]= (a+b)/min_cnt
                ReDraw() 
                message('start='+str(resamp_start)+' min_cnt='+str(min_cnt))
            else:
                message('This channel cannot be up-sampled')
    elif len(event.char) == 1:            
        ev_type = 'char_'+event.keysym
        if event.keysym=='Escape':
            clear_status()
            Sagent_app.hentry.delete(0,99)
            ReDraw()
        elif event.char=='1': # ctl 1 zoom x dimension
            print('zoom ctl 1')              
        elif event.char==' ':  #------ask a question about Sagent commands
             process_command('question') 
        elif event.char=='=':
             process_command('equation')
        elif event.char=='?':
            samples = len(Sagent_S_df.index)
            max=Sagent_S_df.iloc[0,top-1]
            min=Sagent_S_df.iloc[0,top-1]
            sdev = round(statistics.stdev(Sagent_S_df.iloc[:,top-1]),4)
            mean = round(statistics.mean(Sagent_S_df.iloc[:,top-1]),4)
            for i in range(0,samples-1):
                if max<Sagent_S_df.iloc[i,top-1]:
                    max = round(Sagent_S_df.iloc[i,top-1], 4)
                if min>Sagent_S_df.iloc[i,top-1]:
                    min = round(Sagent_S_df.iloc[i,top-1], 4) 
            message('max='+str(max)+'   min='+str(min)+\
                        '   mean='+str(mean)+'   sdev='+str(sdev))
            root.focus_set()
        elif event.keysym=='f':  # ctlf - change filter rolloff
             process_command('rolloff')
        elif event.keysym=='j':  # CTLj - save data as Json File
            Sagent_S_df.to_json(r'test_df.json', lines=True,orient='records')
        elif event.keysym=='n': # ctln notch filter
             process_command('notch')
        elif event.keysym=='s': # ctls sort dataframe
             process_command('sort')
    else: # special keys here
        if event.keysym=='Delete':
            process_command( 'Delete' )
        elif event.keysym=='Up':
            process_command( 'Up')
        elif event.keysym=='Down':
            process_command( 'Down') 
        elif event.keysym=='Right':
            process_command( 'Right') 
        elif event.keysym=='Left':
            print('Left key')
        elif event.keysym=='Insert':
            process_command( 'insert')
        elif event.keysym=='F1':
            print_Sagent_help(  ice.Sagent_help1 )
        elif event.keysym=='F2':
            print_Sagent_help(  ice.Sagent_help2 )
        elif event.keysym=='F4':  
            process_command( 'to_influxdb')  # save DF to InfluxDB
        elif event.keysym=='F3':  
            display_ice()
        elif event.keysym=='Shift_R' or event.keysym=='Shift_L':
            nothing=0 # do nothing
        else:
            if event.keysym!='Control_L':
                print('Unprocessed special key=',event.keysym)
# * * * * * * * * * * * * * * * Alt Key Events  * * * * * * * * * * * * * * * * *
def altkey(event):
    global Sagent_S_df,tbeg,tend,time_ch,samprate, markers, NOM,loaded,xx, yy
    global topname
    ev_type = 'alt_'+event.char
    if event.char=='a':     # alta - set the A marker to current mouse x pos
        [xx,yy] = pyautogui.position() # MARKER A means begining position
        val = str(ice.tidy( trans_xw( xx-8 ), 5 ))
        process_S( 'mark_time', '0'+','+val, True)
    elif event.char=='b':       # set the B marker to current mouse x position
        [xx,yy] = pyautogui.position() # get mouse position
        val = str(ice.tidy( trans_xw( xx-8 ), 5 ))
        process_S( 'mark_time', '1'+','+val, True)  
    elif event.char=='c':       # set the C marker to current mouse x position
        [xx,yy] = pyautogui.position() # get mouse position
        val = str(ice.tidy( trans_xw( xx-8 ), 5 ))
        process_S( 'mark_time', '2'+','+val, True)
    elif event.char=='d':       # set the D marker to current mouse x position
        [xx,yy] = pyautogui.position() # get mouse position
        val = str(ice.tidy( trans_xw( xx-8 ), 5 ))
        process_S( 'mark_time', '3'+','+val, True) 
    elif event.char=='e':       # set the E marker to current mouse x position
        [xx,yy] = pyautogui.position() # MARKER E means ending position
        val = str(ice.tidy( trans_xw( xx-8 ), 5 ))
        process_S( 'mark_time', '4'+','+val, True)
    elif event.char=='f':       # Alt F ------ Frequency Magnitude Spectrum
        alist=toplist(False)
        plt.magnitude_spectrum( alist,samprate) 
        plt.title('Frequency Magnitude Spectrum of '+topname)           
        plt.show()
    elif event.char=='g':  # Altg ------- get marker values to the ice
         process_command('ice_dual_marker')
    elif event.char=='h':
        alist=toplist(False)
        plt.hist( alist, density=True, bins=30)  # plot histogram
        plt.ylabel('Probability')
        plt.xlabel('data')
        plt.title('Histogram of'+topname)
        plt.show()
    elif event.char=='i': # AltI regression
         process_command('regress')
    elif event.char=='j': # altJ -  Insert data to ice.json
         process_command('ice_insert')
    elif event.char=='k':
        print('altk')
    elif event.char=='l':
         process_command('factor') 
    elif event.char=='m': # --- altm - marker commands
         process_command('marker')
    elif event.char=='n':   #---- open a file from ice.ice['filename']
        process_S('open_CSV','`filename`', True)
    elif event.char=='o':            
        if loaded:
            samples = len(Sagent_S_df.index) 
            tbeg=time_ch[0]
            tend=samples/samprate
            ReDraw()   
    elif event.char=='p':
         process_command('run_python')
    elif event.char=='q': # altq - query values at marker A
        print('altq')
    elif event.char=='r': 
        process_command('ice_marker')  
    elif event.char=='s': # alts  =  silence (turn off) markers
        process_command('markers_off')
        ReDraw()  
    elif event.char=='t': # scale time
         process_command('scale_time')          
    elif event.char=='u':  # unused
        print('altu')
    elif event.char=='v':
        print('altv')
    elif event.char=='w': # write text/ice to screen pos (permanent like markers)
        process_command('plot_text')
    elif event.char=='x': # altx end program
        root.destroy()
    elif event.char=='y': 
        print('alty') 
    elif event.char=='z': 
        print('altz') 
# * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
# * * * * * * * * * * * * * * * Mouse Events  * * * * * * * * * * * * * * * * *
def mouse1(event): # left button display values at pointer
    process_S('mouse1',str(event.x)+','+str(event.y), True)
def mouse2(event): # scroll button Zoom Activate event
    process_S('mouse2',str(event.x)+','+str(event.y), True)         
def mouse3(event): # right button
    process_S( 'mouse3',str(event.x)+','+str(event.y), True)
def MouseWheel(event): # scoll wheel event
    process_S( 'wheel',str(event.x)+','+str(event.y)+','+str(event.delta), True)
def _restore_top():
    process_command('restore_top')
    process_command('autoscale') 
def _autoscale():
    process_command('autoscale') 
def _run_python():
    process_command('run_python')
def _commands_help():
    print_Sagent_help(  ice.Sagent_help1 )
def _marker_help():
    print_Sagent_help(  ice.Sagent_help2 )

# * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
# * * * * * * * * * * * * * * * Control Events  * * * * * * * * * * * * * * * * *
def ctrkey(event):
    global topname,top,Sagent_S_df,num_inserts,xg,yg,xunits
    global units,df_is_str,xsave,ysave
    if event.keysym=='z':     # ctrz - restore last Top channel
        process_command('restore_top') 
        process_command('autoscale')
    elif event.keysym=='e':   # ctre - email an ice value with message    
        print('Control=',event.keysym)        
    elif event.keysym=='b':   # ctrb -     
        print('Control=',event.keysym)
    elif event.keysym=='t':   # ctrt -  set a marker to a time 
         process_command('mark_time')
    else:   # unprocessed control keys 
        print('unprocessed control key=',event.keysym)
#******************************************************************************
def main():
    global root, Sagent_app, config, args, process_name
    args = sys.argv[1:]
    root = Tk()
    root.iconbitmap(r'C:\Users\rslip\Desktop\Sagent\S.ico') 
    ice.turn_off_numlock()  # make sure numlock is OFF
    #root.geometry(str(app_wide-10)+'x'+str(app_high-10)+'+0+0')
    root.geometry(str(app_wide-10)+'x'+str(app_high+15)+'+0+0')
    root.resizable(width=False, height=False)
    root.configure(background = 'white')
    set_clipping( xpix[0], ypix[0], xpix[1], ypix[1] )
    for alt in ice.altkeys:
        root.bind( alt, altkey) 
    for ctrl in ice.ctrkeys:
        root.bind( ctrl, ctrkey)
    root.focus_set()
    ice.load_ice() # get iceberg ice dictionary becomes ice.ice
    Sagent_app = Sagent_S(root)
    # Check for args patterns
    #   python3 Sagent_S.py -r json.py
    if len(args) == 2 and args[0] == '-r':
        root.after(500, run_process) # run and exit the process
        process_name = args[1]
    root.mainloop()  
if __name__ == '__main__':
    main()  