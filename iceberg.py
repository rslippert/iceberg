# ----- Iceberg General support routines for Sagent Agents -------
import ctypes
import csv, sys
import math
import numpy as np
import pandas as pd
import json
import warnings
import smtplib
from yahoo_fin import stock_info as si

Separator = ';'  # Separator &  sed for referencing information in text streams
warnings.simplefilter(action='ignore', category=FutureWarning)

Sagent_help1='\n\n\t\t\t\t\t\t---  Sagent_S COMMAND  SUMMARY  ---\n'+\
'1 thru 9\tDisplay channel by number\t\t\t0<num. or name>\tDisplay channel by num. or name\t'+\
'ESCAPE\tredraws the screen or cancels a command\na\tAuto-scale the current channel\t\t'+\
'b\tSet bottom grid of Top chan\t\t\tc\tCalculate timeshift between 2 channels\t\t\n'+\
'd\tDo Derivative of current channel\t\te\tEdit current channel data\t\t\t'+\
'f\tFilter (lowpass) the current channel\t\t\n'+\
'g\tSet scale between Top Channel Grids\t\th\tHighpass filter Top channel\t\t\t'+\
'i\tIntegrate Top channel (zero first point)\nj\tRMS of Top Channel'+\
'\t\t\tk\tChanges a K (constant) value\t\t\tl\tFit top chan to a polynomial model\n'+\
'm\tModel Top chan via equation,eg. ch[5]*ch[7]+5\tn\treName top channel\t\t\t'+\
'o\tOverview (show all data)\np\tTake a Snapshot of Screen\t\t\t'+\
'q\tMedian Filter Top channel\t\t\tr\tRelate 2 channels and model\n'+\
's\tAdjust the Scaling of Top channel\t\tt\tSet sample rate (time base) samps/sec\t\t'+\
'u\tUn-spikes top channel with median filter\n'+\
'v\tConVert top to Frequency domain (FFT)\tw\tWrite the current macro...\t\t\t'+\
'x\tShift the current channel by a time\ny\tAverge Filter 111\t\t\t\t'+\
'z\tZero bottom grid of Top channel\t\t?\tDisplay Statistics for the Top channel\n'+\
'F1\tProvide Help (this help screen)\t\tF2\tDisplay Marker Commands Help\t\t'+\
'F3\tShow all Iceberg ice.json Data\n'+\
'F4\tShow all the Variables created\t\tF5\tFit top channel to Step Response\t\t'+\
'F6\tCubic Spline Top channel between markers\nF7\tConvert Top to Zero Crossing Freq. Count\t'+\
'SPACE\tAsk Sagent about how to perform Analysis\t=\tPerform a calculation\n'+\
'ALT A\tSet the A marker\t\tALT B\tSet the B marker\t\t'+\
'ALT C\tSet the C marker\t\tALT D\tSet the D marker\n'+\
'ALT E\tSet the E marker\t\tALT F\tFrequency Magnatude plot\t'+\
'ALT G\tGet Marker val to ice\tALT H\tHistogram the current channel\n'+\
'ALT I\tMultiple chan Model\tALT J\tInsert an ICE value\t\t'+\
'ALT K\tConvert top to RMS\tALT L\tFactor Top to Discrete Levels\n'+\
'ALT M\tMarker Commands\t\tALT N\tOpen iced filename\t'+\
'ALT O\tDisplays overview\t\tALT P\tRun a Python Script\n'+\
'ALT Q\tQuery value of marker A\tALT R\tRead a Marker to Ice\t'+\
'ALT S\tSilence Markers\t\tALT T\tChange time Scaling\n'+\
'ALT U\t------ Unused ------\tALT V\tAdd an iced Variable\t'+\
'ALT W\tWrite text on screen\tALT X\tExit this program\n'+\
'ALT Y\tDual Marker to Ice\t\t'+\
'ALT Z\tAdd a named variable\nCTL A\t------ Unused ------\t'+\
'CTL B\t------ Unused ------\tCTL C\tAbort this command  \t'+\
'CTL D\t------ Unused ------\nCTL E\t------ Unused ------\t'+\
'CTL F\t------ Unused ------\tCTL G\t------ Unused ------\t'+\
'CTL H\t------ Unused ------\nCTR I\t------ Unused ------\t'+\
'CTL J\t------ Unused ------\tCTL K\t------ Unused ------\t'+\
'CTL L\t------ Unused ------\nCTL M\t------ Unused ------\t'+\
'CTL N\t------ Unused ------\tCTL O\t------ Unused ------\t'+\
'CTL P\t------ Unused ------\nCTL Q\t------ Unused ------\t'+\
'CTL R\t------ Unused ------\tCTL S\t------ Unused ------\t'+\
'CTL T\tSet a marker to a time\nCTL U\t------ Unused ------\t'+\
'CTL V\t------ Unused ------\tCTL W\t------ Unused ------\t'+\
'CTL X\t------ Unused ------\nCTL Y\t------ Unused ------\t'+\
'CTL Z\tRestore last Top channel\t'+\
'INSERT\tInsert new blank channel\tDELETE\tDelete (undisplay) Top\n'+\
'L BuTN\tDisplays top values\t\tR BuTN\t---unused---\n'

help_quest = { 'zoom':'\tThe best way to Zoom, is to Scroll with the wheel,'+\
                ' then press the Scroll wheel\n\n\tYou can also zoom  [time]  with the [s] '+\
    'command\n\n\tor scale the distance between grids with the [g] (grid scaling) command\n\n'+
    '\tand the [a] (autoscale) command will rescale the top channel to a default',\
    'filter':'\tThe [f] command will filter the Top channel based on a frequency\n'+\
    '\tSince [frequency] is dependent on [sample rate] (note: the [t] command sets that)\n'+
    '\tyou can try filtering at 1/10 the [sample rate] and take it from there\n\n'+\
    '\tThe [h] command highpass filters the Top channel, which removes the lower frequencies\n\n'+\
    '\tYou can also remove spikes in the data with the [u] (unspike) command\n\n'+\
    '\tNote:\tIf the A marker is set, only data after the A marker is filtered\n'+\
    '\t\tAlso if the E marker is set, only data before the E marker is filtered',\
    'scale':'\tThe [s] command allows rescaling both time and the Top channel scale\n\n'+\
    '\t\tType also zoom for more information on scaling commands',\
    'chirp':'\tThe [m] modeling command can generate a chirp\n\n'+\
    '\t\tUse the formula:   math.cos(x**2.2)\n\n'+\
    '\t\tThe frequency is the (derivative of x**2.2) / (2*3.141593)'\
    }

def get_help( text):
    if text in help_quest:
        return( 'Help for '+text+'\n\n'+help_quest[text])
    else:
        return('Sorry, no help found for '+text)

Sagent_help2='\t\tALTM   Marker Commands\t\t\t\t\tOther Marker Commands\n\n'+\
'<marker>,use\t\t--- Sets in use marker to that marker number\n'+\
'<marker>,off\t\t--- Turns off that marker number\t\t\t'+\
'altg - <icename>,<marker1>,<marker2>,<opr> - - - Ice from dual markers\n'+\
'<marker>,min\t\t--- Move Marker to the minimum value of top channel\t\t'+\
'\t\taverage - - - Ice the average between 2 markers\n'+\
'<marker>,max\t\t--- Move Marker to the maximum value of top channel\t\t'+\
'\tOPR:\ttime - - - - -  Ice the time between 2 markers\n'+\
'<marker>,put,index,<pos>\t--- Put marker at an index position\t\t\t\t'+\
'\t\txbar - - - - -  Ice the time between 2 markers\n'+\
'<marker>,put,time,<time>\t--- Put marker at a time position\n'+\
'<marker>,put,other,<marker>    Put marker at other marker position\t\t'+\
'altr - <icename>,<marker> - - - Read top channel value into icename\n'+\
'<marker>,put,begin\t--- Put marker at begining position\n'+\
'<marker>,put,end\t\t--- Put marker at end position\n'+\
'<marker>,right,time,<time>\t--- Move marker right by time\t\t\t'+\
'ctrt--- <marker>,<time> --- Set a Marker to a time\n'+\
'<marker>,right,lmin\t--- Move marker right to local minimum\n'+\
'<marker>,right,lmax\t--- Move marker right to local maximum\n'+\
'<marker>,right,above,<value>   Move marker right until above a value\n'+\
'<marker>,right,below,<value>   Move marker right until below a value\n'+\
'<marker>,left,time,<time>\t--- Move marker left by time\n'+\
'<marker>,left,lmin\t\t--- Move marker left to local minimum\n'+\
'<marker>,left,lmax\t\t--- Move marker left to local maximum\n'+\
'<marker>,left,above,<value> -- Move marker left until above a value\n'+\
'<marker>,left,below,<value> -- Move marker left until below a value'

altkeys =['<Alt-a>','<Alt-b>','<Alt-c>','<Alt-d>','<Alt-e>','<Alt-f>','<Alt-g>',
          '<Alt-h>','<Alt-i>','<Alt-j>','<Alt-k>','<Alt-l>','<Alt-m>','<Alt-n>',
          '<Alt-o>','<Alt-p>','<Alt-q>','<Alt-r>','<Alt-s>','<Alt-t>','<Alt-u>',
          '<Alt-v>','<Alt-w>','<Alt-x>','<Alt-y>','<Alt-z>']

ctrkeys =['<Control-a>','<Control-b>','<Control-c>','<Control-d>',
        '<Control-e>','<Control-f>','<Control-g>','<Control-h>',
        '<Control-i>','<Control-j>','<Control-k>','<Control-l>',
        '<Control-m>','<Control-n>','<Control-o>','<Control-p>',
        '<Control-q>','<Control-r>','<Control-s>','<Control-t>',
        '<Control-u>','<Control-v>','<Control-w>','<Control-x>',
        '<Control-y>','<Control-z>']

cmap=['#%02x%02x%02x'%(0, 0, 0),    '#%02x%02x%02x' % (0, 0, 205),  #black,blue
    '#%02x%02x%02x' % (0, 103, 0),  '#%02x%02x%02x' % (204, 0, 205),#green,cyan
    '#%02x%02x%02x' % (204, 0, 0),  '#%02x%02x%02x' % (255, 0, 255),#red,magenta
    '#%02x%02x%02x' % (153,76,0),   '#%02x%02x%02x' % (96,96,96),   #brown,grey
    '#%02x%02x%02x' % (200,185,0),  '#%02x%02x%02x' % (0,180,180),  #gold,sky
    '#%02x%02x%02x' % (255,128,0),  '#%02x%02x%02x' % (0, 204, 0),  #orange,lgrn
    '#%02x%02x%02x' % (255,130,120),'#%02x%02x%02x' % (166,166,166),#pink,lgrey
    '#%02x%02x%02x' % (0, 204, 130),'#%02x%02x%02x' % (178,102,255),#aqua,purple
    '#%02x%02x%02x' % (100,100,255),'#%02x%02x%02x' % (240,240,240)]#grid color,textbox
ref_S = { \
 'scale_top':'11;bottom_scale,grid_scale;scale top channel',\
 'scale_time':'12;begin_time,end_time;time scale zoom',\
 'sort':'13;sort_channel;sort using channel',\
 'rename':'14;new name;rename top_channel',\
 'grid_bot':'15;bottom scale;set bootom grid',\
 'equation':'16;Equation text;process equation',\
 'insert':'17;none;insert new channel',\
 'show_chan':'18;channel number or name;show channel',\
 'regress':'19;independant_chan, dependent_chan',\
 'relate':'20;independant chan,dependent chan,fit order;linear regression model',\
 'rolloff':'21;rolloff number;set filter rate (0=brick 1=high 2=med 3=low)',\
 'filter':'22;cutoff frequency;lowpass filter top channel',\
 'notch':'23;notch frequency;notch top channel',\
 'median':'24;filter width;median filter top channel',\
 'highpass':'25;cutoff frequency;highpass filter top channel',\
 'correlate':'26;chan one,channel two;correlate two channels',\
 'Delete':'27;none;delete top channel',\
 'Up':'28;none;Move scale up 1 grid',\
 'Down':'29;none;Move scale down 1 grid',\
 'grid_space':'30;grid scale;change top grid scale',\
 'kval':'31;K number,K value;change a K value',\
 'shift_top':'32;shift time;shift top channel by time',\
 'set_samprate':'33;sample rate;set time samples/sec',\
 'edit_top':'34;none;edit data of top channel',\
 'model':'35;equation;model the top channel',\
 'question':'36;question;ask a question',\
 'factor':'37;number y levels;factor top into levels',\
 'mark_time':'38;marker,time;set a marker at time',\
 'snapshot':'39;BMP name;create a BMP of screen',\
 'overview':'40;none;set time range to show all data',\
 'mouse1':'41;none;display values left pointer position',\
 'mouse2':'42;none;middle finish zoom',\
 'wheel':'43;none;scroll wheel zoom in/out',\
 'mouse3':'44;none;right mouse click',\
 'save_CSV':'45;!filename;save dataframe to ice !filename',\
 'autoscale':'46;none;autoscale top channel',\
 'open_CSV':'47;open filename;ask to open a CSV file',\
 'to_influxdb':'48;@ice.json;save dataframe to influxdb',\
 'run_python':'49;process name,process parameters;run an external python script',\
 'markers_off':'50;none;turn all markers off',\
 'marker':'51;m1,m2,m3,etc.;execute a marker command',\
 'ice_marker':'52;ice name,marker number;create ice from top at a marker',\
 'ice_dual_marker':'53;ice name,marker1,marker2,operator;dual marker commands',\
 'restore_top':'54;none;restore the prior value of top channel',\
 'ice_insert':'55;ice name,ice value;insert a named ice value',\
 'plot_text':'56;text,xpos,ypos;plot text on screen',\
 'end_trigger':'57;condition;condition that continues macro',\
 'ice_insert':'55;ice name,ice value;insert a named ice value',\
 'integrate':'58;none;integrate the top channel',\
 'derivative':'59;none;take derivative of top channel'
 }

def put_ice( name, param): # update an ice dictionary item
    global ice
    ice.update({name: param})
def save_ice(): # ice dictionary to ice.json file
    global ice
    json_obj = json.dumps(ice, indent=4, separators=(", ", ": "), sort_keys=True)
    file = open('ice.json','w',encoding="utf-8")
    file.write(json_obj)
    file.close()
def load_ice(): # ice.json file to ice dictionary
    global ice
    jf = open('ice.json',)
    ice = json.load(jf)
    jf.close()
def print_sizes( an_array):
    if str(type(an_array))=="<class 'numpy.ndarray'>":
        print('ndarray shape',an_array.shape)
    elif str(type(an_array))=="<class 'list'>":
        rows = len(an_array)
        columns = len(an_array[0])
        print('list shape is ('+str(rows)+','+str(columns)+')')
    else:
        print('type is',type(an_array))

def clip_rectangle(a, b, x_min, y_min, x_max, y_max):

    # Intersections of f(x) = ax + b with the rectangle. (x, y, axis)
    p1, p2 = (x_min, a * x_min + b, 'x'), (x_max, a * x_max + b, 'x'),
    p3, p4 = ((y_min - b) / a, y_min, 'y'), ((y_max - b) / a, y_max, 'y')
    # Python sorts them using the first key
    p1, p2, p3, p4 = sorted([p1, p2, p3, p4])

    # Check if there is an intersection, returns the points otherwise
    if p1[2] == p2[2]:
        return (0,0)
    return (p2[:2], p3[:2])
def turn_off_numlock():
    VK_NUMLOCK = 0x90
    KEYEVENTF_EXTENDEDKEY = 0x01
    KEYEVENTF_KEYUP = 0x02
    GetKeyState = ctypes.windll.user32.GetKeyState
    keybd_event = ctypes.windll.user32.keybd_event
    if GetKeyState(VK_NUMLOCK): # if NUMLOCK is ON, toggle it OFF with  keypress
        keybd_event(VK_NUMLOCK, 0x45, KEYEVENTF_EXTENDEDKEY | 0, 0) # virtual key
        keybd_event(VK_NUMLOCK, 0x45, KEYEVENTF_EXTENDEDKEY | KEYEVENTF_KEYUP,0)
def tidy(x, n): # round x to n significant digits (more general)
    y=abs(x)
    if y <= sys.float_info.min:
        return (0.0)
    return round( x, int( n-math.ceil(math.log10(y)) ) )

def strlist( mylist): # turn a numeric list into a string
    str1 = '['
    for i in range(0,len(mylist)):
        str1 += str( tidy( mylist[i], 5))
        if i< (len(mylist)-1):
            str1 += ', '
        else:
            str1 += ']'
    return( str1)
def ice_email( subject,content):
    get_ice()
    email_address = ice['email'] # get the email address
    app_password = ice['app_password']   # get the email app_password
    footer = ice['email_footer']    # add Iceberg/Sagent footer
    conn = smtplib.SMTP_SSL('smtp.mail.yahoo.com', 465)
    conn.ehlo()
    conn.login(email_address, app_password)
    conn.sendmail(email_address,
                email_address,
                'Subject: '+subject+'\n\n'+content+'\n\n'+footer)
    conn.quit()
def get_stock_data( ticker):
    price = tidy( si.get_live_price( ticker), 4)
    latest = si.get_data( ticker )
    return( price, latest)






