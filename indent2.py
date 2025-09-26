
import os
import clips
import streamlit as st
import re

# os.chdir("D:\\Personel\\Projects Anne\\indentERB")

# Identify a ruby template tag in a line
def getTag(s_):
    s = s_.strip()
    # Comment
    if s.startswith("#") or s == '':
        return("")
    # Inclusive
    elif "<%=" in s and ("%>" in s or "-%>" in s):
        return("")
    elif "<%=" in s:
        return("SO")
    # Open/Close
    elif s.split("<%")[0] == '' and s.split("%>")[-1] == '':
        return("OC")
    # Open
    elif s.split("<%")[0] == '':
        return("O")
    # Close
    elif s.split("%>")[-1] == '':
        return("C")
    else:
        return("")
    
# Get  ruby tags for all lines    
def getTags(lines):
    tags = []
    lt = "close"
    for (i,v) in enumerate(lines):
        tags.append(getTag(v))
    return(tags)

# Get a ruby block open command or nil
def getKw(s_):
    s = s_.strip()
    if s == '': return("")
    wd = s.split()
    if s.startswith("#"): return("")
    if len(wd) >= 2:
        if (wd[0] == "<%" or wd[0] == "<%-") and wd[1] == "#": return("")
        if wd[0] == "<%#" or wd[0] == "<%-#": return("")
    if "next" in wd and "if" in wd: return("")
    if "break" in wd and "if" in wd: return("")
    if "if" in wd: return("if")
    elif "do" in wd: return("do")
    elif "begin" in wd: return("begin")
    elif "else" in wd: return("else")
    elif "elsif" in wd: return("elsif")
    elif "end" in wd: return("end")
    else: return("")
 
 
# Update tags with open and close extrapolation 
def extrapolateTags(tags):
    newtags = []
    lasttag = "C"
    for (i,v) in enumerate(tags):
        if v == "O":
            lasttag = "O"
            newtags.append(v)
        elif v == "C":
            if lasttag == 'SO':
                newtags.append("")
            else:
                newtags.append(v)  
            lasttag = "C"            
        elif v == "SO":
            lasttag = "SO"
            newtags.append("")
        elif v == "OC":
            lasttag = "OC"
            newtags.append(v)
        elif v == '':
            match lasttag:
                case 'O':
                    newtags.append("I")
                case 'SO':
                    newtags.append("")
                case 'C' | 'OC':
                    newtags.append("")
    return(newtags)
    
def updateTagsWithKeywords(tags):
    newtags = []
    for (i,v) in enumerate(tags):
        if v == "":
            newtags.append((i,v,""))
        else:
            kw = getKw(lines[i])
            #print(kw,lines[i])
            newtags.append((i,v,kw))
    return(newtags)

# Exported python function to reorder the tags sequence for rule processing
def reorder():
    ff = list(env.facts())
    ffs = [(str(i),i) for i in ff]
    cnt = 0
    for i in ffs:
        fstr = i[0]
        if 's1' in fstr:
            wd = fstr[1:-1].split()
            cnt+=1
            i[1].retract()
            env.eval(f"(assert (s1 {wd[1]} {wd[2]} {cnt}))")

# Helper CLIPS functions
def ff(): env.eval("(facts)")
def ru(): env.run()
def re(): env.reset()

# Assert tags facts
def assertTags(tags):
    cnt = 0
    for i in tags:
        if i[2] != '':
            cnt+=1
            env.eval(f"(assert (s1 {i[0]} {i[2]} {cnt}))")
 
# Indent code for display
def showIndentedCode(lines,tags,trace):
    codes = []
    cnt = 0
    #trace = 1
    indentC = 0
    indent = "   "
    for (i,v) in enumerate(tags):
        curline = lines[i].strip()
        #if i > 60:
        #    import pdb
        #    pdb.set_trace()
        match v[1]:
            case '':
                #print(indent*indentC + curline)
                codes.append(indent*indentC + curline)
            case 'OC' | 'O' | 'I' | 'C':
                match v[2]:
                    case 'if' | 'do' | 'begin':
                        #print(indent*indentC + curline)
                        codes.append(indent*indentC + curline)
                        indentC+=1
                        if trace:
                            if v[1] == 'O' or v[1] == 'I':
                                #print(indent*indentC + f"puts \"---> {cnt}\"")
                                codes.append(indent*indentC + f"puts \"---> {cnt}\"")
                            else:
                                #print(indent*indentC + f"<%- puts \"---> {cnt}\" -%>")
                                codes.append(indent*indentC + f"<%- puts \"---> {cnt}\" -%>")
                            cnt+=1
                        
                    case 'else' | 'elsif':
                        #print(indent*(indentC-1) + curline)
                        codes.append(indent*(indentC-1) + curline)
                        if trace: 
                            #print(indent*indentC + f"puts \"---> {cnt}\"")
                            if v[1] == 'O' or v[1] == 'I':
                                #print(indent*indentC + f"puts \"---> {cnt}\"")
                                codes.append(indent*indentC + f"puts \"---> {cnt}\"")
                            else:
                                #print(indent*indentC + f"<%- puts \"---> {cnt}\" -%>")
                                codes.append(indent*indentC + f"<%- puts \"---> {cnt}\" -%>")
                            #codes.append(indent*indentC + f"puts \"---> {cnt}\"")
                            cnt+=1
                    case 'end':
                        indentC+=-1
                        #print(indent*indentC + curline)
                        codes.append(indent*indentC + curline)
                    case '': # open or close not keyword
                        #print(indent*indentC + curline)
                        codes.append(indent*indentC + curline)
                        
    return("\n".join(codes))                
                    
              
# CLIPS Rules
r8 = """
(defrule r8 
    ?f1 <- (s1 ?lineno1 if  ?seq1)
    ?f2 <- (s1 ?lineno2 else  ?seq2)
    ?f3 <- (s1 ?lineno3 end ?seq3)
    (test (and (= 1 (- ?seq3 ?seq2)) (= 1 (- ?seq2 ?seq1))))
 =>
    (println "R8 Found if else end at " ?lineno1)
    (retract ?f1 ?f2 ?f3)
    ;;(facts)
    (cc)
)"""

r7 = """
(defrule r7 
    ?f1 <- (s1 ?lineno1 if  ?seq1)
    ?f2 <- (s1 ?lineno2 end ?seq2)
    (test (= 1 (- ?seq2 ?seq1)))
 =>
    (println "R7 Found if end at " ?lineno1)
    (retract ?f1 ?f2)
    (cc)

)"""

r9 = """
(defrule r9 
    ?f1 <- (s1 ?lineno1 if  ?seq1)
    ?f2 <- (s1 ?lineno2 elsif ?seq2)
    ?f3 <- (s1 ?lineno3 else ?seq3)
    ?f4 <- (s1 ?lineno4 end ?seq4)
    (test (= 1 (- ?seq2 ?seq1)))
    (test (= 1 (- ?seq3 ?seq2)))
    (test (= 1 (- ?seq4 ?seq3)))
 =>
    (println "R9 Found if elsif else end at " ?lineno1)
    (retract ?f1 ?f2 ?f3 ?f4)
    (cc)

)"""

r10 = """
(defrule r10 
    ?f1 <- (s1 ?lineno1 do  ?seq1)
    ?f2 <- (s1 ?lineno2 end ?seq2)
    (test (= 1 (- ?seq2 ?seq1)))
 =>
    (println "R10 Found do end at " ?lineno1)
    (retract ?f1 ?f2)
    (cc)

)"""

r11 = """
(defrule r11 
    ?f1 <- (s1 ?lineno1 begin  ?seq1)
    ?f2 <- (s1 ?lineno2 end ?seq2)
    (test (= 1 (- ?seq2 ?seq1)))
 =>
    (println "R11 Found begin end at " ?lineno1)
    (retract ?f1 ?f2)
    (cc)

)"""
#
# Main
#

#f = open("template2.txt","r")
#lines = f.readlines()
#f.close()

st.set_page_config(layout="wide")
st.header("Ruby Template Validator")

template_text = st.text_area("Template to parse", "")

if st.button("Validate"):
    if template_text=="":
        st.warning('The template is empty', icon="⚠️")
        st.stop()
    else:
        import re
        
        template_text = re.sub(pattern="<%-(?!\\s)",string=template_text,repl="<%- ")
        lines = template_text.split("\n")

        # Generate ruby tags sequence on specific lines
        tags = getTags(lines)
        st.write(tags)

        # Extrapolate ruby tags between open and close tags
        newtags = extrapolateTags(tags)
        st.write(newtags)
        
        # Create final tag list with line number and block keyword for clips parsing    
        newtags2 = updateTagsWithKeywords(newtags)
        st.write(newtags2)
                
        # Initialize CLIPS
        env = clips.Environment()
        env.eval("(set-strategy simplicity)")

        # Register function
        env.define_function(reorder)

        # Register python reordering function
        env.build("(deffunction cc () (reorder))")

        #env.clear()
        #env.reset()

        # Build rules
        env.build(r8)
        env.build(r7)
        env.build(r9)
        env.build(r10)
        env.build(r11)

        # Assert facts
        assertTags(newtags2)
        initfacts = [i for i in env.facts()]
        st.write(initfacts)

        # Run
        env.run()
        st.write("No issue.")

        # Check results
        leftovers = [i for i in env.facts()]
        st.write(leftovers)
        for i in leftovers:
            wd = str(i)[1:-1].split()
            st.write(f"Line {int(wd[1]) + 1} : {wd[2]}")

        #if len(leftovers) != 0: st.stop()
        
        # Indent code
        newIndentText = showIndentedCode(lines,newtags2,0)
        
        template_text = st.text_area("Indented template", newIndentText)
        
        newIndentText2 = showIndentedCode(lines,newtags2,1)
        
        template_text_trace = st.text_area("Indented template with trace", newIndentText2)
                
        st.stop()
# Indent code

