MACHINE Enrolment
SETS COURSE; STUDENT
VARIABLES courses,students,enrol,waiting,capacity
INVARIANT
 courses:POW(COURSE) & students:POW(STUDENT) &
 enrol:COURSE<->STUDENT & waiting:COURSE+->seq(STUDENT) &
 capacity:COURSE+->NAT1 &
 dom(enrol)<:courses & ran(enrol)<:students &
 dom(waiting) <: dom(enrol) &  
 dom(capacity)=courses & 
 !(c).(c: dom(waiting) => ran(waiting(c))<:students) &
 !(c).(c: dom(waiting) => card({c}<|enrol)=capacity(c)) &
 !(c).(c:dom(enrol)/\dom(waiting) => ran({c}<|enrol) /\ ran(waiting(c))={})
INITIALISATION 
 courses:={};
 students:={}; 
 enrol:={} ; waiting:={} ; capacity:={}
OPERATIONS
  addcourse(cc,nn) = PRE cc:COURSE & cc/:courses & nn:NAT1 THEN courses:=courses\/{cc}; capacity(cc):=nn END;
  delcourse(cc) = PRE cc:courses & {cc}<|enrol={} & {cc}<|waiting ={} THEN courses:=courses-{cc} ; capacity:= {cc} <<|capacity END;
  addstudent(ss) = PRE ss:STUDENT & ss/:students THEN students:=students\/{ss} END;
  DelStudent(ss) = PRE ss:students & enrol |> {ss}={} & not(#(c).(c: dom(waiting) & ss: ran(waiting(c)))) THEN students:=students - {ss} END;
  Enrol(cc,ss) = PRE cc:courses & ss:students & (cc,ss)/:enrol & card({cc}<|enrol)<capacity(cc) THEN enrol:=enrol\/{cc|->ss} END;
  Withdraw(cc,ss) = PRE cc:courses & ss:students & (cc,ss):enrol THEN 
    enrol:=enrol-{cc|->ss} ; 
    IF cc:dom(waiting) 
    THEN 
      enrol:=enrol\/{cc|->first(waiting(cc))} ; waiting(cc):=tail(waiting(cc)); 
      IF waiting(cc)={} THEN waiting:= {cc}<<|waiting END 
    END 
  END;
  AddWaiting(cc,ss) = PRE cc:courses & ss:students & (cc,ss)/:enrol & card({cc}<|enrol)=capacity(cc) & (cc:dom(waiting) => ss /:ran(waiting(cc))) THEN
   IF cc:dom(waiting) 
    THEN waiting(cc):=waiting(cc)^[ss]
    ELSE waiting:=waiting\/{cc|->[ss]} END 
  END;
  RemoveWaiting(cc,ss) = PRE cc:courses & ss:students & ss:ran(waiting(cc)) THEN 
    VAR x,y,s IN x:=waiting(cc); s:=size(x); y:=[] ;
      WHILE s>0 DO
        IF first(x)/=ss THEN y:=y^[first(x)] END;
        x:=tail(x);
        s:=size(x)
      INVARIANT card(y)<= card(waiting(cc))
      VARIANT s
      END;
      IF y/=[] THEN waiting(cc):=y ELSE waiting:= {cc}<<|waiting END 
    END
  END
END

