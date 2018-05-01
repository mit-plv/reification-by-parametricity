#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Input::Initialization:: *)
ND=If[$Input === "",NotebookDirectory[],DirectoryName @ $InputFileName];
Print["Directory: "<>ND];
Import[FileNameJoin[{ND, (*"benchmark",*) "bench.wl"}]];
Print["Imported"];


(* ::Input::Initialization:: *)
ClearAll[DoPlot,KindsFor,DataFor,DataForConstKinds,FilterOf,XFilterOf,YFilterOf,LabelWith,LabelOneWith,GetXBoundaryReference,GetXPosReference,DataForKinds,DoPlotGen,MakeAndExport,MakeAndExportGen,DataUserOrReal,DropStyle,StyleWith,Rename];
Rename[x_]:=x;
Rename["beta; Parametricity"]:="Parametricity (reduced term)";
Rename["Parametricity; beta"]:="Parametricity (unreduced term)";
Rename[Style[x_,style___]]:=Style[Rename[x],style];
DropStyle[x_]:=x;
DropStyle[Style[x_,___]]:=x;
StyleWith[v_,x_]:=v;
StyleWith[v_,Style[x_,style___]]:=Style[v,style];
XFilterOf[xrange_,data_]:=If[SameQ[xrange,Full],data,Select[data,xrange[[1]]<=#1[[1]]<=xrange[[2]]&]];
YFilterOf[yrange_,data_]:=If[SameQ[yrange,Full],data,Select[data,yrange[[1]]<=#1[[2]]<=yrange[[2]]&]];
FilterOf[{xrange_,yrange_},data_]:=YFilterOf[yrange,XFilterOf[xrange,data]];
DataUserOrReal[name_][kind_][const_][user_]:=data[name][DropStyle[kind]][DropStyle[const]][If[DropStyle[kind]=="identity native_compute"&&DropStyle[const]=="Stats","real",user]];
KindsFor[name_,const_,range_]:=KindsFor[name,const,range]=Select[KindsSortedFor[name][const],#1!="refine let"&&SameQ[Head[DataUserOrReal[name][#1][const]["user"]],List]&&Length[FilterOf[range,DataUserOrReal[name][#1][const]["user"]]]>1&];
DataForKinds[name_,const_,range_,kinds_]:=DataForKinds[name,const,range,kinds]=Table[FilterOf[range,DataUserOrReal[name][kind][const]["user"]],{kind,kinds}];
DataForConstKinds[name_,range_,constKinds_]:=DataForConstKinds[name,range,constKinds]=Table[FilterOf[range,DataUserOrReal[name][constKind[[2]]][constKind[[1]]]["user"]],{constKind,constKinds}];
DataFor[name_,const_,range_]:=DataForKinds[name,const,range,KindsFor[name,const,range]];
GetXBoundaryReference[data_]:=Min[Map[Max[Map[#1[[1]]&,#1]]&,data]];

ClearAll[MakeCallout,CalloutWithAt,CollectInsets,CollectImagePadding,Replot,GetColor,AddColors,AddColorsToData,GetAPos,GetSortingKey,GetColorFrom,CollectImagePadding,Resort,Compare,KeyForYPos,AddColoredBox];
GetColor[colors_,idx_]:=(*From https://mathematica.stackexchange.com/a/54632/12258*)colors[[Mod[idx,Length[colors],1]]];
GetColorFrom[colors_,idx_,idxLength_]:=GetColor[colors,(*idxLength+1-*)idx];
BoxFor[text_]:="\[FilledSquare] ";
BoxFor[Style[text_,Dashing[___]]]:="\[Square] ";
BoxFor[Style[text_,Dashed]]:="\[Square] ";
AddColoredBox[colors_,text_,idx_,len_]:=
StyleWith[Row[{Style[BoxFor[text],Bold,GetColorFrom[colors,idx,len]],Rename[DropStyle[text]]}],text];
AddColors[colors_,labels_]:=MapIndexed[AddColoredBox[colors,#1,#2,Length[labels]]&,labels];
AddColorsToData[colors_,labeledData_]:=MapIndexed[Join[{#1[[1]],AddColoredBox[colors,#1[[2]],#2,Length[labeledData]]},Drop[#1,2]]&,labeledData];
GetAPos[xpos_,data_]:=SortBy[data,-Abs[#[[1]](*-xpos*)]&][[1]];
GetSortingKey[xpos_,data_,count_: 10]:=SortBy[data,-Abs[#[[1]]-xpos]&][[1]](*GetAPos[xpos,data]*)(*Mean[Map[#\[LeftDoubleBracket]2\[RightDoubleBracket]&,Take[SortBy[data,Abs[#1\[LeftDoubleBracket]1\[RightDoubleBracket]-xpos]&],count]]]*);
Compare[data1_,data2_]:=With[{xs1=Map[First,data1],xs2=Map[First,data2]},With[{x=Min[Max[xs1],Max[xs2]]},With[{y1=SortBy[data1,Abs[#[[1]]-x]&][[1]][[2]],y2=SortBy[data2,Abs[#[[1]]-x]&][[1]][[2]]},y1>=y2]]];
KeyForYPos[{_,Offset[{dx_,dy_},{x_,y_}]}]:=-y;
Resort[xpos_,dataLabelYPos_,maxIter_: 1]:=Module[{data,label,ypos},{data,label,ypos}=Transpose[dataLabelYPos];
{data,label}=Transpose[Sort[Transpose[{data,label}],Compare[#1[[1]],#2[[1]]]&]];
ypos=SortBy[ypos,KeyForYPos];
Transpose[{data,label,ypos}]];
MakeCallout[{apos_,data_,label_,{_,Offset[{dx_,dy_},{x_,y_}]}}]:=Callout[StyleWith[data,label],DropStyle[label],{{x,y},{0,0.5}},apos];
CalloutWithAt[colors_,xpos_,ypositions_,data_,labels_]:=Module[{labeledData},labeledData=Transpose[{data,labels,ypositions}];
labeledData=AddColorsToData[colors,Resort[xpos,labeledData]];
labeledData=Map[Join[{GetAPos[xpos,#[[1]]]},#]&,labeledData];
MakeCallout/@labeledData];
CollectInsets[{v___}]:=Flatten[CollectInsets/@{v}/.CollectInsets[_]:>{}];
CollectInsets[Graphics[v___]]:=CollectInsets[{v}];
CollectInsets[GraphicsGroup[v___]]:=CollectInsets[{v}];
CollectInsets[Text[args___]]:=Text[args];
CollectInsets[Hue[___]]:={};
CollectInsets[Directive[___]]:={};
CollectInsets[Point[___]]:={};
CollectInsets[CapForm[___]]:={};
CollectInsets[JoinForm[___]]:={};
CollectInsets[EdgeForm[___]]:={};
CollectInsets[BSplineCurve[___]]:={};
CollectInsets[RGBColor[___]]:={};
CollectInsets[Polygon[___]]:={};
CollectInsets[_->_]:={};
CollectInsets[_:>_]:={};
CollectImagePadding[___,OptionsPattern[Graphics]]:=OptionValue[ImagePadding];
Replot[xpos_,Plot_,data_,labels_,opts___]:=Module[{plot0,ypos,padding,allopts,colors},colors="DefaultPlotStyle"/.(Method/.Charting`ResolvePlotTheme[Automatic,Plot]);
plot0=Plot[data,PlotLabels->AddColors[colors,Map[DropStyle,labels]],opts];
allopts=plot0/.Graphics[_,v___]:>{v};
padding=CollectImagePadding@@plot0;
ypos=Sort[CollectInsets[plot0]/.Text[_,Offset[d_,{x_,y_}],{0,0}]:>{y,Offset[d,{x,y}]}];
Plot[CalloutWithAt[colors,xpos,ypos,data,labels],opts,ImagePadding->padding,PlotRangeClipping->False]/.Text[v_,Offset[{dx_,dy_},{x_,y_}],{0,0}]:>Text[v,Offset[{12(*magic number*),dy},{x,y}],{Left,Center}] (*fix for pdf export,see https://mathematica.stackexchange.com/questions/162942/how-can-i-get-mathematica-to-not-mis-align-plot-labels-when-exporting-to-pdf-wit/163458#163458*)];

DoPlotGen[Plot_,name_,const_,{xrange_,yrange_},extraname_: "",oplotlabel_: Default,okinds_: Default,oconstKinds_: Default,opts___]:=Module[{kinds,plotlabel,data,labels,xpos},plotlabel=If[SameQ[oplotlabel,Default],If[extraname=="",{const,name},{const,name,extraname}],oplotlabel];
kinds=If[SameQ[okinds,Default],KindsFor[name,const,{xrange,yrange}],okinds];
labels=If[SameQ[oconstKinds,Default],kinds,Map[#[[2]]&,oconstKinds]];
data=If[SameQ[oconstKinds,Default],DataForKinds[name,const,{xrange,yrange},Map[DropStyle,kinds]],DataForConstKinds[name,{xrange,yrange},Map[DropStyle,oconstKinds]]];
xpos=GetXBoundaryReference[data];
Replot[xpos,Plot,data,labels,Joined->True,ImageSize->800,AxesLabel->{n//DisplayForm,"Time (s)"},PlotRange->{Full,Full},PlotLabel->plotlabel,opts]];

DoPlot[Plot_,name_,const_,{xrange_,yrange_},extraname_,opts___]:=DoPlotGen[Plot,name,const,{xrange,yrange},extraname,Default,Default,Default,opts];

MakeAndExportGen[Plot_,name_,const_,range_,extratitle_: "",oplotlabel_: Default,ofname_: Default,okinds_: Default,oconstKinds_: Default,opts___]:=Module[{plot,extraname,fname,plotlabel,kinds},fname=If[SameQ[ofname,Default],StringReplace[name<>"-"<>const,{" "->"-","_"->"-"}]<>If[SameQ[Plot,ListLogLogPlot],"-loglog",""]<>extratitle<>".pdf",ofname<>".pdf"];
extraname=If[SameQ[Plot,ListLogLogPlot],"log-log"<>extratitle,extratitle];
Print["Plotting: "<>name<>"_"<>const<>If[SameQ[Plot,ListLogLogPlot]," (log-log)",""]<>extratitle<>If[Not[SameQ[oplotlabel,Default]]," ("<>oplotlabel<>")",""]];
plot=DoPlotGen[Plot,name,const,range,extraname,oplotlabel,okinds,oconstKinds,opts];
If[$Input==="",Print[plot]];
Print[Export[FileNameJoin[{ND,fname}],plot]]];

MakeAndExport[Plot_,name_,const_,range_,extratitle_: "",opts___]:=MakeAndExportGen[Plot,name,const,range,extratitle,Default,Default,Default,Default,opts];

MakeAndExportGen[ListPlot,"big_flat","actual reif",{Full,{0,7}},"","Size of term (no binders) vs Reification time","actual-reif-no-binders"]
MakeAndExportGen[ListPlot,"big","actual reif",{{0,300},{0,5}},"","Size of term (with binders) vs Reification time","actual-reif-with-binders"]
With[{range={Full,{0,10}}},
MakeAndExportGen[ListLogLogPlot,"big","actual reif",range,"","Size of term (with binders) vs Reification time (log-log)","actual-reif-with-binders-log-log",Default,
Join[
Map[{"actual reif",#}&,KindsFor["big","actual reif",range]],
Map[{"Stats",Style[#,Dashed]}&,{"identity lazy","lazy Denote","transitivity"}]
]]]
With[{range={{100,20000},{0,10}}},
MakeAndExportGen[ListLogLogPlot,"big","actual reif",range,"","Size of term (with binders) vs Reification time (log-log)","actual-reif-with-binders-log-log-subset",Default,
Join[
Map[{"actual reif",#}&,{"ParsingElaborated","beta; Parametricity", "TemplateCoq","Parametricity; beta", "OCaml","Ltac2LowLevel"}],
Map[{"Stats",Style[#,Dashed]}&,{"identity lazy","lazy Denote","transitivity"}]
]]]
MakeAndExportGen[ListLogLogPlot,"big_flat","Stats",{Full,Full},"","Size of term (without binders) vs Operation time (log-log)"]
MakeAndExportGen[ListLogLogPlot,"big_flat","actual reif",{Full,Full},"","Size of term (without binders) vs Reification time (log-log)"]
MakeAndExportGen[ListPlot,"big_flat","actual reif",{Full,Full},"","Size of term (without binders) vs Reification time"]
MakeAndExportGen[ListPlot,"big","Stats",{Full,{0,5}},"","Size of term (with binders) vs Operation time",Default,Default,Default,AxesOrigin->{0,0}]
MakeAndExportGen[ListLogLogPlot,"big","Stats",{Full,{0,5}},"","Size of term (with binders) vs Operation time (log-log)"]
MakeAndExportGen[ListLogLogPlot,"big","actual reif",{{0,1000},Full},"","Size of term (with binders) vs Reification time (log-log)"]
MakeAndExportGen[ListPlot,"big","actual reif",{{0,300},{0,5}},"","Size of term (with binders) vs Reification time"]
MakeAndExportGen[ListLogLogPlot,"big","actual reif",{{1500,20000},{0,7}},"","Size of term (with binders) vs Reification time (log-log, large terms only)","big-actual-reif-loglog-2"]
MakeAndExportGen[ListPlot,"big","actual reif",{{1500,20000},{0,7}},"","Size of term (with binders) vs Reification time (large terms only)","big-actual-reif-2"]
MakeAndExportGen[ListLogLogPlot,"big","norm reif",{{1500,20000},{0,7}},"","Size of term (with binders) vs Reification+normalization time (log-log)"]
MakeAndExportGen[ListPlot,"big","norm reif",{{1500,20000},{0,7}},"","Size of term (with binders) vs Reification+normalization time"]
