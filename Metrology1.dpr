program Metrology1;

{$APPTYPE CONSOLE}

uses
  SysUtils;

const
  FileAddress = 'Analyzed.txt';

type
  TGlobal = Record
    ActualVariableReferences: Integer;
    GlobalVariableName: string[20];
  end;

  TStruct = ^TStructRecord;

  TStructRecord = Record
    CurrentStruct: (_HEADER, _NAMESPACE, _CLASS, _METHOD, _COMPOUND_OPERATOR);
    Next: TStruct;
    Prev: TStruct;
  end;

  TMethod = Record
    MethodName: string[30];
    MethodAccess: string;
    MethodText: array[1..100] of string;
    ArrayVariables: array[1..30] of string;
  end;

  TClass = Record
    ClassName: string[30];
    ClassText: array[1..50] of string;
    ArrayMethods: array[1..40] of string;
    ArrayGlobalVariables: array[1..50] of string;
  end;

  TArrayOfClasses = array [1..50] of TClass;

  TArrayOfMethods = array [1..1000] of TMethod;

  TSetOfTypes = array [1..18] of string;

  TSetOfModifiers = array [1..2] of string;

  TClassGlobalVariables = array [1..50] of string;

  TArrayOfGlobalVariables = array [1..100] of TGlobal;

const
  Types: TSetOfTypes = ('void', 'int', 'uint', 'byte', 'sbyte', 'short', 'ushort', 'long', 'ulong', 'float', 'double', 'decimal', 'char', 'string', 'bool', 'object', 'var', '');
  Modifiers: TSetOfModifiers = ('private', 'public');
  NumberOfTypes = 18;
  NumberOfModifiers = 2;

var
  AnalyzedFile: TextFile;
  ArrayLinesOfCode: array of string;
  SizeOfArrayLinesOfCode, ClassesCounter, MethodsCounter, GlobalVariablesTotalNumber: Integer;
  ArrayOfClasses: TArrayOfClasses;
  ArrayOfMethods: TArrayOfMethods;
  ArrayOfGlobalVariables: TArrayOfGlobalVariables;

function AddNewStruct(var Current: TStruct): TStruct;
var
  Temp: TStruct;
begin
  New(Temp);
  Current^.Next := Temp;
  Temp := Current;
  Current := Current^.Next;
  Current^.Prev := Temp;
  Current^.Next := nil;
  Result := Current;
end;

function DeleteStruct(var Current: TStruct): TStruct;
begin
  Current^.Prev^.Next := Current^.Next;
  Current := Current^.Prev;
  Result := Current;
end;

function FindMethodName(var CurrentLine: string): string;
var
  StartPosition, FinishPosition, ConstantSetCounter, BreacketsPosition, Position: Integer;
  BooleanModifier, BooleanReturnType, BooleanBrackets, _Continue: Boolean;
begin
  BooleanModifier := false;
  BooleanReturnType := False;
  BooleanBrackets := False;

  ConstantSetCounter := 0;
  StartPosition := 0;
  while ((ConstantSetCounter < NumberOfModifiers) and (StartPosition = 0)) do
  begin
    Inc(ConstantSetCounter);
    StartPosition := AnsiPos(Modifiers[ConstantSetCounter], CurrentLine);
  end;
  if ((StartPosition = 1) and (CurrentLine[StartPosition + length(Modifiers[ConstantSetCounter])] = ' ')) then
  begin
    BooleanModifier := True;
  end;

  ConstantSetCounter := 1;
  BreacketsPosition := AnsiPos('(', CurrentLine);
  if BreacketsPosition <> 0 then
  begin
    BooleanBrackets := True;
  end;
  FinishPosition := BreacketsPosition;

  ConstantSetCounter := 0;
  StartPosition := 0;
  _Continue := True;
  while ((ConstantSetCounter < NumberOfTypes) and (_Continue = true)) do
  begin
    Inc(ConstantSetCounter);
    Position := AnsiPos(Types[ConstantSetCounter], CurrentLine);
    if ((Position < BreacketsPosition) and (Position <> 0)) then
    begin
      StartPosition := Position;
      _Continue := false;
    end;
  end;
  if ((StartPosition <> 0) and (CurrentLine[StartPosition - 1] = ' ') and (CurrentLine[StartPosition + Length(Types[ConstantSetCounter])] = ' ')) then
  begin
    BooleanReturnType := True;
  end;

  if ((BooleanModifier) and (BooleanReturnType) and (BooleanBrackets)) then
  begin
    StartPosition := StartPosition + Length(Types[ConstantSetCounter]);
    Result := Trim(Copy(CurrentLine, StartPosition, (FinishPosition - StartPosition)));
  end
  else
    Result := '';
end;

function FindClassName(const CurrentLine: string): string;
const 
  Keyword_Class= 'class';
  LengthKeyword_Class= 5;
var
  StartPosition: Integer;
begin
  Result := '';
  StartPosition := AnsiPos(Keyword_Class, CurrentLine);
  if ((StartPosition <> 0) and ((CurrentLine[StartPosition - 1] = ' ') or (StartPosition = 1)) and (CurrentLine[StartPosition + LengthKeyword_Class] = ' ')) then
  begin
    StartPosition := StartPosition + LengthKeyword_Class;
    Result := Trim(Copy(CurrentLine, StartPosition, (Length(CurrentLine) - (StartPosition) + 1)));
  end;
end;

procedure FindGlobalVariablesInLine(var ArrayGlobalVariablesInLine: TClassGlobalVariables; var GlobalVariablesInLineNumber: Integer; CurrentLine: string);
var
  StartPosition, FinishPosition, ConstantSetCounter: Integer;
  BooleanModifier, BooleanReturnType, BooleanBrackets, BooleanConstant, BooleanComma: Boolean;
begin
  BooleanModifier := false;
  BooleanReturnType := False;
  BooleanBrackets := False;
  BooleanConstant := False;
  GlobalVariablesInLineNumber := 0;
  ArrayGlobalVariablesInLine[GlobalVariablesInLineNumber + 1] := '';

  StartPosition := 0;
  StartPosition := AnsiPos('public', CurrentLine);
  if ((StartPosition = 1) and (CurrentLine[StartPosition + length('public')] = ' ')) then
  begin
    BooleanModifier := True;
  end;

  ConstantSetCounter := 1;
  StartPosition := AnsiPos('(', CurrentLine);
  if (StartPosition <> 0) then
  begin
    BooleanBrackets := True;
  end;

  StartPosition := AnsiPos('const', CurrentLine);
  if StartPosition <> 0 then
  begin
    if ((CurrentLine[StartPosition - 1] = ' ') and (CurrentLine[StartPosition + Length('const')] = ' ')) then
      BooleanConstant := True;
  end;

  ConstantSetCounter := 0;
  StartPosition := 0;
  while ((ConstantSetCounter < NumberOfTypes) and (StartPosition = 0)) do
  begin
    Inc(ConstantSetCounter);
    StartPosition := AnsiPos(Types[ConstantSetCounter], CurrentLine);
  end;
  if ((StartPosition <> 0) and (CurrentLine[StartPosition - 1] = ' ') and (CurrentLine[StartPosition + Length(Types[ConstantSetCounter])] = ' ')) then
  begin
    BooleanReturnType := True;
  end;

  FinishPosition := AnsiPos(',', CurrentLine);
  if (FinishPosition = 0) then
  begin
    FinishPosition := AnsiPos('=', CurrentLine);
    if (FinishPosition = 0) then
      FinishPosition := AnsiPos(';', CurrentLine);
  end;

  if ((BooleanModifier) and (BooleanReturnType) and (not (BooleanBrackets)) and (not (BooleanConstant))) then
  begin
    StartPosition := StartPosition + Length(Types[ConstantSetCounter]);
    Inc(GlobalVariablesInLineNumber);
    ArrayGlobalVariablesInLine[GlobalVariablesInLineNumber] := Trim(Copy(CurrentLine, StartPosition, (FinishPosition - StartPosition)));
    if CurrentLine[FinishPosition] = ',' then
      BooleanComma := True;
    while (BooleanComma = True) do
    begin
      if CurrentLine[FinishPosition] = ',' then
        Delete(CurrentLine, FinishPosition, 1);
      StartPosition := FinishPosition;
      FinishPosition := AnsiPos(',', CurrentLine);
      if (FinishPosition = 0) then
      begin
        BooleanComma := False;
        Inc(GlobalVariablesInLineNumber);
        ArrayGlobalVariablesInLine[GlobalVariablesInLineNumber] := Trim(Copy(CurrentLine, StartPosition, (AnsiPos(';', CurrentLine) - StartPosition)));
      end
      else
      begin
        Inc(GlobalVariablesInLineNumber);
        ArrayGlobalVariablesInLine[GlobalVariablesInLineNumber] := Trim(Copy(CurrentLine, StartPosition, (FinishPosition - StartPosition)));
      end
    end;
  end;
end;

procedure FindFormalParameters(var Method: TMethod; CurrentLine: string);
var
  StartPosition, FinishPosition, FormalParametersCounter, ConstantSetCounter, NearestPunctuation, Position: Integer;
  BooleanComma, _Continue: Boolean;
begin
  StartPosition := AnsiPos('(', CurrentLine);
  Delete(CurrentLine, 1, StartPosition);
  Method.ArrayVariables[1] := IntToStr(0);
  FormalParametersCounter := 1;
  BooleanComma := true;
  repeat
    CurrentLine := Trim(CurrentLine);
    _Continue := true;
    StartPosition := 1;
    ConstantSetCounter := 0;
    NearestPunctuation := AnsiPos(',', CurrentLine);
    if NearestPunctuation = 0 then
	begin
      NearestPunctuation := AnsiPos(')', CurrentLine);
	end;  
    if CurrentLine[1] <> ')' then
    begin
      while ((ConstantSetCounter < NumberOfTypes) and (_Continue = true)) do
      begin
        Inc(ConstantSetCounter);
        Position := AnsiPos(Types[ConstantSetCounter], CurrentLine);
        if ((Position < NearestPunctuation) and (Position <> 0)) then
        begin
          _Continue := false;
          StartPosition := Position;
        end;
      end;
      StartPosition := StartPosition + Length(Types[ConstantSetCounter]);
      FinishPosition := AnsiPos(',', CurrentLine);
      if (FinishPosition = 0) then
      begin
        FinishPosition := AnsiPos(')', CurrentLine);
        BooleanComma := False;
      end;
      inc(FormalParametersCounter);
      Method.ArrayVariables[FormalParametersCounter] := Trim(Copy(CurrentLine, StartPosition, FinishPosition - StartPosition));
      Method.ArrayVariables[1] := IntToStr(FormalParametersCounter);
      Delete(CurrentLine, 1, FinishPosition);
    end
    else
      BooleanComma := false;
  until BooleanComma = false;
end;

procedure FindLocalVariablesInMethod(var Method: TMethod; CurrentLine: string);
var
  LocalVariablePositionInLine, ConstantSetCounter, CurrentVariablesInMethod, FinishPosition: Integer;
  BooleanComma: Boolean;
begin
  CurrentVariablesInMethod := StrToInt(Method.ArrayVariables[1]);
  if  CurrentVariablesInMethod=0 then
  begin
    Inc(CurrentVariablesInMethod);
  end;
  FinishPosition := AnsiPos('=', CurrentLine);
  if (FinishPosition = 0) then
  begin
    FinishPosition := AnsiPos(',', CurrentLine);
    if (FinishPosition = 0) then
      FinishPosition := AnsiPos(';', CurrentLine);
  end;
  ConstantSetCounter := 0;
  LocalVariablePositionInLine := 0;
  while ((ConstantSetCounter < NumberOfTypes) and (LocalVariablePositionInLine = 0)) do
  begin
    Inc(ConstantSetCounter);
    LocalVariablePositionInLine := AnsiPos(Types[ConstantSetCounter], CurrentLine);
  end;
  if ((LocalVariablePositionInLine <> 0) and (CurrentLine[LocalVariablePositionInLine + Length(Types[ConstantSetCounter])] = ' ')) then
  begin
    LocalVariablePositionInLine := LocalVariablePositionInLine + Length(Types[ConstantSetCounter]);
    inc(CurrentVariablesInMethod);
    Method.ArrayVariables[CurrentVariablesInMethod] := Trim(Copy(CurrentLine, LocalVariablePositionInLine, (FinishPosition - LocalVariablePositionInLine)));
    Method.ArrayVariables[1] := IntToStr(CurrentVariablesInMethod);
    if CurrentLine[FinishPosition] = ',' then
      BooleanComma := True;
    while (BooleanComma = True) do
    begin
      if CurrentLine[FinishPosition] = ',' then
      begin
        Delete(CurrentLine, FinishPosition, 1);
      end;
      LocalVariablePositionInLine := FinishPosition;
      FinishPosition := AnsiPos(',', CurrentLine);
      if (FinishPosition = 0) then
      begin
        BooleanComma := False;
        Inc(CurrentVariablesInMethod);
        Method.ArrayVariables[CurrentVariablesInMethod] := Trim(Copy(CurrentLine, LocalVariablePositionInLine, (AnsiPos(';', CurrentLine) - LocalVariablePositionInLine)));
        Method.ArrayVariables[1] := IntToStr(CurrentVariablesInMethod);
      end
      else
      begin
        Inc(CurrentVariablesInMethod);
        Method.ArrayVariables[CurrentVariablesInMethod] := Trim(Copy(CurrentLine, LocalVariablePositionInLine, (FinishPosition - LocalVariablePositionInLine)));
        Method.ArrayVariables[1] := IntToStr(CurrentVariablesInMethod);
      end;
    end;
  end;
end;

procedure DivideCodeIntoMethodsAndClasses(LinesNumber: Integer);
var
  State: (_COMMENT, _STRING, _CODE);
  LinesCounter, SymbolsCounter, GlobalVariablesCounter, GlobalVariablesInLineCounter: Integer;
  MethodListCounter, MethodLinesCounter, ClassLinesCounter: Integer;
  BooleanTwoSlashes: Boolean;
  Struct: TStruct;
  CodeLine: string;
  ArrayGlobalVariablesInLine: TClassGlobalVariables;
  GlobalVariablesInLineNumber: Integer;
begin
  New(Struct);
  Struct^.CurrentStruct := _HEADER;
  Struct^.Prev := nil;
  Struct^.Next := nil;
  ClassesCounter := 0;
  State := _CODE;
  MethodsCounter := 0;
  for LinesCounter := 0 to (LinesNumber - 1) do
  begin
    SymbolsCounter := 1;
    BooleanTwoSlashes := false;
    CodeLine := '';
    ArrayLinesOfCode[LinesCounter] := Trim(ArrayLinesOfCode[LinesCounter]);
    while (SymbolsCounter <> (Length(ArrayLinesOfCode[LinesCounter]) + 1)) do
    begin
      if (BooleanTwoSlashes = false) then
      begin
        case State of
          _COMMENT:
            begin
              if ((ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '*') and (ArrayLinesOfCode[LinesCounter][SymbolsCounter + 1] = '/')) then
              begin
                State := _CODE;
                Inc(SymbolsCounter);
              end
              else
                Inc(SymbolsCounter);
            end;
          _STRING:
            begin
              if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '"') then
              begin
                State := _CODE;
                Inc(SymbolsCounter);
              end
              else
                Inc(SymbolsCounter);
            end;
          _CODE:
            begin
              if ((ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '/') and (ArrayLinesOfCode[LinesCounter][SymbolsCounter + 1] = '*')) then
              begin
                State := _COMMENT;
                Inc(SymbolsCounter);
              end
              else if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '"') then
              begin
                State := _STRING;
                Inc(SymbolsCounter);
              end
              else if ((ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '/') and (ArrayLinesOfCode[LinesCounter][SymbolsCounter + 1] = '/')) then
              begin
                State := _CODE;
                BooleanTwoSlashes := true;
              end;

              if (State = _CODE) and (BooleanTwoSlashes = false) then
              begin
                case Struct^.CurrentStruct of
                  _HEADER:
                    begin
                      if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '{') then
                      begin
                        Struct := AddNewStruct(Struct);
                        Struct^.CurrentStruct := _NAMESPACE;
                      end
                      else if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '}') then
                      begin
                        DeleteStruct(Struct);
                      end;
                    end;
                  _NAMESPACE:
                    begin
                      if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '{') then
                      begin
                        Struct := AddNewStruct(Struct);
                        Struct^.CurrentStruct := _CLASS;
                      end
                      else if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '}') then
                      begin
                        Struct := DeleteStruct(Struct);
                        Struct^.CurrentStruct := _HEADER;
                      end;
                    end;
                  _CLASS:
                    begin
                      if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '{') then
                      begin
                        Struct := AddNewStruct(Struct);
                        Struct^.CurrentStruct := _METHOD;
                      end
                      else if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '}') then
                      begin
                        Struct := DeleteStruct(Struct);
                        Struct^.CurrentStruct := _NAMESPACE;
                      end;
                    end;
                  _METHOD:
                    begin
                      if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '{') then
                      begin
                        Struct := AddNewStruct(Struct);
                        Struct^.CurrentStruct := _COMPOUND_OPERATOR;
                      end
                      else if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '}') then
                      begin
                        Struct := DeleteStruct(Struct);
                        Struct^.CurrentStruct := _CLASS;
                      end;
                    end;
                  _COMPOUND_OPERATOR:
                    begin
                      if (ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '{') then
                      begin
                        Struct := AddNewStruct(Struct);
                        Struct^.CurrentStruct := _COMPOUND_OPERATOR;
                      end
                      else if ((ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '}') and (Struct^.Prev^.CurrentStruct <> _COMPOUND_OPERATOR)) then
                      begin
                        Struct := DeleteStruct(Struct);
                        Struct^.CurrentStruct := _METHOD;
                      end
                      else if ((ArrayLinesOfCode[LinesCounter][SymbolsCounter] = '}') and (Struct^.Prev^.CurrentStruct = _COMPOUND_OPERATOR)) then
                      begin
                        Struct := DeleteStruct(Struct);
                        Struct^.CurrentStruct := _COMPOUND_OPERATOR;
                      end;
                    end;
                end;
                CodeLine := CodeLine + ArrayLinesOfCode[LinesCounter][SymbolsCounter];
                Inc(SymbolsCounter);
              end;
            end;
        end;
      end
      else
        SymbolsCounter := (Length(ArrayLinesOfCode[LinesCounter]) + 1);
    end;

    if (Struct^.CurrentStruct = _NAMESPACE) then
    begin
      Inc(ClassesCounter);
      ArrayOfClasses[ClassesCounter].ClassName := FindClassName(Trim(CodeLine));
      if (ArrayOfClasses[ClassesCounter].ClassName <> '') then
      begin
        ClassLinesCounter := 1;
        MethodListCounter := 1;
        ArrayOfClasses[ClassesCounter].ArrayMethods[1] := IntToStr(0);
        GlobalVariablesCounter := 1;
        ArrayOfClasses[ClassesCounter].ArrayGlobalVariables[1] := IntToStr(0);
      end
      else
        Dec(ClassesCounter);
    end;

    if (Struct^.CurrentStruct = _CLASS) then
    begin
      Inc(MethodsCounter);
      ArrayOfMethods[MethodsCounter].MethodName := FindMethodName(CodeLine);
      if (ArrayOfMethods[MethodsCounter].MethodName <> '') then
      begin
        Inc(MethodListCounter);
        FindFormalParameters(ArrayOfMethods[MethodsCounter], CodeLine);
        ArrayOfClasses[ClassesCounter].ArrayMethods[1] := IntToStr(MethodListCounter);
        MethodLinesCounter := 1;
        ArrayOfClasses[ClassesCounter].ClassText[1] := IntToStr(MethodLinesCounter - 1);
        ArrayOfClasses[ClassesCounter].ArrayMethods[MethodListCounter] := ArrayOfMethods[MethodsCounter].MethodName;
      end
      else
      begin
        Dec(MethodsCounter);
        Inc(ClassLinesCounter);

        ArrayOfClasses[ClassesCounter].ClassText[ClassLinesCounter] := CodeLine;
        ArrayOfClasses[ClassesCounter].ClassText[1] := IntToStr(ClassLinesCounter);

        GlobalVariablesInLineNumber := 0;
        GlobalVariablesInLineCounter := 1;
        FindGlobalVariablesInLine(ArrayGlobalVariablesInLine, GlobalVariablesInLineNumber, CodeLine);
        for GlobalVariablesCounter := GlobalVariablesCounter to (GlobalVariablesCounter + GlobalVariablesInLineNumber - 1) do
        begin
          ArrayOfClasses[ClassesCounter].ArrayGlobalVariables[GlobalVariablesCounter + 1] := ArrayGlobalVariablesInLine[GlobalVariablesInLineCounter];
          Inc(GlobalVariablesInLineCounter);
        end;
        ArrayOfClasses[ClassesCounter].ArrayGlobalVariables[1] := IntToStr(GlobalVariablesCounter);
      end;
    end;

    if ((Struct^.CurrentStruct = _METHOD) or (Struct^.CurrentStruct = _COMPOUND_OPERATOR)) then
    begin
      Inc(MethodLinesCounter);
      FindLocalVariablesInMethod(ArrayOfMethods[MethodsCounter], CodeLine);
      ArrayOfMethods[MethodsCounter].MethodText[MethodLinesCounter] := CodeLine;
      ArrayOfMethods[MethodsCounter].MethodText[1] := IntToStr(MethodLinesCounter);
    end;
  end;
end;

function ReadFromFile(): Integer;
var
  TempArrayFile: array[0..970] of string;
  CurrentLine: Integer;
  FileLinesCounter: Integer;
begin
  Assignfile(AnalyzedFile, FileAddress);
  Reset(AnalyzedFile);
  FileLinesCounter := 0;
  while not EOf(AnalyzedFile) do
  begin
    ReadLn(AnalyzedFile, TempArrayFile[FileLinesCounter]);
    Inc(FileLinesCounter);
  end;
  CloseFile(AnalyzedFile);
  SetLength(ArrayLinesOfCode, FileLinesCounter + 1);
  CurrentLine := 0;
  while (CurrentLine <= FileLinesCounter) do
  begin
    ArrayLinesOfCode[CurrentLine] := TempArrayFile[CurrentLine];
    inc(CurrentLine);
  end;
  Result := CurrentLine;
end;

function InitializeArrayOfGlobalVariables(const ClassesCounter: Integer): Integer;
var
  CurrentClass, CurretGlobalVariableInClass, CounterGlobalVariables: Integer;
begin
  CounterGlobalVariables := 0;
  for CurrentClass := 1 to ClassesCounter do
  begin
    for CurretGlobalVariableInClass := 2 to StrToInt(ArrayOfClasses[CurrentClass].ArrayGlobalVariables[1]) do
    begin
      inc(CounterGlobalVariables);
      ArrayOfGlobalVariables[CounterGlobalVariables].GlobalVariableName := ArrayOfClasses[CurrentClass].ArrayGlobalVariables[CurretGlobalVariableInClass];
    end;
  end;
  Result := CounterGlobalVariables;
end;

procedure AnalyzeMethodsOnGlobalVariables(const MethodsNumber: Integer; const ClassesNumber: Integer);
const
  Keyword_This = 'this.';
  LengthKeyword_This = 5;
  PreviousSymbols: set of Char = [' ', '{', '.', '(', ','];
  NextSymbols: set of Char= [' ' , '}', '.' , ')' , ',' , ';' , '=' ,  #10];
var
  CurrentLine, CurrentClass, CurrentMethod, CurrentLocalVariable, CurrentGlobalVariable, CurretGlobalVariableInClass: Integer;
  IgnoredLocalVariable, BufferString, PossibleKeyword: string;
  VariablePosition: Integer;
  BooleanPrintedLine, BooleanPrintedMethod, BooleanActualReference: Boolean;
begin
  for CurrentGlobalVariable := 1 to GlobalVariablesTotalNumber do
  begin
    for CurrentClass := 1 to ClassesNumber do
    begin
      for CurretGlobalVariableInClass := 2 to StrToInt(ArrayOfClasses[CurrentClass].ArrayGlobalVariables[1]) do
      begin
        if (ArrayOfClasses[CurrentClass].ArrayGlobalVariables[CurretGlobalVariableInClass] = ArrayOfGlobalVariables[CurrentGlobalVariable].GlobalVariableName) then
        begin
          Writeln('Global variable -/', ArrayOfGlobalVariables[CurrentGlobalVariable].GlobalVariableName, '/- was declared in class -*', ArrayOfClasses[CurrentClass].ClassName, '*-');
        end;
      end;
    end;
    ArrayOfGlobalVariables[CurrentGlobalVariable].ActualVariableReferences := 0;
    Writeln('      We appealed to ', ArrayOfGlobalVariables[CurrentGlobalVariable].GlobalVariableName, ' in these methods:');
    BooleanPrintedMethod := false;
    for CurrentMethod := 1 to MethodsNumber do
    begin
      IgnoredLocalVariable := '';
      for CurrentLocalVariable := 2 to StrToInt(ArrayOfMethods[CurrentMethod].ArrayVariables[1]) do
      begin
        if (ArrayOfGlobalVariables[CurrentGlobalVariable].GlobalVariableName = ArrayOfMethods[CurrentMethod].ArrayVariables[CurrentLocalVariable]) then
        begin
          IgnoredLocalVariable := ArrayOfMethods[CurrentMethod].ArrayVariables[CurrentLocalVariable];
        end;
      end;
      for CurrentLine := 2 to StrToInt(ArrayOfMethods[CurrentMethod].MethodText[1]) do
      begin
        BufferString := ArrayOfMethods[CurrentMethod].MethodText[CurrentLine];
        BooleanPrintedLine := false;
        VariablePosition := AnsiPos(ArrayOfGlobalVariables[CurrentGlobalVariable].GlobalVariableName, BufferString);
        while (VariablePosition <> 0) do
        begin
          BooleanActualReference:= false;
          if (((VariablePosition = 1) or (BufferString[VariablePosition - 1] in PreviousSymbols)) and ((BufferString[VariablePosition + Length(ArrayOfGlobalVariables[CurrentGlobalVariable].GlobalVariableName)] in NextSymbols))) then
          begin
            if ArrayOfGlobalVariables[CurrentGlobalVariable].GlobalVariableName <> IgnoredLocalVariable then
            begin
              Inc(ArrayOfGlobalVariables[CurrentGlobalVariable].ActualVariableReferences);
              BooleanActualReference:= true;
            end
            else
            begin
              if (VariablePosition >= LengthKeyword_This) then
              begin
                PossibleKeyword := Trim(Copy(BufferString, VariablePosition - LengthKeyword_This, LengthKeyword_This));
                if PossibleKeyword = Keyword_This then
                begin
                  Inc(ArrayOfGlobalVariables[CurrentGlobalVariable].ActualVariableReferences);
                  BooleanActualReference:= true;
                end;
              end;
            end;
            if BooleanPrintedMethod = false then
            begin
              Writeln('      ', ArrayOfMethods[CurrentMethod].MethodName);
              BooleanPrintedMethod := true;
            end;
            if ((BooleanPrintedLine = false) and (BooleanActualReference=true)) then
            begin
              Writeln('            ', ArrayOfMethods[CurrentMethod].MethodText[CurrentLine]);
              BooleanPrintedLine := true;
            end;
          end;
          Delete(BufferString, VariablePosition, length(ArrayOfGlobalVariables[CurrentGlobalVariable].GlobalVariableName));
          VariablePosition := AnsiPos(ArrayOfGlobalVariables[CurrentGlobalVariable].GlobalVariableName, BufferString);
        end;
      end;
      BooleanPrintedMethod := false;
    end;
    Writeln('      Aup=',ArrayOfGlobalVariables[CurrentGlobalVariable].ActualVariableReferences,' Pup=',MethodsNumber);
    Writeln('      Aup/Pup=', (ArrayOfGlobalVariables[CurrentGlobalVariable].ActualVariableReferences / MethodsNumber):0:6);
    Writeln('****************************************************************************************************************************************');
  end;
end;

begin
  SizeOfArrayLinesOfCode := ReadFromFile();
  DivideCodeIntoMethodsAndClasses(SizeOfArrayLinesOfCode);
  GlobalVariablesTotalNumber := InitializeArrayOfGlobalVariables(ClassesCounter);
  AnalyzeMethodsOnGlobalVariables(MethodsCounter, ClassesCounter);

  Readln;
end.
