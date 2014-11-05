with Ada.Text_IO;
with Ada.Integer_Text_IO;
use Ada.Text_IO;
use Ada.Integer_Text_IO;

procedure proc3 (X1: in out Integer) is
  X2:  Integer := 3;

  procedure L (Y1: in Integer) is
    Y2 : Integer := X1;
  begin
      X2 := Y1+X2;
      if X2 < 7 then L(Y1); end if;
      end;

begin
   L(X2);
   --Put(X2);
   X1 := X2;
end;

