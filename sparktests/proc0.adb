
   

procedure Proc0(ARG: in out Integer) is
   M: Integer := 29;

   procedure P1 is
   begin
      M := M + 1;
   end;
begin
   P1;
   ARG := M;
end;

