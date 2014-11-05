

procedure proc4 (ARG2: in out Integer) is
   procedure P1 (ARG: in out Integer) is
   begin
      ARG := ARG-1;
      P1(ARG);
   end;
begin
   P1(ARG2);
end;
