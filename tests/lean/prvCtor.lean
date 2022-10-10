import Lean

private def a := 10

#check a

structure Name (x : String) where
  private mk ::
  val : String := x
  deriving Repr

def n1 : Name "hello" := {}

def n2 : Name "hello" := ⟨"hello"⟩

def n3 : Name "hello" := Name.mk "hello"

open Lean in
#eval id (α := CoreM Unit) do modifyEnv fun env => { env with header.mainModule := `foo } -- change module name to test `private`

#check a -- Error

def m1 : Name "hello" := {} -- Error

def m2 : Name "hello" := ⟨"hello"⟩ -- Error

def m3 : Name "hello" := Name.mk "hello"
