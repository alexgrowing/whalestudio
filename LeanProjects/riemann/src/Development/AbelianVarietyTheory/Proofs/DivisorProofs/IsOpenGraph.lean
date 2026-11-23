import Mathlib

namespace GlobalTheory.PrimLift

variable {X : Type} [TopologicalSpace X]

def Etale (_P : Set X → (X → ℂ) → Prop) : Type := X × ℂ

instance (P : Set X → (X → ℂ) → Prop) : TopologicalSpace (Etale P) :=
  TopologicalSpace.generateFrom
    {S | ∃ O f, P O f ∧ S = (fun y => ((y, f y) : X × ℂ)) '' O}

def Etale.proj (P : Set X → (X → ℂ) → Prop) : Etale P → X := Prod.fst

def Etale.mk (P : Set X → (X → ℂ) → Prop) (y : X) (c : ℂ) : Etale P := ((y, c) : X × ℂ)

def Etale.val {P : Set X → (X → ℂ) → Prop} (e : Etale P) : ℂ := (e : X × ℂ).2

@[simp] theorem Etale.proj_mk (P : Set X → (X → ℂ) → Prop) (y : X) (c : ℂ) :
    Etale.proj P (Etale.mk P y c) = y := rfl

@[simp] theorem Etale.val_mk (P : Set X → (X → ℂ) → Prop) (y : X) (c : ℂ) :
    (Etale.mk P y c).val = c := rfl

theorem Etale.mk_proj_val {P : Set X → (X → ℂ) → Prop} (e : Etale P) :
    Etale.mk P (Etale.proj P e) e.val = e := rfl

theorem Etale.isOpen_graph {P : Set X → (X → ℂ) → Prop} {O : Set X} {f : X → ℂ} (h : P O f) :
    IsOpen ((fun y => Etale.mk P y (f y)) '' O) :=
  TopologicalSpace.GenerateOpen.basic _ ⟨O, f, h, rfl⟩

end GlobalTheory.PrimLift
