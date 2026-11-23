import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

noncomputable section

open NumberField TensorProduct

namespace Formalism.IndefR.NX.Core

variable (C : RatCore) {Pl : Type}

def HeckeStab (j : ℕ) (hL : ℕ → Pl → Module.End C.L0 (C.WL j)) : Prop :=
  ∀ k P (x : C.WL j), x ∈ (C.A j).WK → hL k P x ∈ (C.A j).WK

def HeckeRatAt (j : ℕ) (hL : ℕ → Pl → Module.End C.L0 (C.WL j)) (σ0 : C.L0 →+* ℂ)
    (hC : ℕ → Pl → Module.End ℂ (C.W j σ0)) : Prop :=
  ∀ k P (x : C.WL j), (C.A j).j σ0 (hL k P x) = hC k P ((C.A j).j σ0 x)

def hkK (j : ℕ) (hL : ℕ → Pl → Module.End C.L0 (C.WL j)) (hs : HeckeStab C j hL) (k : ℕ) (P : Pl) :
    Module.End C.Ks (FmK C j) :=
  ((hL k P).restrictScalars C.Ks).restrict (p := (C.A j).WK) (q := (C.A j).WK) fun x hx => hs k P x hx

def hkF (i : C.Tw) (j : ℕ) (b : Bool) (hL : ℕ → Pl → Module.End C.L0 (C.WL j)) (hs : HeckeStab C j hL)
    (k : ℕ) (P : Pl) : Module.End (FractionRing (C.O i)) (Fm C i j b) :=
  (Module.End.baseChangeHom C.Ks (KB C i b) (FmK C j) (hkK C j hL hs k P) :
    Module.End (KB C i b) (KB C i b ⊗[C.Ks] FmK C j))

end Formalism.IndefR.NX.Core
