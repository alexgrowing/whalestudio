import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

namespace GlobalTheory.NewPrime

section General

def rect {Λ B : Type} [CommRing Λ] [AddCommGroup B] [Module Λ B] {r a : ℕ} (Z : Matrix (Fin r) (Fin a) Λ) (x : Fin a → B) :
    Fin r → B := fun c => ∑ j, Z c j • x j

abbrev what₂ {Λ μ ν : Type} [CommRing Λ] (Z : μ → ν → Λ) : Submodule Λ (ν → Λ) := Submodule.span Λ (Set.range Z)

def Cob {Γ Λ M : Type} [Group Γ] [CommRing Λ] [AddCommGroup M] [Module Λ M] (ρ : Representation Λ Γ M) (f : Γ → M) : Prop :=
  ∃ m, ∀ g, f g = ρ g m - m

variable (Λ : Type) [CommRing Λ] {Y Y' : Type} [AddCommGroup Y] [Module Λ Y] [AddCommGroup Y'] [Module Λ Y'] {n : ℕ}

def Bal (β : Y →+ Y' →+ ZMod n) : Prop := ∀ (a : Λ) y y', β (a • y) y' = β y (a • y')

def Perf (β : Y →+ Y' →+ ZMod n) : Prop :=
  Bal Λ β ∧ (∀ y, (∀ y', β y y' = 0) → y = 0) ∧ ∀ y', (∀ y, β y y' = 0) → y' = 0

def vecPair (r : ℕ) (β : Y →+ Y' →+ ZMod n) : (Fin r → Y) →+ (Fin r → Y') →+ ZMod n :=
  ∑ c : Fin r, ((β.comp (Pi.evalAddMonoidHom (fun _ => Y) c)).flip.comp (Pi.evalAddMonoidHom (fun _ => Y') c)).flip

theorem vecPair_apply (r : ℕ) (β : Y →+ Y' →+ ZMod n) (x : Fin r → Y) (y : Fin r → Y') :
    vecPair r β x y = ∑ c, β (x c) (y c) := by
  simp [vecPair, AddMonoidHom.finset_sum_apply]

def CupB {Γ M M' : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [AddCommGroup M'] (χ : Γ → ZMod n)
    (act : Γ → M' → M') (P : M →+ M' →+ ZMod n) (x : Γ → M) (y : Γ → M') : Prop :=
  ∃ f : Γ → ZMod n, IsLocallyConstant f ∧ ∀ g h, P (x g) (act g (y h)) = χ g * f h - f (g * h) + f g

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

def Kills (A : Type) [CommRing A] [Algebra (X.O0 i) A] : Prop := ∀ x ∈ idl i, algebraMap (X.O0 i) A x = 0

section Coef

variable {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)

def SelC (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] (Q : Finset (PlE D.host))
    (f : GE N → Fin D.R.r → Y) : Prop :=
  ∃ z : Z1 (repOn (Tgl i s) κ Y), z.1 = f ∧ Submodule.Quotient.mk z ∈ selOn bkP i (Tgl i s) κ Y Q

def Univ (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) Λ) (Z : GE N → Matrix (Fin D.R.r) (Fin a) Λ) : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y],
    (∀ x : Fin a → Y, matAct Φ x = 0 → SelC bkP i s κ Y Q fun g => rect (Z g) x) ∧
    (∀ x : Fin a → Y, matAct Φ x = 0 → Cob (repOn (Tgl i s) κ Y) (fun g => rect (Z g) x) → x = 0) ∧
    ∀ f, SelC bkP i s κ Y Q f → ∃ x : Fin a → Y, matAct Φ x = 0 ∧
      Cob (repOn (Tgl i s) κ Y) fun g => f g - rect (Z g) x

variable (ρ : GE N →* GL (Fin D.R.r) (X.O0 i))

section Dual

variable {Y Y' : Type} [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y]
  [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1)))
  (Q : Finset (PlE D.host))

def DualSel (y : Z1 (repOn ρ κ⁻¹ Y')) : Prop :=
  (∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 v), y.1 τ = 0) ∧
  (∀ v, v ∈ Spl i ∨ v ∈ Q → ∃ m, ∀ g ∈ DecV N v, y.1 g = repOn ρ κ⁻¹ Y' g m - m) ∧
  ∀ v ∈ placesOver D.host.E (X.l i), ∀ x : Z1 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype),
    Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) κ Y v →
    CupB (fun g : DecV N v => ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g.1 : (ZMod (X.l i ^ (nu X i + 1)))ˣ) :
        ZMod (X.l i ^ (nu X i + 1))))
      (fun g m => repOn ρ κ⁻¹ Y' g.1 m) (vecPair D.R.r β) x.1 (fun g => y.1 g.1)

def DualCl : Set (H1 (repOn ρ κ⁻¹ Y')) := {c | ∃ y, DualSel bkP i s κ ρ β Q y ∧ c = Submodule.Quotient.mk y}

end Dual

def OrderFormula (Q : Finset (PlE D.host)) : Prop :=
  ∀ (Y Y' : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] [Finite Y']
    (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Perf Λ β →
    Finite (DualCl bkP i s κ ρ β Q) ∧ Nat.card (selOn bkP i (Tgl i s) κ Y Q) =
      Nat.card (DualCl bkP i s κ ρ β Q) * ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ Y').comp (DecV N v).subtype))

def NoInvDual : Prop := ∀ (Y' : Type) [AddCommGroup Y'] [Module Λ Y'] (m : Fin D.R.r → Y'),
  (∀ g, repOn ρ κ⁻¹ Y' g m = m) → m = 0

def LocCountFin : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y],
    ∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (bkOn bkP i (Tgl i s) κ Y v) =
      (∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype))) *
        Nat.card Y ^ (D.R.f * D.R.r)

omit [Algebra (X.O0 i) Λ] in

def IsChar {M : ℕ} {ι : Type} [Fintype ι] (ξ : ι → Λ) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  ∀ g, ((κ g : Λˣ) : Λ) * ∏ q, (1 + ξ q) ^ (Multiplicative.toAdd (d q g)).val = 1

def bform (x y : GE N → Fin D.R.r → Λ) (h : GE N) : Λ := x h ⬝ᵥ y h - x (cConj X h) ⬝ᵥ y (cConj X h)

end Coef

def NewPl (M : ℕ) (L : Subgroup (GE N)) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N) : Prop :=
  (∀ v, Over p v → v ∉ X.S0 i) ∧ IsSplitPl D.host p ∧ normV p % (2 * X.l i ^ M) = 1 ∧ DecV N p ≤ L ∧
    IsOpen (d.ker : Set (GE N)) ∧ IsFrob (N.plOm.1 p) (normV p) σ ∧ γ ∈ Ine (F := D.host.E) (N.plOm.1 p) ∧
    d γ = Multiplicative.ofAdd 1

variable (X) in

def two (g : GE N) : Bool → GE N := fun b => if b then cConj X g else g

end GlobalTheory.NewPrime
