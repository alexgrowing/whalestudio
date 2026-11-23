import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance factPrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev PlOver (k : Fin 2) : Type := {PP : R.Pg // R.C.P.Div k PP.1}

abbrev Labels (D : D7) : Type := ∀ k : Fin 2, GlobalTheory.GLq.LabelDatum (D.host.g k)

abbrev ResIso : Type := ∀ (k : Fin 2) (PP : PlOver R k), ZMod (D.host.g k) ≃+* kP PP.1.1

abbrev TameLab : Type := ∀ k : Fin 2, PlOver R k → Fin D.R.m → (ZMod (D.host.g k))ˣ

abbrev Tuple : Type := ∀ k : Fin 2, PlOver R k → GlobalTheory.GLq.Gn (D.host.g k) D.R.r → ℂ

def IsTameLab (Lb : Labels D) (iso : ResIso R) (c : TameLab R) : Prop :=
  ∀ (k : Fin 2) (PP : PlOver R k) (j : Fin D.R.m) (u : (ZMod (D.host.g k))ˣ) (u' : (kP PP.1.1)ˣ),
    (u' : kP PP.1.1) = iso k PP (u : ZMod (D.host.g k)) →
      ((R.chi ((j : ℕ) + 1) PP.1.1 u' : ℂˣ) : ℂ) =
        GlobalTheory.GLq.thetaOf (Lb k) 1
          (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (c k PP j : ZMod (D.host.g k)))
          (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))

def IsGoodTuple (Lb : Labels D) (c : TameLab R) (τ : Tuple R) : Prop :=
  ∀ k : Fin 2, ∃ f : PlOver R k → (ZMod (D.host.g k))[X],
    (∀ PP, GlobalTheory.GLq.IsIrr (τ k PP) ∧ GlobalTheory.GLq.HasLabel (Lb k) (τ k PP) (f PP)) ∧
      Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) f (c k) ∧ Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) f fun PP j => (c k PP j)⁻¹

def IsCharOf (iso : ResIso R) (χ : G → D.what₂.LL) (τ : Tuple R) : Prop :=
  ∀ g : G, D.what₂.embLL (χ g) = ∏ k : Fin 2, ∏ᶠ PP : PlOver R k,
    τ k PP (Formalism.UG.bc ((iso k PP).symm : kP PP.1.1 →+* ZMod (D.host.g k)) (R.eG g PP.1))

def GoodTypes : Prop :=
  ∃ (Lb : Labels D) (iso : ResIso R) (c : TameLab R), IsTameLab R Lb iso c ∧
    (∀ χ ∈ A.X, ∃ τ, IsGoodTuple R Lb c τ ∧ IsCharOf R iso χ τ) ∧
    ∀ τ, IsGoodTuple R Lb c τ → ∃ χ ∈ A.X, IsCharOf R iso χ τ

def V0C : Submodule ℂ (R.HX A.μ0).H :=
  Submodule.span ℂ (R.jX A.μ0 '' ((A.fam.R A.μ0).goodF A.X : Set (A.fam.amb.FR A.μ0)))

def UC : Submodule ℂ (R.HX A.μ0).H := V0C R ⊓ LinearMap.ker (R.Th A.μ0)

def KerRational : Prop :=
  Submodule.span ℂ (R.jX A.μ0 '' {x | R.jX A.μ0 x ∈ UC R}) = UC R

def dimRows (b : Bool) : ℕ := Module.finrank ℂ ((R.EEat (R.levR F b)).comap R.HE.e)

def dimQ (b : Bool) : ℕ := (lv (F.fc (R.toCx F).zs) b).dQ A.μ0

theorem dimQ_eq (b : Bool) :
    dimQ R F b = Module.finrank D.what₂.LL ((A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0)) := by
  cases b <;> rfl

theorem pos_iff (b : Bool) : (lv (F.fc (R.toCx F).zs) b).Pos ↔ 0 < dimQ R F b := Iff.rfl

theorem pos_iff_ne_bot (b : Bool) :
    (lv (F.fc (R.toCx F).zs) b).Pos ↔ (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ := by
  rw [pos_iff, dimQ_eq, pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]

def HidaSetting : Prop :=
  R.toLevCh.Is A.μ0 ∧ R.IsGrp F ∧ R.IsFam ∧ R.IsModels ∧ R.IsChain ∧ R.IsThP ∧ R.IsScal F ∧ GoodTypes R

end

def AtScale (eps x0 : ℝ) (D : D7) : Prop :=
  ∃ L : SizeData₂ D, L.sc.eps = eps ∧ x0 ≤ L.sc.x ∧ Nonempty (ParameterChoice' D L) ∧ Formalism.MainNotions.SizesAt L

def AtLargeScale (P : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL], RealDat D A Ks → Face D A → Prop) : Prop :=
  ∀ eps : ℝ, ∃ x0 : ℝ, ∀ D : D7, AtScale eps x0 D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
      HidaSetting R F → P D G Pl0 T A Ks R F

def RowsPos : Prop := AtLargeScale fun _ _ _ _ _ _ _ _ _ _ _ R F => ∀ b, 0 < dimRows R F b

def DimQEq : Prop := AtLargeScale fun _ _ _ _ _ _ _ _ _ _ _ R F => KerRational R → ∀ b, dimQ R F b = dimRows R F b

def QPos : Prop :=
  AtLargeScale fun _ _ _ _ _ _ _ _ _ _ _ R F => KerRational R → ∀ b, (lv (F.fc (R.toCx F).zs) b).Pos

theorem AtScale.mono {eps x0 x1 : ℝ} {D : D7} (h : AtScale eps x1 D) (hx : x0 ≤ x1) : AtScale eps x0 D :=
  let ⟨L, h1, h2, h3⟩ := h
  ⟨L, h1, hx.trans h2, h3⟩

theorem qPos_of (h1 : RowsPos) (h2 : DimQEq) : QPos := by
  intro eps
  obtain ⟨x1, h1⟩ := h1 eps
  obtain ⟨x2, h2⟩ := h2 eps
  refine ⟨max x1 x2, fun D hD G _ _ Pl0 T A Ks _ _ _ R F hS hK b => ?_⟩
  rw [pos_iff, h2 D (hD.mono (le_max_right _ _)) G Pl0 T A Ks R F hS hK b]
  exact h1 D (hD.mono (le_max_left _ _)) G Pl0 T A Ks R F hS b

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

end
