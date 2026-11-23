import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Objects

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def levW (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) : Subgroup (GL (Fin (Wc D i).rank) (EAf D)) :=
  lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i P)

def levK (i : Fin D.R.m) : Subgroup (GL (Fin (Wc D i).rank) (EAf D)) := levW R i R.triv

abbrev Cls (i : Fin D.R.m) : Type := Cl D.sp.cm (Wc D i).gram (levK R i)

def clsOf (i : Fin D.R.m) (x : UA D.sp.cm (Wc D i).gram) : Cls R i := Quotient.mk'' x

def levB (b : Bool) : LevelP R.Pg D.R.r ℂ := R.levL F b (sg0 D A)

def dimRho (i : Fin D.R.m) : ℕ := ∏ ρ, Module.finrank ℂ ((R.MW i (sg0 D A)).H ρ)

def dK (i : Fin D.R.m) : ℕ := Module.finrank ℂ (R.Wall i (sg0 D A))

def allAt (b : Bool) (i : Fin D.R.m) : Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (levB R F b))) (levChi _ (R.βW i) (R.datWp i (levB R F b)))

def d0 (b : Bool) (i : Fin D.R.m) : ℕ := Module.finrank ℂ (allAt R F b i)

def dGood (b : Bool) (i : Fin D.R.m) : ℕ := Module.finrank ℂ (R.Wat i (sg0 D A) (levB R F b))

def repB (b : Bool) (i : Fin D.R.m) : Representation ℂ (F.lvl b).P (R.HW i (sg0 D A)).H :=
  (R.gW i (sg0 D A)).comp (F.lvl b).P.subtype

def PrincipalCount (i : Fin D.R.m) : Prop :=
  Finite (Cls R i) ∧ Nonempty (Cls R i) ∧ (∀ c : Cls R i, Gam c = ⊥) ∧
    (∀ ρ, FiniteDimensional ℂ ((R.MW i (sg0 D A)).H ρ)) ∧ 1 ≤ dimRho R i ∧
    FiniteDimensional ℂ (R.Wall i (sg0 D A)) ∧ dK R i = Nat.card (Cls R i) * dimRho R i ∧ 1 ≤ dK R i

def ActsFreely (b : Bool) (i : Fin D.R.m) : Prop :=
  (∀ u ∈ (levB R F b).H, ∃ κ ∈ levW R i (levB R F b), rTup (R.βW i) (R.datWp i (levB R F b)) κ = u) ∧
    ∀ x κ : UA D.sp.cm (Wc D i).gram, (κ : GL (Fin (Wc D i).rank) (EAf D)) ∈ levW R i (levB R F b) →
      clsOf R i (x * κ) = clsOf R i x → rTup (R.βW i) (R.datWp i (levB R F b)) (κ : GL (Fin (Wc D i).rank) (EAf D)) = 1

def FreeCount (b : Bool) (i : Fin D.R.m) : Prop :=
  (∃ N : ℕ, Nat.card (F.lvl b).P * N = dK R i ∧
      Nonempty ((repB R F b i).asModule ≃ₗ[MonoidAlgebra ℂ (F.lvl b).P] (Fin N → MonoidAlgebra ℂ (F.lvl b).P))) ∧
    Nat.card (F.lvl b).P * d0 R F b i = dK R i ∧ 1 ≤ d0 R F b i

def GoodShare (δ : ℝ) (b : Bool) (i : Fin D.R.m) : Prop :=
  (1 - δ) * (d0 R F b i : ℝ) ≤ (dGood R F b i : ℝ) ∧ 0 < (1 - δ) * (d0 R F b i : ℝ)

structure HidaSetting : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F

theorem GoodShare.ne_bot {δ : ℝ} {b : Bool} {i : Fin D.R.m} (h : GoodShare R F δ b i) :
    R.Wat i (sg0 D A) (levB R F b) ≠ ⊥ := by
  intro h0
  have h1 : (0 : ℝ) < dGood R F b i := lt_of_lt_of_le h.2 h.1
  unfold dGood at h1
  rw [h0, finrank_bot] at h1
  simp at h1

end Objects

theorem exists_last (D : D7) : ∃ i : Fin D.R.m, (i : ℕ) + 1 = D.R.m :=
  ⟨⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩, by have := D.R.two_le_m; show D.R.m - 1 + 1 = _; omega⟩

def DefiniteFree : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), HidaSetting R F → ∀ i : Fin D.R.m, (i : ℕ) + 1 = D.R.m →
    PrincipalCount R i ∧ ∀ b : Bool, ActsFreely R F b i ∧ FreeCount R F b i

def DefiniteGoodShare : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x₀ ≤ L.sc.x →
    Formalism.MainNotions.SizesAt L → GlobalTheory.GLq.ESerTie D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
      (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
      (R : RealDat D A Ks) (F : Face D A), HidaSetting R F → ∀ i : Fin D.R.m, (i : ℕ) + 1 = D.R.m →
      ∀ b : Bool, GoodShare R F (Real.exp (-(L.sc.x ^ (L.sc.ez / 7)))) b i

def GoodVectorsDefinite : Prop := DefiniteFree ∧ DefiniteGoodShare

end GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification

end
