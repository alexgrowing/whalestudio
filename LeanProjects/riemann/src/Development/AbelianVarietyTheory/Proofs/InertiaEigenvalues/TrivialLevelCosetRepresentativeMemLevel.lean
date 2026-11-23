import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LatIndexEqOneOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Eu

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def fid (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D :=
  if h : ∃ f, IsFinIdem D v f then h.choose else 0

def locSet (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : Set (GA D (Wc D i)) :=
  {g | g ∈ GfC (Wc D i) ∧ SuppF (Wc D i) (fid D v) g}

def LX (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type :=
  Quotient ((QuotientGroup.leftRel (levW R i)).comap (Subtype.val : locSet R i v → GA D (Wc D i)))

theorem one_mem_locSet (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (1 : GA D (Wc D i)) ∈ locSet R i v := by
  refine ⟨(GfC (Wc D i)).one_mem, ?_⟩
  have : Formalism.L2.Theta.mt (Wc D i) 1 = 1 := rfl
  intro a b
  simp [this]

def lx0 (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : LX R i v :=
  Quotient.mk _ ⟨1, one_mem_locSet R i v⟩

def rep {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) : GA D (Wc D i) :=
  (Quotient.out x).1

open Classical in

def Bop (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  if h : ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧ ∀ x y, trPair R i γ x y = ⟪x, B y⟫_ℂ then
    h.choose else 0

open Classical in

def famProd (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) : GA D (Wc D i) :=
  if h : {w | F w ≠ lx0 R i w}.Finite then (h.toFinset.toList.map fun w => rep (F w)).prod else 1

def Bfam (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  Bop R i (famProd R i F)

def acoef (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : LX R i v) : ℂ :=
  coef R i t μ 𝓕 (rep x)

def Zop (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  ∑' x : LX R i v, acoef R i t μ 𝓕 v x • Bop R i (rep x)

section Helpers
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem bop_one {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) : Eu.Bop R i 1 = 1 := by
  have h6 : ∀ x y, trPair R i 1 x y = ⟪x, y⟫_ℂ := hTL.2.2.2.2.2
  have hex : ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧
      ∀ x y, trPair R i 1 x y = ⟪x, B y⟫_ℂ :=
    ⟨1, ContinuousLinearMap.norm_id_le, fun x y => by rw [h6]; rfl⟩
  unfold Eu.Bop
  rw [dif_pos hex]
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [← hex.choose_spec.2 x y, h6]
  rfl

theorem bop_norm (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) : ‖Eu.Bop R i γ‖ ≤ 1 := by
  unfold Eu.Bop
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem trivial_level_coset_representative_mem_level (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Eu.rep (Eu.lx0 R i v) ∈ levW R i := by
  have h := Quotient.mk_out (s := (QuotientGroup.leftRel (levW R i)).comap
    (Subtype.val : Eu.locSet R i v → GA D (Wc D i))) ⟨1, Eu.one_mem_locSet R i v⟩
  rw [Setoid.comap_rel, QuotientGroup.leftRel_apply] at h
  have h2 := h
  have h3 := (levW R i).inv_mem h2
  simpa [Eu.rep, Eu.lx0] using h3

theorem local_coefficient_trivial_level_coset {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} (hLF : LevFix R i t) (hVN : VecNe R i t) {μ 𝓕}
    (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Eu.acoef R i t μ 𝓕 v (Eu.lx0 R i v) = 1 := by
  unfold Eu.acoef
  have := Model.coef_mul_lev R i t hLF μ 𝓕 1 _ (trivial_level_coset_representative_mem_level R i v)
  rw [one_mul] at this
  rw [this, Model.coef_one R i t hVN μ 𝓕 hμ]

theorem localCosetFamilyRepresentativeProd_trivial_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) : Eu.famProd R i (Eu.lx0 R i) = 1 := by
  unfold Eu.famProd
  have hf : {w | Eu.lx0 R i w ≠ Eu.lx0 R i w}.Finite := by simp
  rw [dif_pos hf]
  have : hf.toFinset = ∅ := by simp
  rw [this]
  simp

end Helpers

end GlobalTheory.RawLift.Eu

end
