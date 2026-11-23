import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherFaceStatementsIndependentOfError
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFacePrim
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsBaseLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3

section Gen

theorem majAt_eq_zero_of_self {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {x : V}
    (h : Formalism.HermitianLatticesTheory.majAt b X v x x = 0) (y : V) : Formalism.HermitianLatticesTheory.majAt b X v x y = 0 := by
  unfold Formalism.HermitianLatticesTheory.majAt at h ⊢
  have hz : ∀ i, Formalism.HermitianLatticesTheory.fcoord b X v x i = 0 := by
    have h1 : ∀ i, star (Formalism.HermitianLatticesTheory.fcoord b X v x i) * Formalism.HermitianLatticesTheory.fcoord b X v x i =
        ((Complex.normSq (Formalism.HermitianLatticesTheory.fcoord b X v x i) : ℝ) : ℂ) := fun i => by
      rw [mul_comm]; exact Complex.mul_conj _
    simp only [h1] at h
    have h2 : ∑ i, Complex.normSq (Formalism.HermitianLatticesTheory.fcoord b X v x i) = 0 := by exact_mod_cast h
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 h2 i (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  simp [hz]

theorem partPr_of_bot {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Df : DefSide Bs) (t : Bs.Tup) (p : Bs.Ix)
    (h : Df.Qp t p = ⊥) : partPr Df t p = 0 := by
  unfold partPr
  split_ifs with hc
  · have hz : ∀ z ∈ Df.Qp t p, z = 0 := fun z hz => by
      rw [h] at hz
      exact (Submodule.mem_bot K).1 hz
    ext i j
    rw [LinearMap.toMatrix'_apply, LinearMap.comp_apply, Submodule.subtype_apply, hz _ (Submodule.coe_mem _)]
    rfl
  · rfl

theorem rowXE_congr {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Df : DefSide Bs)
    (Y : Matrix (Fin (Df.dQ Bs.μ0)) (Fin (Df.dQ Bs.μ0)) ℂ) (κ : InfinitePlace K → ℝ) (lam lam' : Bs.J → Bs.Ix → InfinitePlace K → ℝ)
    (h : ∀ p, partPr Df Bs.μ0 p ≠ 0 → ∀ j v, lam j p v = lam' j p v) : rowXE Df Y κ lam = rowXE Df Y κ lam' := by
  have hw : weightMet (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0) =
      weightMet (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam' j p v) (Df.XQ Bs.μ0) := by
    funext v
    unfold weightMet
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : partPr Df Bs.μ0 p = 0
    · rw [hp]
      simp [restrMetC]
    · simp only [h p hp]
  unfold rowXE rowFrame weightFrame
  rw [hw]

end Gen

section GenCx2
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs}

theorem cx_XE_scal (Y : CxData A) (cr : Crd A fc) (lam : type_of% Y.lam) (b : Bool)
    (h : ∀ p, partPr (lv (fc Y.zs) b) Bs.μ0 p ≠ 0 → ∀ j v, lam j Bs.μ0 p v = Y.lam j Bs.μ0 p v) :
    ((reScal Y Y.κ lam).data cr b).XE = (Y.data cr b).XE :=
  rowXE_congr _ _ _ _ _ h

theorem cx_galD_scal (Y : CxData A) (cr : Crd A fc) (κ : InfinitePlace K → ℝ) (lam : type_of% Y.lam)
    (hlam : ∀ j p v, v ≠ Bs.v0 → (∃ x, Y.tC cr false j Bs.μ0 (cpt Bs.v0.embedding x) ∈ Y.Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x ≠ 0) → lam j Bs.μ0 p v = Y.lam j Bs.μ0 p v)
    (h : Y.GalD cr false) : (reScal Y κ lam).GalD cr false := by
  intro j v hv p x hx y
  have h0 := h j v hv p x hx y
  refine h0.trans ?_
  show _ = ((lam j Bs.μ0 p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x y
  by_cases hp : ∃ x, Y.tC cr false j Bs.μ0 (cpt Bs.v0.embedding x) ∈ Y.Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x ≠ 0
  · rw [hlam j p v hv hp]
  · have hxx : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x = 0 := by
      by_contra hne
      exact hp ⟨x, hx, hne⟩
    rw [majAt_eq_zero_of_self _ _ v hxx y, mul_zero, mul_zero]

end GenCx2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) : type_of% R.lam3 :=
  fun i t p v => if (v = A3.A.v0 ∧ R.Wp3 i p = ⊥) ∨ (v ≠ A3.A.v0 ∧ ¬ R.PartAt F i p v) then Real.exp (c i) else R.lam3 i t p v

theorem zeroLam_of_ne (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (h1 : R.Wp3 i p ≠ ⊥) (h2 : v ≠ A3.A.v0 → R.PartAt F i p v) : zeroLam R F c i t p v = R.lam3 i t p v := by
  unfold zeroLam
  rw [if_neg]
  rintro (⟨_, h⟩ | ⟨hv, h⟩)
  · exact h1 h
  · exact h (h2 hv)

theorem scalarsZeroPartConvention_fixedPlace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p}
    (h1 : R.Wp3 i p ≠ ⊥) : zeroLam R F c i t p A3.A.v0 = R.lam3 i t p A3.A.v0 :=
  zeroLam_of_ne R F c h1 fun h => absurd rfl h

theorem zeroLam_off (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (hv : v ≠ A3.A.v0) (h2 : R.PartAt F i p v) : zeroLam R F c i t p v = R.lam3 i t p v := by
  unfold zeroLam
  rw [if_neg]
  rintro (⟨h, _⟩ | ⟨_, h⟩)
  · exact hv h
  · exact h h2

theorem zeroLam_of_zero (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (h : (v = A3.A.v0 ∧ R.Wp3 i p = ⊥) ∨ (v ≠ A3.A.v0 ∧ ¬ R.PartAt F i p v)) : zeroLam R F c i t p v = Real.exp (c i) := by
  unfold zeroLam
  rw [if_pos h]

theorem zeroLam_pos (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (h : ∀ i t p v, 0 < R.lam3 i t p v) (i t p v) :
    0 < zeroLam R F c i t p v := by
  unfold zeroLam
  split_ifs
  · exact Real.exp_pos _
  · exact h i t p v

set_option maxHeartbeats 4000000 in

theorem qp_bot (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) (hOk : A3.fam3.Ok3 1)
    (hsep : A3.fam3.TypesSep3) {p : A3.fam3.base3.Ix} (hp : R.EEp3 p = ⊥) (b : Bool) :
    (lv (F.fc (R.toCx3 F).zs) b).Qp A3.fam3.base3.μ0 p = ⊥ := by
  have kR := RealDat3.kFormR_of (F := F) hC.base.models
  have hst := (subspaces_stable_in_block (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP)).1
  have hH := hP.hecke.1.choose_spec
  have key : ∀ ℓ y, y ∈ (A3.fam3.RI A3.fam3.F.μ0).part3 ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) p.1 → y = 0 := by
    intro ℓ y hy
    have h1 := (part_iff_rows3 kR hst hOk hH p ℓ y).1 hy
    have h2 : (R.toCx3 F).Θ A3.fam3.F.μ0 ((R.toCx3 F).jR A3.fam3.F.μ0
        ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) y)) = 0 := by
      have h3 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).Θ A3.fam3.F.μ0 ((R.toCx3 F).jR A3.fam3.F.μ0
          ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) y))) ∈ R.EEp3 p := h1
      rw [hp] at h3
      have h5 := (Submodule.mem_bot ℂ).1 h3
      exact h5
    have h4 := CxData.theta_jR_inj (R.toCx3 F) kR _ _ (coordinates_mem_subspace ℓ _ y) h2
    exact BlockDat.toF_injective _ ℓ _ (h4.trans (map_zero _).symm)
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  cases b
  · exact key _ y hy
  · exact key _ y hy

end GlobalTheory.Mem.R3

end
