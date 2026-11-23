import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelLattice
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVecOfNe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PtFieldMain
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.MetBase

open Formalism.HermitianLatticesTheory

section Polar

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fcoord_smul_emb (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x : V) : fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i; simp [vecAt, map_mul]
  simp only [fcoord, hv, Matrix.mulVec_smul]

theorem fcoord_add_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
    funext i; simp [vecAt, map_add]
  simp only [fcoord, hv, Matrix.mulVec_add]

theorem majAt_add_left_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x x' y : V) : majAt b X v (x + x') y = majAt b X v x y + majAt b X v x' y := by
  simp only [majAt, fcoord_add_of b X v x x', Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem majAt_add_right_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y y' : V) : majAt b X v x (y + y') = majAt b X v x y + majAt b X v x y' := by
  simp only [majAt, fcoord_add_of b X v y y', Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem majAt_smul_left_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : majAt b X v (a • x) y = star (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul_emb, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem majAt_smul_right_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : majAt b X v x (a • y) = v.embedding a * majAt b X v x y := by
  simp only [majAt, fcoord_smul_emb, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem majAt_self_eq (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    majAt b X v x x = (((normAt b X v x) ^ 2 : ℝ) : ℂ) := by
  unfold normAt cnorm majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem majAt_eq_of_diag {V' ι' : Type} [AddCommGroup V'] [Module K V'] [Fintype ι'] [DecidableEq ι']
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Module.Basis ι' K V')
    (X' : InfinitePlace K → Matrix ι' ι' ℂ) (v : InfinitePlace K) (e : V' →ₗ[K] V)
    (hv : ∃ a : K, star (v.embedding a) ≠ v.embedding a)
    (h : ∀ x, majAt b X v (e x) (e x) = majAt b' X' v x x) (x y : V') :
    majAt b X v (e x) (e y) = majAt b' X' v x y := by
  have hadd : ∀ x y : V', (majAt b X v (e x) (e y) - majAt b' X' v x y) +
      (majAt b X v (e y) (e x) - majAt b' X' v y x) = 0 := by
    intro x y
    have h0 := h (x + y)
    have h1 := h x
    have h2 := h y
    simp only [map_add, majAt_add_left_of, majAt_add_right_of] at h0
    linear_combination h0 - h1 - h2
  obtain ⟨a, ha⟩ := hv
  have h3 := hadd x (a • y)
  simp only [map_smul, majAt_smul_left_of, majAt_smul_right_of] at h3
  have h4 := hadd x y
  have h5 : (v.embedding a - star (v.embedding a)) * (majAt b X v (e x) (e y) - majAt b' X' v x y) = 0 := by
    linear_combination h3 - star (v.embedding a) * h4
  have h6 : v.embedding a - star (v.embedding a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_left h6)

end Polar

theorem exists_nonreal {K : Type} [Field K] (v : InfinitePlace K) (hv : v.IsComplex) :
    ∃ a : K, star (v.embedding a) ≠ v.embedding a := by
  by_contra hc
  push_neg at hc
  apply InfinitePlace.not_isReal_iff_isComplex.2 hv
  rw [InfinitePlace.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq]
  exact hc a

end GlobalTheory.Mem.R3.MetBase

namespace GlobalTheory.Mem.R3.MetBase

set_option maxHeartbeats 2000000 in

theorem metric_base_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →
    ∀ x y, Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s0Of R F).XE A3.A.v0 x y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h2 : (R.toCx3 F).H2 F.cr false := (hCx.what₂ false).1
  have hE : R.models_HE := hP.char.base.models.HE
  have hn : 0 < RealDat.nP F.lv2 false := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have hv0 : A3.A.v0 = InfinitePlace.mk D.what₂.embLL := R.hv0
  have hcx : ∃ a : D.what₂.LL, star (A3.A.v0.embedding a) ≠ A3.A.v0.embedding a := by
    haveI := (GlobalTheory.ptField_main D).1
    exact exists_nonreal _ (IsTotallyComplex.isComplex _)
  refine majAt_eq_of_diag _ _ _ _ _ Z.eRR0.toLinearMap hcx ?_
  intro x
  have hR := PrincipalLevelLattice.majorant_at_base_place_eq_inner (R.toCx3 F) F.cr false h2 hn x x

  set w := (R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding x) with hw
  set z := X0.s.jEE (Z.eRR0 x) with hz
  set u : R.HE.H := Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) w with hu
  have hjE := Z.jEE0 x
  rw [← hz] at hjE
  change _ = PiTensorProduct.lift (R.HE.e u) at hjE
  have hee := Y.tied.base.ee z z
  have hnorm := X0.s.jEE_norm (Z.eRR0 x)
  have hL : Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 x) = ⟪z, z⟫_ℂ := by
    rw [majAt_self_eq, hv0, hnorm, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hK : ⟪z, z⟫_ℂ = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, u⟫_ℂ := by
    by_cases hT : R.HE.e (u) = 0
    · have h0 : u = 0 := hE.1 (hT.trans (map_zero _).symm)
      have hz0 : Y.Iz.jE z = 0 := by
        apply Subtype.ext
        rw [hjE, hT, map_zero]
        rfl
      have hz1 : z = 0 := Y.Iz.jE.map_eq_zero_iff.1 hz0
      rw [hz1, h0]
      simp
    · obtain ⟨v, hv⟩ := GlobalTheory.KapRedII.exists_vec_of_ne hT
      rw [hee]
      show ipMT (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.ν0) R.fd0 _ _ = _
      rw [hjE, ipMT, LinearEquiv.symm_apply_apply, GlobalTheory.KapRedII.ipM_smul_of_vec _ _ _ _ _ (inv_pos.2 hn) v hv, ← hE.2.2]
  change Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 x) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XE F.cr false) A3.fam3.base3.v0 x x
  rw [hL, hK, hR]
  have hc : ∀ (s : Bool) (c : ℂ), starRingEnd ℂ c = c → Formalism.IndefR.Links.cj s c = c := by
    intro s c h
    cases s <;> simp [Formalism.IndefR.Links.cj, h]
  change _ = _ * Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) ⟪u, u⟫_ℂ
  rw [hc _ _ (inner_conj_symm u u)]
  rfl

end GlobalTheory.Mem.R3.MetBase
