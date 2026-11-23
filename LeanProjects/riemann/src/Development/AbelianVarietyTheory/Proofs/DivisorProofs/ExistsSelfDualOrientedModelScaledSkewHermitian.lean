import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeBlockDirectSumScaled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijectiveStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SkewOverW

open Matrix GlobalTheory.SkewLat GlobalTheory.SkewLat.DualPair
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (HasSig form)
open scoped nonZeroDivisors

private theorem hasSignature_of_smul {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSig ((κ : ℂ) • M) r s) : Formalism.UG.HasSignature M r s := by
  refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
  obtain ⟨h1, A, hA⟩ := h
  refine ⟨h1, ((Real.sqrt κ : ℝ) : ℂ) • A.map star, ?_⟩
  have h2 := congrArg (fun X : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ => X.map (starRingEnd ℂ)) hA
  simp only [Matrix.map_mul] at h2
  have e2 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).map (starRingEnd ℂ) =
      Matrix.fromBlocks 1 0 0 (-1) := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply] <;> split_ifs <;> simp
  have hs : ((Real.sqrt κ : ℝ) : ℂ) * ((Real.sqrt κ : ℝ) : ℂ) = (κ : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hκ.le
  have t1 : (((Real.sqrt κ : ℝ) : ℂ) • A.map star)ᵀ = ((Real.sqrt κ : ℝ) : ℂ) • (Aᵀ).map (starRingEnd ℂ) := by
    ext i j; simp
  have t2 : (((Real.sqrt κ : ℝ) : ℂ) • A.map star).map star =
      ((Real.sqrt κ : ℝ) : ℂ) • (A.map star).map (starRingEnd ℂ) := by
    ext i j; simp
  have t3 : ((κ : ℂ) • M).map (starRingEnd ℂ) = (κ : ℂ) • M.map (starRingEnd ℂ) := by
    ext i j; simp
  rw [t3, e2] at h2
  rw [t1, t2, ← h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]

variable {D : D7}

private theorem form_smul {d : ℕ} (J : Matrix (Fin d) (Fin d) D.host.E) (c e : D.host.E) (y x : Fin d → D.host.E) :
    form D.sp.cm.sig J (c • y) (e • x) = c * star e * form D.sp.cm.sig J y x := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
  simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, hσ, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem mem_lat {d : ℕ} {L : Submodule (𝓞 D.host.E) (Fin d → D.host.E)} {y : Fin d → D.host.E} :
    y ∈ scLat D.host.AA⁻¹ L ↔ ∀ c ∈ D.host.AA, c • y ∈ L := by
  rw [mem_scLat, inv_inv]

private theorem smul_mem_lat {d : ℕ} {L : Submodule (𝓞 D.host.E) (Fin d → D.host.E)} {y : Fin d → D.host.E}
    (hy : y ∈ L) {e : D.host.E} (he : e ∈ D.host.AA⁻¹) : e • y ∈ scLat D.host.AA⁻¹ L := by
  refine mem_lat.2 fun c hc => ?_
  obtain ⟨b, hb⟩ := int_of_inv_mul he hc
  rw [smul_smul, mul_comm, ← hb]
  exact L.smul_mem b hy

private theorem mem_iff {d : ℕ} (L : Submodule (𝓞 D.host.E) (Fin d → D.host.E)) (y : Fin d → D.host.E) :
    y ∈ L ↔ y ∈ scLat D.host.AA (scLat D.host.AA⁻¹ L) := by
  refine ⟨fun hy e he => smul_mem_lat hy he, fun h => ?_⟩
  have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, u • y ∈ L := fun u hu =>
    FractionalIdeal.mul_induction_on hu (C := fun u => u • y ∈ L)
      (fun a ha e he => by rw [mul_smul]; exact mem_lat.1 (h e he) a ha)
      (fun u v hu hv => by rw [add_smul]; exact L.add_mem hu hv)
  simpa using key 1 one_mem_AA_mul

private theorem dual_iff {d : ℕ} (J : Matrix (Fin d) (Fin d) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin d → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ L, IntTr (form D.sp.cm.sig J y x)) (y : Fin d → D.host.E) :
    y ∈ scLat D.host.AA⁻¹ L ↔ ∀ x ∈ scLat D.host.AA⁻¹ L,
      ∃ b : 𝓞 D.host.E, (b : D.host.E) = D.host.xi0⁻¹ * form D.sp.cm.sig J y x := by
  have hξ : D.host.xi0 ≠ 0 := xi_ne
  have hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar := fun c h => by
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]; exact Formalism.L2.Pj.conj_mem_AAbar D h
  have hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA := fun c h => GlobalTheory.star_mem_AA_of_mem_AAbar h
  constructor
  · intro hy x hx
    have hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x) * D.host.AA * D.host.AAbar ≤
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar := by
      rw [hX, mul_assoc, FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ z ?_
      refine FractionalIdeal.mul_induction_on hj
        (C := fun j => form D.sp.cm.sig J y x * j ∈
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E))
        (fun a ha b hb => ?_) (fun u v hu hv => by rw [mul_add]; exact Submodule.add_mem _ hu hv)
      have h1 := (intTr_iff_mem_dual _).1 ((hL _).1 (mem_lat.1 hy a ha) _ (mem_lat.1 hx _ (hc b hb)))
      rw [form_smul, star_star, mul_comm] at h1
      exact h1
    have hne : D.host.AA * D.host.AAbar ≠ 0 := mul_ne_zero AA_ne AAbar_ne
    have hle' : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x) ≤
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 := by
      rw [mul_assoc, mul_assoc] at hle
      calc FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x)
          = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x) * (D.host.AA * D.host.AAbar) *
            (D.host.AA * D.host.AAbar)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
        _ ≤ FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * (D.host.AA * D.host.AAbar) *
            (D.host.AA * D.host.AAbar)⁻¹ := by gcongr
        _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
    obtain ⟨z, hz⟩ := (FractionalIdeal.mem_spanSingleton _).1 (hle' (FractionalIdeal.mem_spanSingleton_self _ _))
    refine ⟨z, ?_⟩
    rw [← hz, Algebra.smul_def]
    field_simp
  · intro h
    refine mem_lat.2 fun c hcA => (hL _).2 fun x hx => ?_
    have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, IntTr (c * star u * form D.sp.cm.sig J y x) := by
      intro u hu
      refine FractionalIdeal.mul_induction_on hu (C := fun u => IntTr (c * star u * form D.sp.cm.sig J y x))
        (fun a ha e he => ?_) (fun u v hu hv => ?_)
      · obtain ⟨b, hb⟩ := h _ (smul_mem_lat hx he)
        have h1 := form_smul J 1 e y x
        rw [one_smul, one_mul] at h1
        have e1 : c * star (a * e) * form D.sp.cm.sig J y x = D.host.xi0 * c * star a * (b : D.host.E) := by
          rw [hb, h1, star_mul']
          field_simp
        rw [e1]
        exact ((intTr_iff_mem_dual _).2 (xi_mem hs hcA ha)).mul_int b
      · rw [star_add, mul_add, add_mul]
        exact hu.add hv
    have h1 := form_smul J c 1 y x
    rw [one_smul] at h1
    rw [h1]
    exact key 1 one_mem_AA_mul

private theorem exists_place (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (h : GlobalTheory.SqStepBig.EmbCM Bs) (τ : D.what₂.Tau) :
    ∃ w, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x) := by
  refine ⟨InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)), ?_⟩
  obtain ⟨τ', hτ'⟩ := h (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
  have e : τ' = τ := by
    apply (GlobalTheory.T.cmType_restrict_realSubfield_infinitePlace_bijective D).1
    have h1 := (Bs.emb (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))).2
    have h2 : ComplexEmbedding.conjugate ((tauE D τ').comp (algebraMap D.host.F D.host.E)) =
        (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))).embedding := by
      rw [← h1]
      ext x
      simp [hτ']
    show InfinitePlace.mk _ = InfinitePlace.mk _
    rw [← InfinitePlace.mk_conjugate_eq, h2, InfinitePlace.mk_embedding]
  rwa [e] at hτ'

end GlobalTheory.SkewOverW

open Matrix GlobalTheory.SkewOverW GlobalTheory.SkewLat GlobalTheory.WeilSchrodinger GlobalTheory.WeilSchrodingerHerm in
theorem _root_.GlobalTheory.T.exists_selfDual_orientedModel_scaled_skewHermitian : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → GlobalTheory.SqStepBig.EmbCM Bs →
    ∀ (d r y : ℕ) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d), Z.IsSkew D.sp.cm.sig Bs r y →
      ∃ (WW : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
        IsSelfDualC WW Λ ∧ NegIdx WW y ∧ GlobalTheory.SqStepBig.OverW WW Λ Z := by
  intro D Bs _ hemb d r y Z hZ
  have hξ : D.host.xi0 ≠ 0 := DualPair.xi_ne
  have hsξ : star D.host.xi0 = -D.host.xi0 := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
  have hsk : ∀ i j, star (Z.J j i) = -Z.J i j := fun i j => hZ.skew i j
  set G : Matrix (Fin d) (Fin d) D.host.E := (D.host.xi0⁻¹ • Z.J)ᵀ with hG
  have hGij : ∀ i j, G i j = D.host.xi0⁻¹ * Z.J j i := fun i j => rfl
  have hsG : ∀ i j, star (G i j) = G j i := fun i j => by
    rw [hGij, hGij, star_mul', star_inv₀, hsξ, hsk, inv_neg, neg_mul_neg]
  have hdetJ : Z.J.det ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    have h := det_ne_zero_of_hasSig (hZ.sig w)
    intro h0
    apply h
    have hm : (Z.J.map (Bs.emb w).1).det = (Bs.emb w).1 Z.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, hm, h0, map_zero, mul_zero]
  have hdet : G.det ≠ 0 := by
    rw [hG, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hξ)) hdetJ
  have hform : ∀ x v, sesq D G x v = D.host.xi0⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig Z.J v x := fun x v => by
    rw [hG, sesq_transpose_eq_form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul]
  have hsum : ∀ x v : Fin d → D.host.E, ∑ i, ∑ j, star (x i) * G i j * v j =
      D.host.xi0⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig Z.J v x := fun x v => by
    rw [← hform, sesq_apply]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  have hdual := dual_iff Z.J Z.L hZ.dual
  have hlat : Submodule.IsLattice D.host.E (scLat D.host.AA⁻¹ Z.L) :=
    PairLatLattice.scLat_isLattice (inv_ne_zero DualPair.AA_ne) hZ.lat
  have herm : (sesq D G).IsSymm := by
    refine ⟨fun x v => ?_⟩
    simp only [sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul',
      star_star, Pi.star_apply, hsG, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have nd : (sesq D G).Nondegenerate := by
    refine ⟨fun x hx => ?_, fun v hv => ?_⟩
    · have h1 : star x ᵥ* G = 0 := by
        refine dotProduct_eq_zero _ fun v => ?_
        rw [← Matrix.dotProduct_mulVec, ← sesq_apply]
        exact hx v
      have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
      simpa using congrArg star h2
    · have h1 : G *ᵥ v = 0 := by
        refine dotProduct_eq_zero _ fun u => ?_
        rw [dotProduct_comm]
        have := hv (star u)
        rwa [sesq_apply, star_star] at this
      exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) (scLat D.host.AA⁻¹ Z.L) := by
    show Formalism.E.hdual _ _ = _
    ext x
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [hdual x]
    refine forall₂_congr fun v _ => ?_
    rw [hform, Submodule.mem_one]
  have hgram := gram_hspOf G herm nd _ hlat hU (fun _ => (r, y))
  refine ⟨hspOf D G herm nd _ hlat hU (fun _ => (r, y)), scLat D.host.AA⁻¹ Z.L, ⟨hlat, fun v => ?_⟩, fun τ => ?_,
    rfl, ?_, fun v => mem_iff Z.L v⟩
  · rw [hgram]
    refine (hdual v).trans (forall₂_congr fun x _ => ?_)
    exact exists_congr fun b => Eq.congr_right (hsum x v).symm
  · obtain ⟨w, hw⟩ := exists_place Bs hemb τ
    have hs := hZ.sig w
    have hre : (tauE D τ D.host.xi0).re = 0 := by
      have h := congrArg Complex.re (GlobalTheory.FockCompare.tauE_star τ D.host.xi0)
      rw [hsξ, map_neg, Complex.neg_re, Complex.conj_re] at h
      linarith
    have hx : (Bs.emb w).1 D.host.xi0 = -((((tauE D τ D.host.xi0).im : ℝ) : ℂ) * Complex.I) := by
      rw [hw]; apply Complex.ext <;> simp [hre]
    have hJ : ∀ i j, Z.J i j = D.host.xi0 * star (G i j) := fun i j => by
      rw [hsG, hGij, mul_inv_cancel_left₀ hξ]
    have hM : Complex.I • Z.J.map (Bs.emb w).1 = (((tauE D τ D.host.xi0).im : ℝ) : ℂ) • G.map (tauE D τ) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      rw [hJ, map_mul, hx, hw, GlobalTheory.FockCompare.tauE_star, Complex.conj_conj]
      linear_combination (-(((tauE D τ D.host.xi0).im : ℝ) : ℂ) * tauE D τ (G i j)) * Complex.I_mul_I
    rw [hM] at hs
    have h := hasSignature_of_smul (xi_zero_im_pos D τ) hs
    have hr : r = d - y := by have := hs.1; omega
    rw [hr] at h
    unfold gramAt
    rw [hgram]
    exact h
  · rw [hgram]
    ext i j
    show Z.J i j = D.host.xi0 * G j i
    rw [hGij, mul_inv_cancel_left₀ hξ]
