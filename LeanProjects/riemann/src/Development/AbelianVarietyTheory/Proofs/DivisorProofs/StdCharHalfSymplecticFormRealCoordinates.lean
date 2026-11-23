import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMRealLineFiniteInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.RealCharF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infPartF_cAF (σ : E →ₐ[F] E) (z : AEF F E) :
    infPartF F E (cAF σ z) = sigR (Ainf F) σ (infPartF F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem conj_theta_tmul_one [IsTotallyReal F] {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (a : Ainf F) :
    starRingEnd ℂ (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val τ w hw θ h a, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem theta_sigR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ)
    (y : Ainf F ⊗[F] E) : θ (sigR (Ainf F) σ y) = starRingEnd ℂ (θ y) := by
  haveI : IsTotallyReal F := hσ.1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e =>
    have e1 : ∀ e' : E, a ⊗ₜ[F] e' = (a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] e') := by
      intro e'; rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    show θ (a ⊗ₜ[F] σ e) = _
    rw [e1 (σ e), e1 e, map_mul, map_mul, map_mul, h.1, h.1, hσ.2.2.2, conj_theta_tmul_one hw h a]
    rfl

theorem theta_infPartF_incAF {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (e : E) :
    θ (infPartF F E (incAF F E e)) = τ e := by
  have : infPartF F E (incAF F E e) = (1 : Ainf F) ⊗ₜ[F] e := by
    show (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rw [this, h.1]

theorem theta_fstA_symplOHF {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ)
    {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y : WOF F E nS nT) :
    θ (fstA F (symplOHF σ JS JT ξ₀ x y) ⊗ₜ[F] (1 : E)) =
      ((τ ξ₀ * θ (infPartF F E (hOF σ JS JT x y))).re : ℂ) := by
  set z := incAF F E ξ₀ * hOF σ JS JT x y with hz
  have h1 : fstA F (symplOHF σ JS JT ξ₀ x y) =
      algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (infPartF F E z) := by
    unfold symplOHF symplOF
    rw [map_mul, AlgHom.commutes, GlobalTheory.HeisLineDiffF.map_trace_tens]
    rfl
  have h2 : ∀ c : Ainf F, c ⊗ₜ[F] (1 : E) = algebraMap (Ainf F) (Ainf F ⊗[F] E) c := by
    intro c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h3 : θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (algebraMap F (Ainf F) (1 / 2))) = 1 / 2 := by
    rw [← IsScalarTower.algebraMap_apply]
    have : (θ.comp (algebraMap F (Ainf F ⊗[F] E))) (1 / 2) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    exact this
  have h4 : θ (infPartF F E z) = τ ξ₀ * θ (infPartF F E (hOF σ JS JT x y)) := by
    rw [hz, map_mul, map_mul, theta_infPartF_incAF h]
  rw [h1, h2, map_mul, map_mul, GlobalTheory.SelfDualLatticeCompare.trace_tensor (Ainf F) hσ, map_add,
    theta_sigR hσ hw h, h3, h4, Complex.add_conj]
  push_cast
  ring

theorem theta_hOF {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {tau : InfinitePlace F → (E →+* ℂ)}
    (hw : ∀ w, w.embedding = (tau w).comp (algebraMap F E)) {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)}
    (hθ : IsInfFamF tau θ) {ι : (InfinitePlace F → ℂ) →+ AEF F E} (hι : IsChartF θ ι)
    {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} (JT : Matrix (Fin nT) (Fin nT) E) (hJS : JS.det ≠ 0)
    (u v : IxF F nS nT → ℂ) (w : InfinitePlace F) :
    θ w (infPartF F E (hOF σ JS JT (iotaVF ι u) (iotaVF ι v))) =
      ((JS.map (tau w))⁻¹ * (cpt v w)ᴴ * JT.map (tau w) * cpt u w).trace := by
  rw [GlobalTheory.OrientedChar.map_inv_field _ _ hJS, GlobalTheory.OrientedChar.trace_four]
  unfold hOF
  simp only [map_sum, map_mul, infPartF_cAF, theta_sigR hσ (hw w) (hθ w), theta_infPartF_incAF (hθ w),
    iotaVF, Matrix.of_apply, hι.comp, cpt, Matrix.map_apply]

theorem trace_HMF {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (tau : InfinitePlace F → (E →+* ℂ)) (u v : IxF F nS nT → ℂ) :
    star v ⬝ᵥ HMF JS JT ξ₀ tau *ᵥ u = ∑ w, ((2 * (tau w ξ₀).im : ℝ) : ℂ) *
      ((JS.map (tau w))⁻¹ * (cpt v w)ᴴ * JT.map (tau w) * cpt u w).trace := by
  rw [star_dotProduct_eq]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold HMF
  rw [cpt_blk, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem psi_symplOHF_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ θ hθ ι hι u v
  have hσ := hB.cm
  haveI : IsTotallyReal F := hσ.1
  have hψ := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  have hw : ∀ w : InfinitePlace F, w.embedding = (B.emb w).1.comp (algebraMap F E) := fun w => (B.emb w).2.symm
  set s := symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v) with hs
  have hsnd : sndA F s = 0 :=
    GlobalTheory.HeisDerivCM.map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ _ _ (Or.inr (real_iotaVF hι v))
  have e1 : B.ψ s = psiInf F B.ψ (fstA F s) := by
    have hsplit : s = pairA F (fstA F s) 0 := Prod.ext rfl hsnd
    conv_lhs => rw [hsplit]
    rfl
  have hre : ∀ w : InfinitePlace F, ((B.emb w).1 ξ₀).re = 0 := by
    intro w
    have h1 := hσ.2.2.2 (B.emb w).1 ξ₀
    rw [hσξ, map_neg] at h1
    have h2 := congrArg Complex.re h1
    rw [Complex.neg_re, Complex.star_def, Complex.conj_re] at h2
    linarith
  rw [e1, hψ.2.2 θ hθ, trace_HMF]
  have e2 : ∑ w, θ w (fstA F s ⊗ₜ[F] (1 : E)) = ∑ w, ((((B.emb w).1 ξ₀) *
      ((JS.map (B.emb w).1)⁻¹ * (cpt v w)ᴴ * JT.map (B.emb w).1 * cpt u w).trace).re : ℂ) :=
    Finset.sum_congr rfl fun w _ => by
      rw [hs, theta_fstA_symplOHF hσ (hw w) (hθ w) JS JT ξ₀ (iotaVF ι u) (iotaVF ι v),
        theta_hOF hσ hw hθ hι JT hJS.2 u v]
  rw [e2]
  congr 1
  rw [Complex.im_sum]
  simp only [Complex.mul_re, hre, Complex.im_ofReal_mul, zero_mul, zero_sub]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

end GlobalTheory.RealCharF
