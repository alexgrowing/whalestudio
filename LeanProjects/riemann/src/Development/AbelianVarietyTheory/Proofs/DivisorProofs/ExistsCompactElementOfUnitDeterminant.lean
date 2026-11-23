import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSelfDualLatticeSplitPlaceDictionary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

noncomputable section

namespace GlobalTheory.SplitDetStab

theorem exists_idem {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (hn : 0 < n) (C D : Matrix (Fin n) (Fin n) K)
    (hCD : C * D = 1) : ∃ P : Matrix (Fin n) (Fin n) K, P * P = P ∧ (∀ c : K, (1 + c • P).det = 1 + c) ∧
      (∀ i j, P i j ∈ O) ∧ ∀ i j, (C * P * D) i j ∈ O := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨⟨i, j⟩, -, hij⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => O.valuation (D p.1 p.2)) Finset.univ_nonempty
  have h0 : D i j ≠ 0 := by
    intro h
    have hD : D = 0 := by
      ext k l
      have := hij (k, l) (Finset.mem_univ _)
      simp only [h, map_zero, le_zero_iff] at this
      simpa using this
    rw [hD, Matrix.mul_zero] at hCD
    exact zero_ne_one hCD
  have hint : ∀ k l, (D i j)⁻¹ * D k l ∈ O := fun k l => by
    rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hij (k, l) (Finset.mem_univ _)) zero_le
  set x : Fin n → K := fun k => (D i j)⁻¹ * D k j with hx
  have hl : (Pi.single i 1 : Fin n → K) ⬝ᵥ x = 1 := by
    rw [single_dotProduct, one_mul, hx]; exact inv_mul_cancel₀ h0
  refine ⟨Matrix.vecMulVec x (Pi.single i 1), ?_, fun c => ?_, fun k l => ?_, fun k l => ?_⟩
  · rw [Matrix.vecMulVec_mul_vecMulVec, hl, one_smul]
  · rw [← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
      dotProduct_smul, hl, smul_eq_mul, mul_one]
  · rw [Matrix.vecMulVec_apply]
    by_cases e : l = i
    · subst e; simpa using hint k j
    · simp [e]
  · rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_apply]
    have e1 : (C *ᵥ x) k = (D i j)⁻¹ * (1 : Matrix (Fin n) (Fin n) K) k j := by
      rw [← hCD, Matrix.mul_apply, Finset.mul_sum]
      simp only [Matrix.mulVec, dotProduct, hx]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, Matrix.single_vecMul]
    by_cases e : k = j
    · subst e; simpa using hint i l
    · simp [Matrix.one_apply, e]

theorem keep {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (b : GL (Fin n) K) (Q : Matrix (Fin n) (Fin n) K)
    (hQ : ∀ i j, ((b⁻¹ : GL (Fin n) K).val * Q * b.val) i j ∈ O) {c : K} (hc : c ∈ O) (y : Fin n → K)
    (hy : ∀ i, ((b⁻¹ : GL (Fin n) K).val *ᵥ y) i ∈ O) (i : Fin n) :
    ((b⁻¹ : GL (Fin n) K).val *ᵥ ((1 + c • Q) *ᵥ y)) i ∈ O := by
  have e : (b⁻¹ : GL (Fin n) K).val *ᵥ ((1 + c • Q) *ᵥ y) = (b⁻¹ : GL (Fin n) K).val *ᵥ y +
      c • (((b⁻¹ : GL (Fin n) K).val * Q * b.val) *ᵥ ((b⁻¹ : GL (Fin n) K).val *ᵥ y)) := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.smul_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ b.val, Units.mul_inv, Matrix.mul_one]
  rw [e]
  exact add_mem (hy i) (mul_mem hc (sum_mem (t := Finset.univ) fun j _ => mul_mem (hQ i j) (hy j)))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mulVec_mem {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {d : ℕ} (W : Spc F E d) {v : Pl F}
    (τ : E →ₐ[F] Fv F v) {b₁ b₂ : GL (Fin d) (Fv F v)} (hb₁ : IsSplitBasis τ W.L b₁)
    (hb₂ : IsSplitBasis (τ.comp σ) W.L b₂) (M : Matrix (Fin d) (Fin d) (AE F E))
    (Q₁ Q₂ : Matrix (Fin d) (Fin d) (Fv F v)) {c₁ c₂ : Fv F v} (hc₁ : c₁ ∈ v.adicCompletionIntegers F)
    (hc₂ : c₂ ∈ v.adicCompletionIntegers F)
    (hQ₁ : ∀ i j, ((b₁⁻¹ : GL (Fin d) (Fv F v)).val * Q₁ * b₁.val) i j ∈ v.adicCompletionIntegers F)
    (hQ₂ : ∀ i j, ((b₂⁻¹ : GL (Fin d) (Fv F v)).val * Q₂ * b₂.val) i j ∈ v.adicCompletionIntegers F)
    (h₁ : M.map (piW τ) = 1 + c₁ • Q₁) (h₂ : M.map (piW (τ.comp σ)) = 1 + c₂ • Q₂)
    {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt W v) : M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  rw [GlobalTheory.SplitDictHerm.mem_latAt_iff_bases h W τ hb₁ hb₂] at hz ⊢
  have e : ∀ ρ : E →ₐ[F] Fv F v, (fun j => piW ρ ((M *ᵥ z) j)) = M.map (piW ρ) *ᵥ fun j => piW ρ (z j) :=
    fun ρ => funext fun j => RingHom.map_mulVec (piW ρ) M z j
  refine ⟨fun u hu => ?_, ?_, ?_⟩
  · rw [← Matrix.mulVec_smul, hz.1 u hu, Matrix.mulVec_zero]
  · rw [e, h₁]; exact keep _ b₁ Q₁ hQ₁ hc₁ _ hz.2.1
  · rw [e, h₂]; exact keep _ b₂ Q₂ hQ₂ hc₂ _ hz.2.2

theorem exists_mem_KAt_det_eq : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ u : (Fv F B.v₁)ˣ, ValuativeRel.valuation (Fv F B.v₁) (u : Fv F B.v₁) = 1 →
      ∃ k ∈ GlobalTheory.InertSph.KAt σ G.W B.v₁, Matrix.GeneralLinearGroup.det (GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ k) = u := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT u hu
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have skew : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j := fun i j => by
    rw [map_neg, map_one, neg_one_mul]; exact hT.geo.hW.skew i j
  have hJ : IsUnit (G.W.J.map B.τ₁).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J B.τ₁ (B.emb w).1 Complex.I Complex.I_ne_zero (G.W.θ w)
      (hT.geo.hW.cartan w)
  haveI := hT.geo.hW.lat
  obtain ⟨b₁, hb₁⟩ := exists_isSplitBasis B.τ₁ G.W.L hcm
  obtain ⟨b₂, hb₂⟩ := exists_isSplitBasis (B.τ₁.comp σ) G.W.L hcm
  have hn : 0 < a + a' := by have := hT.geo.aBig; omega
  haveI : (Valued.v : Valuation (Fv F B.v₁) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (Fv F B.v₁))
    (Valued.v : Valuation (Fv F B.v₁) (WithZero (Multiplicative ℤ)))
  have hu1 : Valued.v (u : Fv F B.v₁) = 1 := he.eq_one_iff_eq_one.1 hu
  have hc : (u : Fv F B.v₁) - 1 ∈ B.v₁.adicCompletionIntegers F :=
    sub_mem (by rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu1]) (one_mem _)
  have hc' : (u : Fv F B.v₁)⁻¹ - 1 ∈ B.v₁.adicCompletionIntegers F :=
    sub_mem (by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu1, inv_one]) (one_mem _)
  set J := G.W.J.map B.τ₁ with hJdef
  have hJ1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have hJ2 : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hJ
  obtain ⟨P, hPP, hdet, hP1, hP2⟩ := exists_idem (B.v₁.adicCompletionIntegers F) hn
    ((J * b₂.val)ᵀ * b₁.val) ((b₁⁻¹ : GL _ _).val * ((b₂⁻¹ : GL _ _).val * J⁻¹)ᵀ) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc b₁.val, Units.mul_inv, Matrix.one_mul, ← Matrix.transpose_mul,
        Matrix.mul_assoc, ← Matrix.mul_assoc J⁻¹, hJ2, Matrix.one_mul, Units.inv_mul, Matrix.transpose_one])
  set Q := b₁.val * P * (b₁⁻¹ : GL _ _).val with hQdef
  have hQQ : Q * Q = Q := by
    rw [hQdef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (b₁⁻¹ : GL _ _).val, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc P, hPP]
  have hmul : ∀ c c' : Fv F B.v₁, c * c' = 1 → (1 + (c - 1) • Q) * (1 + (c' - 1) • Q) = 1 := fun c c' e => by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hQQ,
      smul_smul, add_assoc, ← add_smul, ← add_smul,
      show c' - 1 + (c - 1 + (c - 1) * (c' - 1)) = 0 by linear_combination e, zero_smul, add_zero]
  let g : GL (Fin (a + a')) (Fv F B.v₁) := ⟨1 + ((u : Fv F B.v₁) - 1) • Q, 1 + ((u : Fv F B.v₁)⁻¹ - 1) • Q,
    hmul _ _ (mul_inv_cancel₀ u.ne_zero), hmul _ _ (inv_mul_cancel₀ u.ne_zero)⟩
  have hQ₁ : ∀ i j, ((b₁⁻¹ : GL _ _).val * Q * b₁.val) i j ∈ B.v₁.adicCompletionIntegers F := by
    rw [hQdef]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    exact hP1
  have hQ₂ : ∀ i j, ((b₂⁻¹ : GL _ _).val * (J⁻¹ * Qᵀ * J) * b₂.val) i j ∈ B.v₁.adicCompletionIntegers F := by
    intro i j
    have := hP2 j i
    have e : (b₂⁻¹ : GL _ _).val * (J⁻¹ * Qᵀ * J) * b₂.val =
        ((J * b₂.val)ᵀ * b₁.val * P * ((b₁⁻¹ : GL _ _).val * ((b₂⁻¹ : GL _ _).val * J⁻¹)ᵀ))ᵀ := by
      simp only [hQdef, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [e]
    exact this
  have hconj : ∀ c : Fv F B.v₁, J⁻¹ * (1 + c • Q)ᵀ * J = 1 + c • (J⁻¹ * Qᵀ * J) := fun c => by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, hJ2, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨GlobalTheory.SplitUnitLift.liftU hcm B.τ₁ G.W.J (-1) skew hJ g,
    ⟨GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm B.τ₁ G.W (-1) skew hJ g, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · exact mulVec_mem hcm G.W B.τ₁ hb₁ hb₂ _ Q _ hc hc' hQ₁ hQ₂
      (GlobalTheory.SplitUnitLift.liftU_piW hcm B.τ₁ G.W.J (-1) skew hJ g)
      ((GlobalTheory.SplitUnitLift.liftU_piW_comp hcm B.τ₁ G.W.J (-1) skew hJ g).trans (hconj _)) hz
  · rw [← map_inv]
    exact mulVec_mem hcm G.W B.τ₁ hb₁ hb₂ _ Q _ hc' hc hQ₁ hQ₂
      (GlobalTheory.SplitUnitLift.liftU_piW hcm B.τ₁ G.W.J (-1) skew hJ g⁻¹)
      ((GlobalTheory.SplitUnitLift.liftU_piW_comp hcm B.τ₁ G.W.J (-1) skew hJ g⁻¹).trans (hconj _)) hz
  · refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, GlobalTheory.LocalUnitSubgroupClosure.cmpGL_val, GlobalTheory.SplitUnitLift.liftU_piW]
    show (1 + ((u : Fv F B.v₁) - 1) • Q).det = u
    have e : 1 + ((u : Fv F B.v₁) - 1) • Q = b₁.val * (1 + ((u : Fv F B.v₁) - 1) • P) * (b₁⁻¹ : GL _ _).val := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv, Matrix.mul_smul, Matrix.smul_mul]
    rw [e, Matrix.det_units_conj, hdet, add_sub_cancel]

end GlobalTheory.SplitDetStab

end
