import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapPairsContinuousDensityNearDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitPropsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarMeasureGramGL2ActionTensorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompactsStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeEx.SwapLoc

theorem dens_compare {V T : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure V) (τ : Measure T) [SigmaFinite τ] [τ.IsOpenPosMeasure]
    (g : V → T) (Γ : V ≃ₜ V) (Φ : T ≃ₜ T) (hg : ∀ X, g (Γ X) = Φ (g X))
    (c₁ c₂ : ℝ≥0) (hμ : μ = c₁ • μ.map Γ) (hτ : τ = c₂ • τ.map Φ) (φ : V → ℝ)
    (U₁ U₂ : Set T) (D₁ D₂ : T → ℝ) (t : T) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (ht₁ : t ∈ U₁) (ht₂ : Φ t ∈ U₂) (hD₁ : ContinuousOn D₁ U₁) (hD₂ : ContinuousOn D₂ U₂)
    (h0₁ : 0 ≤ D₁ t) (h0₂ : 0 ≤ D₂ (Φ t))
    (h₁ : ∀ S ⊆ U₁, MeasurableSet S →
      ∫⁻ X in g ⁻¹' S, ENNReal.ofReal (φ (Γ X)) ∂μ = ∫⁻ t in S, ENNReal.ofReal (D₁ t) ∂τ)
    (h₂ : ∀ S ⊆ U₂, MeasurableSet S →
      ∫⁻ X in g ⁻¹' S, ENNReal.ofReal (φ X) ∂μ = ∫⁻ t in S, ENNReal.ofReal (D₂ t) ∂τ) :
    (c₂ : ℝ) * D₂ (Φ t) = c₁ * D₁ t := by
  set W : Set T := U₁ ∩ Φ ⁻¹' U₂ with hW
  have hWo : IsOpen W := hU₁.inter (hU₂.preimage Φ.continuous)
  have k₁ : ContinuousOn (fun s => ENNReal.ofReal ((c₁ : ℝ) * D₁ s)) W :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul (hD₁.mono Set.inter_subset_left))
  have k₂ : ContinuousOn (fun s => ENNReal.ofReal ((c₂ : ℝ) * D₂ (Φ s))) W :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul (hD₂.comp Φ.continuous.continuousOn fun s hs => hs.2))
  have hae : (fun s => ENNReal.ofReal ((c₂ : ℝ) * D₂ (Φ s))) =ᵐ[τ.restrict W]
      fun s => ENNReal.ofReal ((c₁ : ℝ) * D₁ s) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (k₂.aemeasurable hWo.measurableSet)
      (k₁.aemeasurable hWo.measurableSet) fun s hs _ => ?_
    rw [Measure.restrict_restrict hs]
    set S := s ∩ W with hS
    have hSm : MeasurableSet S := hs.inter hWo.measurableSet
    have e₁ := h₁ S (fun z hz => hz.2.1) hSm
    have e₂ := h₂ (Φ '' S) (by rintro _ ⟨z, hz, rfl⟩; exact hz.2.2)
      (Φ.measurableEmbedding.measurableSet_image.2 hSm)
    have a₁ : ∫⁻ X in g ⁻¹' (Φ '' S), ENNReal.ofReal (φ X) ∂μ =
        c₁ * ∫⁻ X in g ⁻¹' S, ENNReal.ofReal (φ (Γ X)) ∂μ := by
      conv_lhs => rw [hμ]
      rw [Measure.restrict_smul, lintegral_smul_measure, Γ.measurableEmbedding.restrict_map,
        Γ.measurableEmbedding.lintegral_map]
      have : Γ ⁻¹' (g ⁻¹' (Φ '' S)) = g ⁻¹' S := by
        ext X
        simp only [Set.mem_preimage, hg]
        exact Φ.injective.mem_set_image
      rw [this]; rfl
    have a₂ : ∫⁻ t in Φ '' S, ENNReal.ofReal (D₂ t) ∂τ =
        c₂ * ∫⁻ t in S, ENNReal.ofReal (D₂ (Φ t)) ∂τ := by
      conv_lhs => rw [hτ]
      rw [Measure.restrict_smul, lintegral_smul_measure, Φ.measurableEmbedding.restrict_map,
        Φ.measurableEmbedding.lintegral_map, Set.preimage_image_eq _ Φ.injective]
      rfl
    simp only [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
      ← a₂, ← e₂, a₁, e₁]
  have := Measure.eqOn_open_of_ae_eq hae hWo k₂ k₁ (show t ∈ W from ⟨ht₁, ht₂⟩)
  exact (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg c₂.2 h0₂) (mul_nonneg c₁.2 h0₁)).1 this

theorem lrAct_one_apply {S : Type} [CommRing S] {n M : ℕ} (γ : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) (a : Fin n) (i : Fin M) :
    lrAct 1 γ X a i = ∑ c, X c i * γ c a := by
  simp [lrAct]

theorem lrAct_one_mul {S : Type} [CommRing S] {n M : ℕ} (γ δ : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) : lrAct 1 δ (lrAct 1 γ X) = lrAct 1 (γ * δ) X := by
  funext a i
  simp only [lrAct_one_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lrAct_one_one {S : Type} [CommRing S] {n M : ℕ}
    (X : Fin n → Fin M → S) : lrAct 1 1 X = X := by
  funext a i
  simp [lrAct_one_apply, Matrix.one_apply]

theorem continuous_lrAct_one {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    {n M : ℕ} (γ : Matrix (Fin n) (Fin n) S) :
    Continuous (lrAct (M := M) 1 γ) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [lrAct_one_apply]
  fun_prop

def lrHomeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    {n M : ℕ} (γ δ : Matrix (Fin n) (Fin n) S) (h₁ : γ * δ = 1) (h₂ : δ * γ = 1) :
    (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S) where
  toFun := lrAct 1 γ
  invFun := lrAct 1 δ
  left_inv X := by rw [lrAct_one_mul, h₁, lrAct_one_one]
  right_inv X := by rw [lrAct_one_mul, h₂, lrAct_one_one]
  continuous_toFun := continuous_lrAct_one γ
  continuous_invFun := continuous_lrAct_one δ

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E)

theorem hR_incl {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (y i)) = inclR R (hE σ J x y) := by
  simp [hR, hE, Formalism.UG.hform, map_sum, JR, sigR, inclR]

theorem qR_incl [CharZero F] (h2 : Module.finrank F E = 2) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x : Fin M → E) (a : F) (h : hE σ J x x = algebraMap F E a) :
    qR R σ J (fun i => inclR R (x i)) = algebraMap F R a := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have e : inclR (F := F) R (algebraMap F E a) = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a
  rw [qR, hR_incl, h, e, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2))]
  rw [Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
  have : algebraMap F R (1 / 2) * ((2 : ℕ) : R) = 1 := by
    rw [← map_natCast (algebraMap F R), ← map_mul]; norm_num
  rw [this, one_mul]

theorem hE_mulVec {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M) (Fin M') E)
    (y : Fin M' → E) :
    hE σ J (B.mulVec y) (B.mulVec y) = hE σ (Formalism.UG.cT (σ : E →+* E) B * J * B) y y := by
  have k : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (u v : Fin n → E),
      hE σ A u v = (fun i => σ (u i)) ⬝ᵥ A.mulVec v := by
    intro n A u v
    simp [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have : (fun i => σ (B.mulVec y i)) = Matrix.vecMul (fun i => σ (y i)) (Formalism.UG.cT (σ : E →+* E) B) := by
    funext i
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, mul_comm]
  rw [k, k, this, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem hE_mulVec_zero {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M) (Fin M') E)
    (x : Fin M → E) (h : ∀ j, hE σ J x (fun i => B i j) = 0) (y : Fin M' → E) :
    hE σ J x (B.mulVec y) = 0 := by
  have : hE σ J x (B.mulVec y) = ∑ j, hE σ J x (fun i => B i j) * y j := by
    simp only [hE, Formalism.UG.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin M')))]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  simp [this, h]

theorem unitaryOrthogonalComplement_gram_step [CharZero F] (h2 : Module.finrank F E = 2) {M : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (y : Fin M → E) (b : F)
    (h : StepData σ J x a B J') (hy : hE σ J' y y = algebraMap F E b) :
    gram3 R σ J (ratTup (F := F) R ![x 0, B.mulVec y]) = (algebraMap F R a, 0, algebraMap F R b) := by
  obtain ⟨-, -, hx, hB, hJ, -⟩ := h
  refine Prod.ext (qR_incl R σ h2 J (x 0) a hx) (Prod.ext ?_ (qR_incl R σ h2 J (B.mulVec y) b ?_))
  · have := hR_incl R σ J (x 0) (B.mulVec y)
    rw [hE_mulVec_zero σ J B (x 0) hB, map_zero] at this
    exact this
  · rw [hE_mulVec, ← hJ, hy]

theorem ratTup_lrAct {n M : ℕ} (γ : Matrix (Fin n) (Fin n) E) (X : Fin n → Fin M → E) :
    ratTup (F := F) R (lrAct 1 γ X) = lrAct 1 (γ.map (inclR R)) (ratTup (F := F) R X) := by
  funext a i
  simp [ratTup, lrAct_one_apply, map_sum]

end Alg

theorem twoStep_swap_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x₁ : Fin 1 → Fin (M + 1) → E) (a₁ : F) (B₁ : Matrix (Fin (M + 1)) (Fin M) E) (J₁' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (a₂ : F) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (y₁ y₂ : Fin 1 → Fin M → E) (b₁ b₂ : F) (γ : GL (Fin 2) E), StepData σ J x₁ a₁ B₁ J₁' → StepData σ J x₂ a₂ B₂ J₂' → b₁ ≠ 0 → b₂ ≠ 0 → hE σ J₁' (y₁ 0) (y₁ 0) = algebraMap F E b₁ → hE σ J₂' (y₂ 0) (y₂ 0) = algebraMap F E b₂ → ![x₂ 0, B₂.mulVec (y₂ 0)] = lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] → ∃ u : E, u ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m₁ m₂ : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m₁' m₂' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N₁ N₂ : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 (M + 1)) ν (algebraMap F R a₁) m₁ → FibAt R σ J₁' (tupMeas lam 1 M) ν (algebraMap F R b₁) m₁' → FibAt R σ J (tupMeas lam 1 (M + 1)) ν (algebraMap F R a₂) m₂ → FibAt R σ J₂' (tupMeas lam 1 M) ν (algebraMap F R b₂) m₂' → TwoStep R σ J x₁ B₁ m₁ m₁' N₁ → TwoStep R σ J x₂ B₂ m₂ m₂' N₂ → N₂ = modu (R ⊗[F] E) (inclR R u) • N₁.map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R))) := by
  intro F E _ _ _ _ _ σ hσ M J x₁ a₁ B₁ J₁' x₂ a₂ B₂ J₂' y₁ y₂ b₁ b₂ γ hS₁ hS₂ hb₁ hb₂ hy₁ hy₂ hγ
  have hP₁ := (GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ (AF F) M J x₁ a₁ B₁ J₁' hS₁).1
  have hP₂ := (GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ (AF F) M J x₂ a₂ B₂ J₂' hS₂).1
  have hd : (γ : Matrix (Fin 2) (Fin 2) E).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  set d := (γ : Matrix (Fin 2) (Fin 2) E).det with hdd
  have hw₁ : (consCol x₁ B₁).det / algebraMap F E a₁ ≠ 0 :=
    div_ne_zero hP₁ ((map_ne_zero _).2 hS₁.2.1)
  have hw₂ : (consCol x₂ B₂).det / algebraMap F E a₂ ≠ 0 :=
    div_ne_zero hP₂ ((map_ne_zero _).2 hS₂.2.1)
  set w₁ := (consCol x₁ B₁).det / algebraMap F E a₁ with hw₁d
  set w₂ := (consCol x₂ B₂).det / algebraMap F E a₂ with hw₂d
  have hu : d ^ (M + 1) * w₁ / (d ^ 2 * w₂) ≠ 0 := by positivity
  refine ⟨d ^ (M + 1) * w₁ / (d ^ 2 * w₂), hu, ?_⟩
  have hue : d ^ (M + 1) * w₁ / (d ^ 2 * w₂) * (d ^ 2 * w₂) = d ^ (M + 1) * w₁ :=
    div_mul_cancel₀ _ (by positivity)
  generalize d ^ (M + 1) * w₁ / (d ^ 2 * w₂) = u at hu hue ⊢
  intro R _ _ _ _ _ _ _ _ _ hR lam ν m₁ m₂ m₁' m₂' N₁ N₂ hlam hν f₁ f₁' f₂ f₂' t₁ t₂
  obtain ⟨hart, hred, -⟩ := nice_tensor F E R hR
  obtain ⟨hpos, hmul, hone, -⟩ := modu_basic (R ⊗[F] E)
  have un : ∀ {z : E}, z ≠ 0 → IsUnit (inclR (F := F) R z) := fun hz => (IsUnit.mk0 _ hz).map _
  have unF : ∀ {z : F}, z ≠ 0 → IsUnit (algebraMap F R z) := fun hz => (IsUnit.mk0 _ hz).map _
  have mm : ∀ {z w : E}, z ≠ 0 → w ≠ 0 → modu (R ⊗[F] E) (inclR R (z * w)) =
      modu (R ⊗[F] E) (inclR R z) * modu (R ⊗[F] E) (inclR R w) := fun hz hw => by
    rw [map_mul, hmul _ _ (un hz) (un hw)]
  have mp : ∀ k : ℕ, modu (R ⊗[F] E) (inclR R (d ^ k)) = modu (R ⊗[F] E) (inclR R d) ^ k := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ, mm (pow_ne_zero _ hd) hd, ih, pow_succ]
  have key : modu (R ⊗[F] E) (inclR R u) * (modu (R ⊗[F] E) (inclR R d) ^ 2 *
      modu (R ⊗[F] E) (inclR R w₂)) =
      modu (R ⊗[F] E) (inclR R d) ^ (M + 1) * modu (R ⊗[F] E) (inclR R w₁) := by
    rw [← mp, ← mp, ← mm (pow_ne_zero _ hd) hw₂, ← mm (pow_ne_zero _ hd) hw₁,
      ← mm hu (by positivity), hue]
  have fin₁ : IsFiniteMeasureOnCompacts N₁ :=
    GlobalTheory.T.twoStep_pair_measure_finite_on_compacts F E σ hσ R hR M J x₁ a₁ B₁ J₁' m₁ m₁' N₁ hS₁
      (GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hσ R hR _ J x₁ a₁ lam ν m₁ hS₁.1 hS₁.2.1 hS₁.2.2.1 hlam hν f₁).2.1
      (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hR _ J _ ν _ m₁ hν (unF hS₁.2.1) f₁).2.1
      (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hR _ J₁' _ ν _ m₁' hν (unF hb₁) f₁').2.1
      (GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hσ R hR _ J₁' y₁ b₁ lam ν m₁' hS₁.2.2.2.2.2 hb₁ hy₁ hlam hν f₁').1 t₁
  have fin₂ : IsFiniteMeasureOnCompacts N₂ :=
    GlobalTheory.T.twoStep_pair_measure_finite_on_compacts F E σ hσ R hR M J x₂ a₂ B₂ J₂' m₂ m₂' N₂ hS₂
      (GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hσ R hR _ J x₂ a₂ lam ν m₂ hS₂.1 hS₂.2.1 hS₂.2.2.1 hlam hν f₂).2.1
      (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hR _ J _ ν _ m₂ hν (unF hS₂.2.1) f₂).2.1
      (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hR _ J₂' _ ν _ m₂' hν (unF hb₂) f₂').2.1
      (GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hσ R hR _ J₂' y₂ b₂ lam ν m₂' hS₂.2.2.2.2.2 hb₂ hy₂ hlam hν f₂').1 t₂
  let Γ : (Fin 2 → Fin (M + 1) → R ⊗[F] E) ≃ₜ (Fin 2 → Fin (M + 1) → R ⊗[F] E) :=
    lrHomeo ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R))
      (((γ⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).map (inclR R))
      (by rw [← Matrix.map_mul, Units.mul_inv]; simp) (by rw [← Matrix.map_mul, Units.inv_mul]; simp)
  change N₂ = modu (R ⊗[F] E) (inclR R u) • N₁.map Γ
  obtain ⟨Φ, hΦ, hτ⟩ := GlobalTheory.T.haar_measure_gram_GL2_action_tensor F E σ hσ R lam ν γ hlam hν
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (F := F) R)).det = inclR R d :=
    ((inclR (F := F) R).map_det _).symm
  have hμ := GlobalTheory.T.vectorTupleProductMeasure_two_sided_action (R ⊗[F] E) hart hred lam hlam 2 (M + 1) 1
    ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R)) (by simp) (by rw [hdet]; exact un hd)
  rw [hdet, Matrix.det_one, hone, one_pow, one_mul] at hμ
  have g₁ := unitaryOrthogonalComplement_gram_step R σ hσ.2.2.1 J x₁ a₁ B₁ J₁' (y₁ 0) b₁ hS₁ hy₁
  have g₂ := unitaryOrthogonalComplement_gram_step R σ hσ.2.2.1 J x₂ a₂ B₂ J₂' (y₂ 0) b₂ hS₂ hy₂
  rw [hγ, ratTup_lrAct, hΦ _ J hS₁.1, g₁] at g₂
  have fin₃ : IsFiniteMeasureOnCompacts (N₁.map Γ) := Measure.IsFiniteMeasureOnCompacts.map N₁ Γ
  have : TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin (M + 1) → R ⊗[F] E) :=
    TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology _
  have r₂ : N₂.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have r₁ : (N₁.map Γ).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f => ?_
  have fc : Continuous fun X => (f X : ℝ) := NNReal.continuous_coe.comp f.continuous
  have fs : HasCompactSupport fun X => (f X : ℝ) :=
    f.hasCompactSupport.comp_left (g := fun r : ℝ≥0 => (r : ℝ)) rfl
  obtain ⟨U₂, D₂, o₂, e₂, c₂, n₂, i₂, v₂⟩ := GlobalTheory.T.gramMap_pairs_continuous_density_near_diagonal F E σ hσ R hR M J x₂ a₂ B₂ J₂' y₂ b₂ lam ν
    m₂ m₂' N₂ hS₂ hb₂ hy₂ hlam hν f₂ f₂' t₂ (fun X => (f X : ℝ)) fc fs (fun X => (f X).2)
  obtain ⟨U₁, D₁, o₁, e₁, c₁, n₁, i₁, v₁⟩ := GlobalTheory.T.gramMap_pairs_continuous_density_near_diagonal F E σ hσ R hR M J x₁ a₁ B₁ J₁' y₁ b₁ lam ν
    m₁ m₁' N₁ hS₁ hb₁ hy₁ hlam hν f₁ f₁' t₁ (fun X => (f (Γ X) : ℝ)) (fc.comp Γ.continuous)
    (fs.comp_homeomorph Γ) (fun X => (f (Γ X)).2)
  have cmp := dens_compare (tupMeas lam 2 (M + 1)) (ν.prod (lam.prod ν)) (gram3 R σ J) Γ Φ
    (hΦ _ J hS₁.1) _ _ hμ hτ (fun X => (f X : ℝ)) U₁ U₂ D₁ D₂ _ o₁ o₂ e₁ (g₂ ▸ e₂) c₁ c₂
    (n₁ _ e₁) (n₂ _ (g₂ ▸ e₂)) i₁ i₂
  rw [g₂, v₁, v₂] at cmp
  rw [integral_smul_nnreal_measure, Γ.measurableEmbedding.integral_map, NNReal.smul_def, smul_eq_mul]
  have p₁ : (0 : ℝ) < modu (R ⊗[F] E) (inclR R d) := (hpos _ (un hd)).1
  have p₂ : (0 : ℝ) < modu (R ⊗[F] E) (inclR R w₂) := (hpos _ (un hw₂)).1
  have key' := congrArg (fun r : ℝ≥0 => (r : ℝ)) key
  simp only [NNReal.coe_mul, NNReal.coe_pow] at key' cmp
  refine mul_left_cancel₀ (mul_pos (pow_pos p₁ 2) p₂).ne' ?_
  rw [mul_assoc, cmp, ← mul_assoc, ← key']
  ring

end GlobalTheory.GaugeEx.SwapLoc
