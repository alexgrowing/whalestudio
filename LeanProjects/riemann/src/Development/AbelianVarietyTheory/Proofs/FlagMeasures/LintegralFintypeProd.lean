import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.Push

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_prod {n : ℕ} {X : Fin n → Type}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : Fin n) → Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → X i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : X 0 × ((i : Fin n) → X (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : X (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← ih _ (fun i => hf _), ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {ι : Type} [Fintype ι] {X : ι → Type} {mX : ∀ i, MeasurableSpace (X i)}
    {μ : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (μ i)] in
private theorem lmarginal_prod_eq_prod_lintegral_mul_prod [DecidableEq ι] (f : (i : ι) → X i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (s : Finset ι) (x : (i : ι) → X i) :
    (∫⋯∫⁻_s, (fun z => ∏ i, f i (z i)) ∂μ) x =
      (∏ i ∈ s, ∫⁻ y, f i y ∂(μ i)) * ∏ i ∈ sᶜ, f i (x i) := by
  have hF : Measurable fun z : (i : ι) → X i => ∏ i, f i (z i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert i s hi ih =>
    rw [lmarginal_insert _ hF hi]
    simp_rw [ih]
    have h : ∀ y, ∏ j ∈ sᶜ, f j (Function.update x i y j) =
        f i y * ∏ j ∈ (insert i s)ᶜ, f j (x j) := by
      intro y
      rw [Finset.compl_insert, ← Finset.mul_prod_erase _ _ (Finset.mem_compl.2 hi),
        Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    simp_rw [h]
    rw [Finset.prod_insert hi, lintegral_const_mul _ ((hf i).mul_const _),
      lintegral_mul_const _ (hf i)]
    ring

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
theorem _root_.GlobalTheory.SnMass.Push.lintegral_fintype_prod {ι : Type} [Fintype ι] {X : ι → Type}
    {mX : ∀ i, MeasurableSpace (X i)}
    {μ : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → X i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  by_cases hne : ∀ i, Nonempty (X i)
  · rw [lintegral_eq_lmarginal_univ (fun i => (hne i).some), lmarginal_prod_eq_prod_lintegral_mul_prod f hf]
    simp
  · push_neg at hne
    obtain ⟨i, hi⟩ := hne
    haveI : IsEmpty ((i : ι) → X i) := ⟨fun x => hi.elim (x i)⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Measure.eq_zero_of_isEmpty (μ i)])]
    simp [Measure.eq_zero_of_isEmpty (Measure.pi μ)]

theorem lintegral_comp_prod {ι : Type} [Fintype ι] {X : ι → Type} {mX : ∀ i, MeasurableSpace (X i)}
    {μ : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (μ i)] {G : Type} [MeasurableSpace G] (α : Measure G)
    (ρ : G → ∀ i, X i) (hρ : Measurable ρ)
    (h : ∀ B : ∀ i, Set (X i), (∀ i, MeasurableSet (B i)) → α (ρ ⁻¹' Set.pi Set.univ B) = ∏ i, μ i (B i))
    (f : (i : ι) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun g => ∏ i, f i (ρ g i)) ∧ ∫⁻ g, ∏ i, f i (ρ g i) ∂α = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  have hm : Measurable fun x : ∀ i, X i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)
  have he : Measure.pi μ = α.map ρ := Measure.pi_eq fun B hB => by
    rw [Measure.map_apply hρ (MeasurableSet.univ_pi hB), h B hB]
  refine ⟨hm.comp hρ, ?_⟩
  rw [← lintegral_fintype_prod f hf, he, lintegral_map hm hρ]

theorem lintegral_real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μw : InfinitePlace E → Measure (Mt k r)) (θ : InfinitePlace E → (Ainf F ⊗[F] E →+* ℂ)) (α : Measure (HA (Ainf F) σ J)), IsCMExt F E σ → IsHermND σ J → IsModelAt J A → (∀ w, SigmaFinite (μw w)) → (∀ w, Formalism.MainNotions.StandardLattice.IsInfEmb w.embedding (θ w)) → (∀ B : InfinitePlace E → Set (Mt k r), (∀ w, MeasurableSet (B w)) → MeasurableSet {h : HA (Ainf F) σ J | ∀ w, ∃ b ∈ B w, Matrix.of b * A w = A w * (((HA.mat (Ainf F) σ J h : GL (Fin (2 * r + k + 1)) (Ainf F ⊗[F] E)) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) (Ainf F ⊗[F] E))).map (θ w)} → α {h | ∀ w, ∃ b ∈ B w, Matrix.of b * A w = A w * (((HA.mat (Ainf F) σ J h : GL (Fin (2 * r + k + 1)) (Ainf F ⊗[F] E)) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) (Ainf F ⊗[F] E))).map (θ w)} = ∏ w, μw w (B w)) → (∀ w, IsUnit (A w).det) ∧ ∀ Ψ : InfinitePlace E → Mt k r → ℝ≥0∞, (∀ w, Measurable (Ψ w)) → Measurable (fun h : HA (Ainf F) σ J => ∏ w, Ψ w (Matrix.of.symm (A w * (((HA.mat (Ainf F) σ J h : GL (Fin (2 * r + k + 1)) (Ainf F ⊗[F] E)) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) (Ainf F ⊗[F] E))).map (θ w) * (A w)⁻¹))) ∧ ∫⁻ h, ∏ w, Ψ w (Matrix.of.symm (A w * (((HA.mat (Ainf F) σ J h : GL (Fin (2 * r + k + 1)) (Ainf F ⊗[F] E)) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) (Ainf F ⊗[F] E))).map (θ w) * (A w)⁻¹)) ∂α = ∏ w, ∫⁻ g, Ψ w g ∂(μw w) := by
  intro F E _ _ _ _ _ σ k r J A μw θ α hcm hJ hA hμ hθ hα
  have hdet : ∀ w, IsUnit (A w).det := by
    intro w
    have h1 := congrArg Matrix.det (hA w)
    have h2 : (J.map w.embedding).det ≠ 0 := by
      have := (w.embedding : E →+* ℂ).map_det J
      rw [RingHom.mapMatrix_apply] at this
      rw [← this]
      exact (map_ne_zero _).2 hJ.2
    rw [← h1, Matrix.det_mul] at h2
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h2)
  refine ⟨hdet, fun Ψ hΨ => ?_⟩
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (HA (Ainf F) σ J) := ⟨rfl⟩
  have hc : ∀ w, Continuous (θ w) := fun w =>
    IsModuleTopology.continuous_of_ringHom (R := Ainf F) (θ w) (hθ w).2
  let m : HA (Ainf F) σ J → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) (Ainf F ⊗[F] E) :=
    fun h => (HA.mat (Ainf F) σ J h : GL (Fin (2 * r + k + 1)) (Ainf F ⊗[F] E))
  have hmc : Continuous m := Units.continuous_val.comp continuous_subtype_val
  let ρ : HA (Ainf F) σ J → InfinitePlace E → Mt k r := fun h w =>
    Matrix.of.symm (A w * (m h).map (θ w) * (A w)⁻¹)
  have hρc : Continuous ρ := continuous_pi fun w =>
    ((continuous_const.matrix_mul (hmc.matrix_map (hc w))).matrix_mul continuous_const :
      Continuous fun h => A w * (m h).map (θ w) * (A w)⁻¹)
  have hρ : Measurable ρ := hρc.measurable
  refine lintegral_comp_prod α ρ hρ (fun B hB => ?_) Ψ hΨ
  have hs : {h : HA (Ainf F) σ J | ∀ w, ∃ b ∈ B w, Matrix.of b * A w = A w * (m h).map (θ w)} =
      ρ ⁻¹' Set.pi Set.univ B := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi]
    refine forall_congr' fun w => ⟨?_, fun hw => ⟨_, hw, ?_⟩⟩
    · rintro ⟨b, hb, e⟩
      have : ρ h w = b := by
        simp only [ρ]
        rw [← e, Matrix.mul_nonsing_inv_cancel_right _ _ (hdet w), Equiv.symm_apply_apply]
      rwa [this]
    · simp only [ρ]
      rw [Equiv.apply_symm_apply, Matrix.nonsing_inv_mul_cancel_right _ _ (hdet w)]
  rw [← hs]
  refine hα B hB ?_
  rw [hs]
  exact hρ (MeasurableSet.univ_pi hB)

end GlobalTheory.SnMass.Push
