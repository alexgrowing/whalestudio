import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerArchimedeanIntegralUnfoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanEigenvectorIdeleMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanParabolicFixedDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementCompositionRuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviUnipotentProductDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadicalAltBis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

theorem GlobalTheory.IwasawaConeA.kInt_cone_right_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))),
    μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ m : (AE F E)ˣ → UA σ G.V.J, (∀ l ∈ idelesAt E (evI F), IsLevi (W₁ := G₁.V) H l 1 (m l) ∧ m l ∈ UAt σ G.V (evI F)) →
    ∀ L : UA σ G.V.J → ℂ, ContinuousOn L (UAt σ G.V (evI F)) →
    (∀ n ∈ unip σ G.V H, n ∈ UAt σ G.V (evI F) → ∀ x ∈ UAt σ G.V (evI F), L (n * x) = L x) →
    (∀ (g₀ : UA σ G₁.V.J) (g' : UA σ G.V.J), IsLevi H 1 g₀ g' → g' ∈ UAt σ G.V (evI F) → g₀ ∈ UAt σ G₁.V (evI F) →
      ∀ x ∈ UAt σ G.V (evI F), L (g' * x) = L x) →
    (∀ g ∈ UAt σ G.V (evI F), Integrable (fun p : KAt K (evI F) × idelesAt E (evI F) =>
      L (m p.2.1⁻¹ * p.1.1 * g) * (((absE F E p.2.1 : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ)) (μK.prod μ)) →
    ∀ g ∈ UAt σ G.V (evI F),
      ∫ k, ∫ l, L (m l.1⁻¹ * k.1 * g) * (((absE F E l.1 : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) ∂μ ∂μK =
        ∫ k, ∫ l, L (m l.1⁻¹ * k.1) * (((absE F E l.1 : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) ∂μ ∂μK := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ K hK μK μ hμK hμ m hm L _hLc hN hLev hint g hg
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  have hA : H.IsAdapted σ B G.V G₁.V 0 (b + 1) := hC.hH
  have hV := hG.hV
  have hV₁ := hG₁.hV

  set w : idelesAt E (evI F) → ℂ := fun l => (((absE F E l.1 : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) with hw
  set Ψ : UA σ G.V.J → ℂ := fun x => ∫ l, L (m l.1⁻¹ * x) * w l ∂μ with hΨ
  have hw_mul : ∀ l l' : idelesAt E (evI F), w (l * l') = w l * w l' := by
    intro l l'
    simp only [hw, Subgroup.coe_mul, map_mul, NNReal.coe_mul]
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    push_cast; ring

  have hequiv : ∀ p ∈ UAt σ G.V (evI F), ∀ x ∈ UAt σ G.V (evI F), ∀ t : (AE F E)ˣ,
      mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      Ψ (p * x) = (((absE F E t : ℝ) ^ (b + 1) : ℝ) : ℂ) * Ψ x := by
    intro p hp x hx t hpt
    have ht : t ∈ idelesAt E (evI F) := GlobalTheory.T.archimedean_eigenvector_idele_mem F E σ B b G.V G₁.V H 0 (b + 1) hA p hp t hpt
    set T : idelesAt E (evI F) := ⟨t, ht⟩ with hT
    obtain ⟨hmt, hmtU⟩ := hm t ht

    have hp' : (m t)⁻¹ * p ∈ UAt σ G.V (evI F) :=
      (UAtSub σ G.V (evI F)).mul_mem ((UAtSub σ G.V (evI F)).inv_mem hmtU) hp
    have hfix : mat ((m t)⁻¹ * p) *ᵥ incV F H.x = incV F H.x := by
      have h1 : mat (m t) *ᵥ incV F H.x = t.1 • incV F H.x := hmt.1
      have h2 : mat (m t)⁻¹ *ᵥ (mat (m t) *ᵥ incV F H.x) = incV F H.x := by
        rw [Matrix.mulVec_mulVec, ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
      rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hpt, Matrix.mulVec_smul]
      rw [h1, Matrix.mulVec_smul] at h2
      exact h2
    obtain ⟨n, hnU, hnA, g₀, hg₀, g', hg', hg'A, hdec⟩ :=
      GlobalTheory.T.archimedean_parabolic_fixed_decomposition F E σ B b G.V G₁.V H 0 (b + 1) (b + 2 - G.p) G.p (b - G₁.p) G₁.p hB hV hV₁ hA _ hp' hfix
    have hp_eq : p = m t * n * g' := by
      rw [mul_assoc, ← hdec, mul_inv_cancel_left]

    have hpt' : ∀ l : idelesAt E (evI F), L (m l.1⁻¹ * (p * x)) = L (m (T⁻¹ * l).1⁻¹ * x) := by
      intro l
      have hs : (T⁻¹ * l).1⁻¹ = l.1⁻¹ * t := by
        simp [hT, mul_comm]
      have hsI : (T⁻¹ * l).1⁻¹ ∈ idelesAt E (evI F) := (idelesAt E (evI F)).inv_mem (T⁻¹ * l).2
      have hlI : l.1⁻¹ ∈ idelesAt E (evI F) := (idelesAt E (evI F)).inv_mem l.2
      obtain ⟨hms, hmsU⟩ := hm _ hsI
      obtain ⟨hml, -⟩ := hm _ hlI
      have hmul : m l.1⁻¹ * m t = m (T⁻¹ * l).1⁻¹ :=
        GlobalTheory.T.levi_element_composition_rule F E σ B b G.V G₁.V H 0 (b + 1) (b + 2 - G.p) G.p (b - G₁.p) G₁.p hB hV hV₁ hA _ _ _ _ _ hml hmt (hs ▸ hms)
      set s := m (T⁻¹ * l).1⁻¹ with hsdef
      have hcomm : s * g' = g' * s :=
        GlobalTheory.T.levi_unipotent_product_decomposition F E σ B b G.V G₁.V H 0 (b + 1) (b + 2 - G.p) G.p (b - G₁.p) G₁.p hB hV hV₁ hA _ _ _ _ hms hg'
      have hconj : s * n * s⁻¹ ∈ unip σ G.V H := GlobalTheory.T.levi_normalizes_unipotent_radical' F E σ b G.V G₁.V H _ _ hms n hnU
      have hconjU : s * n * s⁻¹ ∈ UAt σ G.V (evI F) :=
        (UAtSub σ G.V (evI F)).mul_mem ((UAtSub σ G.V (evI F)).mul_mem hmsU hnA) ((UAtSub σ G.V (evI F)).inv_mem hmsU)
      have hsx : s * x ∈ UAt σ G.V (evI F) := (UAtSub σ G.V (evI F)).mul_mem hmsU hx
      have hrest : s * g' * x ∈ UAt σ G.V (evI F) := by
        rw [hcomm, mul_assoc]; exact (UAtSub σ G.V (evI F)).mul_mem hg'A hsx
      calc L (m l.1⁻¹ * (p * x)) = L ((s * n * s⁻¹) * (s * g' * x)) := by
            congr 1; rw [hp_eq, ← hmul]; group
        _ = L (s * g' * x) := hN _ hconj hconjU _ hrest
        _ = L (g' * (s * x)) := by rw [hcomm, mul_assoc]
        _ = L (s * x) := hLev g₀ g' hg' hg'A hg₀ _ hsx
    have hwT : w T = (((absE F E t : ℝ) ^ (b + 1) : ℝ) : ℂ) := by
      simp only [hw, hT, Real.rpow_natCast]
    calc Ψ (p * x) = ∫ l, L (m (T⁻¹ * l).1⁻¹ * x) * w l ∂μ := by
          simp only [hΨ]; congr 1; funext l; rw [hpt' l]
      _ = ∫ l, L (m (T⁻¹ * (T * l)).1⁻¹ * x) * w (T * l) ∂μ :=
          (integral_mul_left_eq_self (fun l => L (m (T⁻¹ * l).1⁻¹ * x) * w l) T).symm
      _ = w T * Ψ x := by
          simp only [hΨ, inv_mul_cancel_left, hw_mul]
          rw [← integral_const_mul]; congr 1; funext l; ring
      _ = _ := by rw [hwT]

  have hint' : ∀ h ∈ UAt σ G.V (evI F), Integrable (fun k : KAt K (evI F) => Ψ (k.1 * h)) μK := by
    intro h hh
    have := (hint h hh).integral_prod_left
    simpa only [hΨ, hw, mul_assoc] using this
  have key := GlobalTheory.T.stabilizer_archimedean_integral_unfold F E σ B b G.V G₁.V H 0 (b + 1) (b + 2 - G.p) G.p hB hV hA K hK μK hμK Ψ hint' hequiv g hg
  simpa only [hΨ, hw, mul_assoc] using key
