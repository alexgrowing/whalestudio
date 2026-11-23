import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightHermitianDerivationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerEqZeroOfVanishOnHighestStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightTensorDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeUnitaryActionStatement

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.Isotypic

variable {n : ℕ}

theorem exists_map_out (H L : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ : Fin n → ℝ)
    (hG : Formalism.REAL.GlRel G) (hK : Formalism.REAL.GlRel K)
    (hGs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ)
    (v : L) (hv0 : v ≠ 0) (hv : Formalism.REAL.KHighest (fun _ => true) K μ v)
    (d : H) (hd : Formalism.REAL.KHighest (fun _ => true) G μ d) :
    ∃ T : L →ₗ[ℂ] H, T v = d ∧ ∀ a b w, T (K a b w) = G a b (T w) := by
  have hsp : ∀ x ∈ Submodule.span ℂ {v}, Formalism.REAL.KHighest (fun _ => true) K μ x := by
    intro x hx
    have hvm : v ∈ hwOf K μ := hv
    have : x ∈ hwOf K μ := (Submodule.span_singleton_le_iff_mem v (hwOf K μ)).2 hvm hx
    exact this
  let f : (Submodule.span ℂ {v}) →ₗ[ℂ] H :=
    ((innerₛₗ ℂ v).comp (Submodule.subtype _)).smulRight ((⟪v, v⟫_ℂ)⁻¹ • d)
  have hf : ∀ x, Formalism.REAL.KHighest (fun _ => true) G μ (f x) := by
    intro x
    have hdm : d ∈ hwOf G μ := hd
    have : f x ∈ hwOf G μ := by
      simp only [f, LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hdm)
    exact this
  obtain ⟨T, hT, hi⟩ := GlobalTheory.T.highest_weight_tensor_decomposition L H K G μ hK hG hKs hGs (Submodule.span ℂ {v}) hsp f hf
  refine ⟨T, ?_, hi⟩
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  have := hT ⟨v, Submodule.mem_span_singleton_self v⟩
  simp only at this
  rw [this]
  simp only [f, LinearMap.smulRight_apply, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply]
  rw [smul_smul, mul_inv_cancel₀ hvv, one_smul]

theorem exists_map_in (H L : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ : Fin n → ℝ)
    (hG : Formalism.REAL.GlRel G) (hK : Formalism.REAL.GlRel K)
    (hGs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ)
    (v : L) (hv : Formalism.REAL.KHighest (fun _ => true) K μ v)
    (D : Submodule ℂ H) (hD : ∀ x ∈ D, Formalism.REAL.KHighest (fun _ => true) G μ x) (φ : D →ₗ[ℂ] ℂ) :
    ∃ P : H →ₗ[ℂ] L, (∀ d : D, P d = φ d • v) ∧ ∀ a b w, P (G a b w) = K a b (P w) := by
  have hf : ∀ x, Formalism.REAL.KHighest (fun _ => true) K μ (φ.smulRight v x) := by
    intro x
    have hvm : v ∈ hwOf K μ := hv
    have : φ.smulRight v x ∈ hwOf K μ := by
      simp only [LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ hvm
    exact this
  obtain ⟨P, hP, hi⟩ := GlobalTheory.T.highest_weight_tensor_decomposition H L G K μ hG hK hGs hKs D hD (φ.smulRight v) hf
  exact ⟨P, fun d => by rw [hP d, LinearMap.smulRight_apply], hi⟩

theorem eq_smul_id_of_apply (L : Type) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (K : Fin n → Fin n → Module.End ℂ L) (hK : Formalism.REAL.GlRel K)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) (v : L)
    (huniq : ∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v)
    (R : L →ₗ[ℂ] L) (hR : ∀ a b w, R (K a b w) = K a b (R w)) (r : ℂ) (hr : R v = r • v) :
    R = r • LinearMap.id := by
  have h0 := GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest L L K K hK hKs (R - r • LinearMap.id)
    (fun a b w => by simp [hR, map_smul]) (fun μ w hw => by
      obtain ⟨c, rfl⟩ := huniq w (fun a b hab => hw.2 a b hab rfl)
      simp [hr, smul_comm c r])
  exact sub_eq_zero.1 h0

theorem map_highest_eq_zero {H L : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup L] [Module ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ μ' : Fin n → ℝ)
    (v : L) (hv0 : v ≠ 0) (hv : Formalism.REAL.KHighest (fun _ => true) K μ' v)
    (huniq : ∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v)
    (P : H →ₗ[ℂ] L) (hP : ∀ a b w, P (G a b w) = K a b (P w))
    (hne : μ ≠ μ') (w : H) (hw : Formalism.REAL.KHighest (fun _ => true) G μ w) : P w = 0 := by
  obtain ⟨c, hc⟩ := huniq (P w) (fun a b hab => by rw [← hP, hw.2 a b hab rfl, map_zero])
  by_contra hne0
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne0 (by simpa using hc)
  apply hne
  funext a
  have h1 : K a a (P w) = (μ a : ℂ) • P w := by rw [← hP, hw.1 a, map_smul]
  rw [hc, map_smul, hv.1 a, smul_comm] at h1
  have h2 : ((μ' a : ℂ) - (μ a : ℂ)) • (c • v) = 0 := by rw [sub_smul, h1, sub_self]
  have h3 : (μ' a : ℂ) - (μ a : ℂ) = 0 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h (smul_ne_zero hc0 hv0)
  have h4 : (μ' a : ℂ) = (μ a : ℂ) := sub_eq_zero.1 h3
  exact (Complex.ofReal_injective h4).symm

theorem map_mem_hwOf {H : Type} [AddCommGroup H] [Module ℂ H]
    (G : Fin n → Fin n → Module.End ℂ H) (μ : Fin n → ℝ) (S : H →ₗ[ℂ] H)
    (hS : ∀ a b w, S (G a b w) = G a b (S w)) (x : H) (hx : x ∈ hwOf G μ) : S x ∈ hwOf G μ :=
  ⟨fun a => by rw [← hS, hx.1 a, map_smul],
    fun a b hab he => by rw [← hS, hx.2 a b hab he, map_zero]⟩

theorem exists_isotypic_projection {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H))
    (G : Fin n → Fin n → Module.End ℂ H) (ν : Fin n → ℤ) :
    Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) →
    (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) →
    Antitone ν →
    ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧ (∀ v ∈ hwOf G (wtR ν), p v = v) ∧
      (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  intro hG hGs hder hν
  obtain ⟨L, _, _, _, σ, K, v, hK, hKs, hσ, hv0, hv, huniq, htr⟩ := GlobalTheory.T.exists_highest_weight_hermitian_derivation ν hν
  have hD : ∀ x ∈ hwOf G (wtR ν), Formalism.REAL.KHighest (fun _ => true) G (wtR ν) x := fun x hx => hx
  let b := Module.finBasis ℂ (hwOf G (wtR ν))
  have ex1 : ∀ j, ∃ T : L →ₗ[ℂ] H, T v = (b j : H) ∧ ∀ a c w, T (K a c w) = G a c (T w) := fun j =>
    exists_map_out H L G K (wtR ν) hG hK hGs hKs v hv0 hv (b j : H) (b j).2
  choose T hTv hTi using ex1
  have ex2 : ∀ j, ∃ P : H →ₗ[ℂ] L, (∀ d : hwOf G (wtR ν), P d = b.coord j d • v) ∧
      ∀ a c w, P (G a c w) = K a c (P w) := fun j =>
    exists_map_in H L G K (wtR ν) hG hK hGs hKs v hv _ hD (b.coord j)
  choose P hPd hPi using ex2
  have hPk : ∀ j k w, P j (ρ k w) = σ k (P j w) := fun j =>
    GlobalTheory.T.derivative_unitary_action H L ρ G hder σ K hσ hKs (P j) (hPi j)
  have hp : ∀ w, (∑ j, T j ∘ₗ P j) w = ∑ j, T j (P j w) := fun w => by
    simp [LinearMap.sum_apply]
  refine ⟨∑ j, T j ∘ₗ P j, ?_, ?_, ?_, ?_⟩
  · intro a c w
    rw [hp, hp, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hPi, hTi]
  · intro d hd
    rw [hp]
    have h1 : ∀ j, T j (P j d) = b.coord j ⟨d, hd⟩ • (b j : H) := fun j => by
      have := hPd j ⟨d, hd⟩
      simp only at this
      rw [this, map_smul, hTv]
    simp only [h1]
    have h2 : ∑ j, b.coord j ⟨d, hd⟩ • b j = ⟨d, hd⟩ := b.sum_repr _
    calc ∑ j, b.coord j ⟨d, hd⟩ • (b j : H)
        = ((∑ j, b.coord j ⟨d, hd⟩ • b j : hwOf G (wtR ν)) : H) := by
          simp only [Submodule.coe_sum, Submodule.coe_smul]
      _ = d := by rw [h2]
  · intro μ w hne hw
    rw [hp]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_highest_eq_zero G K μ (wtR ν) v hv0 hv huniq (P j) (hPi j) hne w hw, map_zero]
  · intro S hS k z hk hz
    have hSD : ∀ x ∈ hwOf G (wtR ν), S x ∈ hwOf G (wtR ν) := map_mem_hwOf G (wtR ν) S hS
    have hj : ∀ j, LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j)) =
        b.coord j ⟨S (b j), hSD _ (b j).2⟩ * weylChar ν z := by
      intro j
      have hR : P j ∘ₗ S ∘ₗ T j = b.coord j ⟨S (b j), hSD _ (b j).2⟩ • LinearMap.id := by
        refine eq_smul_id_of_apply L K hK hKs v huniq _ (fun a c w => ?_) _ ?_
        · simp only [LinearMap.comp_apply]
          rw [hTi, hS, hPi]
        · simp only [LinearMap.comp_apply]
          rw [hTv]
          exact hPd j ⟨S (b j), hSD _ (b j).2⟩
      have e1 : (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j) = ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ T j) ∘ₗ P j := rfl
      have e2 : P j ∘ₗ ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ T j) = σ k ∘ₗ (P j ∘ₗ S ∘ₗ T j) := by
        ext w
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        exact hPk j k _
      rw [e1, LinearMap.trace_comp_comm', e2, hR, LinearMap.comp_smul, LinearMap.comp_id, map_smul,
        htr k z hk hz, smul_eq_mul]
    have hsum : (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (∑ j, T j ∘ₗ P j) =
        ∑ j, (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j) := by
      ext w
      simp [LinearMap.sum_apply, map_sum]
    rw [hsum, map_sum, Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_mul]
    congr 1
    unfold trOn
    rw [dif_pos hSD, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl

end GlobalTheory.CompanionTheory.RealCountG.Isotypic
