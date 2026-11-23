import Development.WeilBound.ThetaLifts.TowerModels.PlaneLat

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_adapted_pair (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) {ε : E}
    (hε : ε = 1 ∨ ε = -1) (hJ : ∀ i j, σ (J j i) = ε * J i j) (D : Submodule (𝓞 E) E) (hD1 : (1 : E) ∈ D)
    (L : Submodule (𝓞 E) (Fin n → E)) (hlat : L.IsLattice E) (hd : ∀ y, y ∈ L ↔ ∀ x ∈ L, form σ J y x ∈ D)
    (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1) (P : Finset (Pl F)) (τ : ∀ v : P, E →ₐ[F] Fv F v)
    (hDτ : ∀ v, ∀ c ∈ D, Valued.v (τ v c) ≤ 1) (x₀ : Fin n → E) (hx₀ : x₀ ≠ 0) (hxx₀ : form σ J x₀ x₀ = 0) :
    ∃ x y : Fin n → E, form σ J x x = 0 ∧ form σ J y y = 0 ∧ form σ J x y = 1 ∧
      (∀ z ∈ L, form σ J z x • y ∈ L ∧ form σ J z y • x ∈ L) ∧
      ∀ v : P, ((∀ c : E, c • x ∈ L → Valued.v (τ v c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ L → Valued.v (τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ v c) = 1) := by
  classical
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hεv : ∀ v, Valued.v (τ v ε) = 1 := fun v => by rcases hε with rfl | rfl <;> simp
  have hεD : ∀ a ∈ D, ε * a ∈ D := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have sw : ∀ a b, form σ J b a = ε * σ (form σ J a b) := fun a b => by
    rw [form_swap h hJ, ← mul_assoc, hεε, one_mul]
  have hne : ∃ z ∈ L, formL (σ := σ) J x₀ z ≠ 0 := by
    by_contra H
    push Not at H
    have h0 : formL (σ := σ) J x₀ = 0 := LinearMap.ext_on hlat.span_eq_top fun z hz => H z hz
    have h1 : J *ᵥ (fun i => σ (x₀ i)) = 0 := by
      funext k
      have := LinearMap.congr_fun h0 (Pi.single k 1)
      simpa [formL, form] using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1
    exact hx₀ (funext fun i => by simpa using congrFun h2 i)
  let S : Finset (HeightOneSpectrum (𝓞 E)) :=
    Finset.univ.image (fun v : P => splitPrime (τ v)) ∪ Finset.univ.image (fun v : P => splitPrime ((τ v).comp σ))
  obtain ⟨z₀, hz₀, hc0, hmax⟩ := exists_max_val L hlat.fg (formL (σ := σ) J x₀) hne S
  change form σ J z₀ x₀ ≠ 0 at hc0
  set c₀ := form σ J z₀ x₀ with hc₀
  obtain ⟨x, hxx, hz₀x, hle⟩ : ∃ x, form σ J x x = 0 ∧ form σ J z₀ x = 1 ∧
      ∀ w ∈ S, ∀ z ∈ L, w.valuation E (form σ J z x) ≤ 1 := by
    refine ⟨σ c₀⁻¹ • x₀, by rw [form_smul_left, form_smul_right, hxx₀]; simp,
      by rw [form_smul_right, sigma_sigma h, inv_mul_cancel₀ hc0], fun w hw z hz => ?_⟩
    rw [form_smul_right, sigma_sigma h, map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hmax w hw z hz) zero_le
  obtain ⟨y, hyy, hxy, hL⟩ := exists_partner h hε hJ D L hlat.fg hd θ hθ x hxx z₀ hz₀ (by rw [hz₀x]; exact one_ne_zero)
  have hyx : form σ J y x = ε := by rw [sw, hxy, map_one, mul_one]
  refine ⟨x, y, hxx, hyy, hxy, hL, fun v => ⟨⟨fun c hc => ?_, ?_⟩, fun c hc => ?_, 1, ?_, by simp⟩⟩
  · have := hεD _ ((hd _).1 hc z₀ hz₀)
    rw [form_smul_left, sw z₀ x, hz₀x, map_one, mul_one, mul_left_comm, hεε, mul_one] at this
    exact hDτ v c this
  · obtain ⟨d, hdw, hdC⟩ := exists_denom (L.map ((formL (σ := σ) J x).restrictScalars (𝓞 E))) (hlat.fg.map _)
      (splitPrime ((τ v).comp σ)) (by
        rintro _ ⟨z, hz, rfl⟩
        exact hle _ (by simp [S]) z hz)
    refine ⟨σ d, (hd _).2 fun z hz => ?_, ?_⟩
    · obtain ⟨o, ho⟩ := hdC _ ⟨z, hz, rfl⟩
      change (d : E) * form σ J z x = o at ho
      rw [form_smul_left, sw z x, mul_left_comm, ← map_mul, ho]
      refine hεD _ ?_
      have := D.smul_mem (conjInt σ o) hD1
      rwa [← algebraMap_smul E, smul_eq_mul, mul_one] at this
    · change Valued.v (((τ v).comp σ) d) = 1
      rw [valued_apply_eq_valuation]
      exact ((splitPrime ((τ v).comp σ)).valuation_eq_one_iff_notMem (K := E)).2 hdw
  · have := hle (splitPrime (τ v)) (by simp [S]) _ hc
    rwa [form_smul_left, hyx, ← valued_apply_eq_valuation, map_mul, map_mul, hεv, mul_one] at this
  · have := (hL z₀ hz₀).1
    rwa [hz₀x] at this

end PositivityTheory.ThKG.Tow.Pln

end
