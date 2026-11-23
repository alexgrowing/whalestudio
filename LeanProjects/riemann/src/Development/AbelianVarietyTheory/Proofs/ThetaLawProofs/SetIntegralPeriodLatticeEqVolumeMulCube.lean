import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem setIntegral_periodic_eq_measure_mul_cube {E I : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]
    (ν : Measure E) [ν.IsAddHaarMeasure] (T : (I → ℝ) ≃L[ℝ] E) (Λ : Submodule ℤ E)
    (hΛ : ∀ p, T p ∈ Λ ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = p i)
    (Fd : Set E) (hFd : IsAddFundamentalDomain Λ Fd ν)
    (F : E → ℝ) (hF : ∀ (l : Λ) z, F (z + l) = F z) :
    ∫ z in Fd, F z ∂ν = (ν Fd).toReal *
      ∫ p in Set.pi Set.univ (fun _ : I => Set.Ico (0 : ℝ) 1), F (T p) := by
  classical
  set b : Module.Basis I ℝ E := (Pi.basisFun ℝ I).map T.toLinearEquiv with hb
  have hrepr : ∀ p i, b.repr (T p) i = p i := by
    intro p i
    simp [hb]
  have hspan : Λ = Submodule.span ℤ (Set.range b) := by
    ext z
    obtain ⟨p, rfl⟩ := T.surjective z
    rw [hΛ, Module.Basis.mem_span_iff_repr_mem]
    simp [hrepr]
  subst hspan
  have hcell := ZSpan.isAddFundamentalDomain b ν
  have hpre : T ⁻¹' ZSpan.fundamentalDomain b
      = Set.pi Set.univ (fun _ : I => Set.Ico (0 : ℝ) 1) := by
    ext p
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, hrepr, Set.mem_pi, Set.mem_univ,
      true_imp_iff]
  have hcount : Countable (Submodule.span ℤ (Set.range b)) := inferInstance
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) E ν :=
    ⟨fun c s _ => measure_preimage_add ν (c : E) s⟩
  have h1 : ∫ z in Fd, F z ∂ν = ∫ z in ZSpan.fundamentalDomain b, F z ∂ν :=
    hFd.setIntegral_eq hcell (fun l z => by
      have := hF l z
      rw [add_comm] at this
      exact this)
  have h2 : ν Fd = ν (ZSpan.fundamentalDomain b) := hFd.measure_eq hcell
  let e : (I → ℝ) ≃ᵐ E := T.toHomeomorph.toMeasurableEquiv
  have he : (e : (I → ℝ) → E) = T := rfl
  haveI : (Measure.map T (volume : Measure (I → ℝ))).IsAddHaarMeasure :=
    T.isAddHaarMeasure_map _
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • Measure.map e (volume : Measure (I → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν (Measure.map T volume)⟩
  have h3 : ν (ZSpan.fundamentalDomain b) = c := by
    rw [hc, Measure.smul_apply, e.map_apply, he, hpre, Real.volume_pi_Ico]
    simp
  rw [h1, h2, h3, hc, Measure.restrict_smul, integral_smul_nnreal_measure, setIntegral_map_equiv,
    he, hpre]
  simp [NNReal.smul_def]

theorem setIntegral_periodLattice_eq_volume_mul_cube :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    ∀ F : (Fin g → ℂ) → ℝ, (∀ (l : Λ) z, F (z + l) = F z) →
    ∫ z in Fd, F z = (volume Fd).toReal * ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
      F (φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ)))) := by
  intro g Λ φ τ hτ hΛ Fd hFd F hF
  let L : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun p => φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ)))
      map_add' := fun p q => by
        rw [← map_add]
        congr 1
        ext i
        simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c p => by
        have : ∀ v : Fin g → ℂ, c • v = (c : ℂ) • v := fun v => by ext i; simp
        rw [RingHom.id_apply, this, ← map_smul]
        congr 1
        ext i
        simp [Matrix.mulVec, dotProduct, mul_add, Finset.mul_sum, mul_left_comm] }
  have hL : ∀ p, L p = φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ))) :=
    fun _ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL, LinearEquiv.map_eq_zero_iff] at hp
    have him : (τ.map Complex.im).mulVec (fun i => p (.inr i)) = 0 := by
      ext i
      have := congrArg Complex.im (congrFun hp i)
      simpa [Matrix.mulVec, dotProduct] using this
    have hr : (fun i => p (.inr i)) = 0 :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hτ.isUnit) (by rw [him, Matrix.mulVec_zero])
    have hr' : ∀ i, p (.inr i) = 0 := fun i => congrFun hr i
    ext (i | i)
    · have := congrFun hp i
      simpa [Matrix.mulVec, dotProduct, hr'] using this
    · exact hr' i
  have hdim : Module.finrank ℝ (Fin g ⊕ Fin g → ℝ) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  let T : (Fin g ⊕ Fin g → ℝ) ≃L[ℝ] (Fin g → ℂ) :=
    (L.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hT : ∀ p, T p = L p := fun _ => rfl
  refine setIntegral_periodic_eq_measure_mul_cube volume T Λ (fun p => ?_) Fd hFd F hF
  rw [hT, hL, hΛ]
  constructor
  · rintro ⟨m, n, h⟩
    have : L p = L (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) := by
      rw [hL, hL, h]
      simp
    have hp := hinj this
    rintro (i | i)
    · exact ⟨m i, by simp [hp]⟩
    · exact ⟨n i, by simp [hp]⟩
  · intro h
    choose k hk using h
    refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
    simp [← hk]

end GlobalTheory
