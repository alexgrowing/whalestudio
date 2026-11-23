import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsPowPrincipal
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProdNormEmbeddingsEqAbsNorm
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ProductFormulaLogNormsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding

open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat

section Place

variable {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]

noncomputable def placeOf (κ : F →+* ℂ_[p]) : HeightOneSpectrum (𝓞 F) where
  asIdeal := GlobalTheory.DatumJets.Place.smallIdeal κ
  isPrime := GlobalTheory.DatumJets.Place.smallIdeal_isPrime κ
  ne_bot := by
    intro hbot
    have hp : ((p : ℕ) : 𝓞 F) ∈ GlobalTheory.DatumJets.Place.smallIdeal κ := by
      rw [GlobalTheory.DatumJets.Place.mem_smallIdeal]
      simpa using GlobalTheory.DatumJets.Place.norm_p_lt_one (p := p)
    rw [hbot, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

theorem mem_placeOf (κ : F →+* ℂ_[p]) (y : 𝓞 F) :
    y ∈ (placeOf κ).asIdeal ↔ ‖κ (y : F)‖ < 1 := Iff.rfl

theorem valuation_placeOf_le_one_iff (κ : F →+* ℂ_[p]) (a : F) :
    (placeOf κ).valuation F a ≤ 1 ↔ ‖κ a‖ ≤ 1 :=
  ⟨fun h => GlobalTheory.MomPlace.norm_le_one_of_valuation F p κ (placeOf κ) (mem_placeOf κ) a h,
    fun h => GlobalTheory.DatumJets.Place.valuation_le_one_of_norm κ (placeOf κ) (mem_placeOf κ) a h⟩

theorem norm_eq_one_of_valuation_eq_one (κ : F →+* ℂ_[p]) {u : F}
    (hu : (placeOf κ).valuation F u = 1) : ‖κ u‖ = 1 := by
  have h1 : ‖κ u‖ ≤ 1 := (valuation_placeOf_le_one_iff κ u).1 hu.le
  have h2 : ‖κ u⁻¹‖ ≤ 1 := (valuation_placeOf_le_one_iff κ u⁻¹).1 (by simp [hu])
  rw [map_inv₀, norm_inv] at h2
  have h0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have h3 : 0 < ‖κ u‖ := by simp [h0]
  exact le_antisymm h1 ((inv_le_one₀ h3).1 h2)

theorem log_norm_eq_of_valuation (κ : F →+* ℂ_[p]) {π α : F} {n : ℤ}
    (hπ : (placeOf κ).valuation F π = WithZero.exp (-1 : ℤ))
    (hα : (placeOf κ).valuation F α = WithZero.exp (-n)) (hα0 : α ≠ 0) :
    Real.log ‖κ α‖ = n * Real.log ‖κ π‖ := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hu : (placeOf κ).valuation F (α * π ^ (-n)) = 1 := by
    rw [map_mul, map_zpow₀, hα, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have h := norm_eq_one_of_valuation_eq_one κ hu
  rw [map_mul, map_zpow₀, norm_mul, norm_zpow] at h
  have hκπ : ‖κ π‖ ≠ 0 := by simp [hπ0]
  have hκα : ‖κ α‖ ≠ 0 := by simp [hα0]
  have h2 := congrArg Real.log h
  rw [Real.log_mul hκα (zpow_ne_zero _ hκπ), Real.log_zpow, Real.log_one] at h2
  push_cast at h2
  linarith

theorem dvd_absNorm_placeOf (κ : F →+* ℂ_[p]) :
    p ∣ Ideal.absNorm (placeOf κ).asIdeal := by
  refine GlobalTheory.DatumJets.Place.dvd_of_natCast_mem (placeOf κ).asIdeal (placeOf κ).isPrime.ne_top
    Fact.out ?_ (Ideal.absNorm_mem _)
  rw [mem_placeOf]
  simpa using GlobalTheory.DatumJets.Place.norm_p_lt_one (p := p)

end Place

theorem deg_eq_places : ∀ (F : Type) [Field F] [NumberField F] (N : LogNorms F) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), (∀ (p : Nat.Primes) (κ : F →+* ℂ_[p]) (v : HeightOneSpectrum (𝓞 F)) (π : F), (∀ a : F, v.valuation F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → v.valuation F π = WithZero.exp (-1 : ℤ) → N.fin p κ = (r v : ℝ) * Real.log ‖κ π‖) → N.IsAdelic ∧ N.deg = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F →+* ℂ, N.inf σ) / (Module.finrank ℚ F : ℝ) := by
  intro F _ _ N r h
  obtain ⟨M, α, hM, hα, hn⟩ := exists_pow_principal F r
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hfin : ∀ (p : Nat.Primes) (κ : F →+* ℂ_[p]), ∃ π : F,
      N.fin p κ = (r (placeOf κ) : ℝ) * Real.log ‖κ π‖ ∧
        (placeOf κ).valuation F π = WithZero.exp (-1 : ℤ) := by
    intro p κ
    obtain ⟨π, hπ⟩ := (placeOf κ).valuation_exists_uniformizer F
    exact ⟨π, h p κ _ π (valuation_placeOf_le_one_iff κ) hπ, hπ⟩
  have key : ∀ (p : Nat.Primes) (κ : F →+* ℂ_[p]), (M : ℝ) * N.fin p κ = Real.log ‖κ α‖ := by
    intro p κ
    obtain ⟨π, h1, hπ⟩ := hfin p κ
    obtain ⟨m, hm, hv⟩ := hn (placeOf κ)
    rw [log_norm_eq_of_valuation κ hπ hv hα, h1]
    have hm' : (m : ℝ) = M * (r (placeOf κ) : ℝ) := by exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hm
    rw [hm']
    ring
  have hadel : N.IsAdelic := by
    have hS : ((r.support.biUnion fun v => (Ideal.absNorm v.asIdeal).primeFactors : Finset ℕ) : Set ℕ).Finite :=
      Finset.finite_toSet _
    refine (hS.preimage (f := fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn).subset ?_
    rintro p ⟨κ, hκ⟩
    obtain ⟨π, h1, -⟩ := hfin p κ
    have hr : r (placeOf κ) ≠ 0 := by
      intro h0
      exact hκ (by rw [h1, h0]; simp)
    simp only [Set.mem_preimage, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Nat.mem_primeFactors]
    refine ⟨placeOf κ, Finsupp.mem_support_iff.2 hr, p.2, dvd_absNorm_placeOf κ, ?_⟩
    have := NumberField.HeightOneSpectrum.one_lt_absNorm (placeOf κ)
    omega
  refine ⟨hadel, ?_⟩
  let n : HeightOneSpectrum (𝓞 F) →₀ ℤ := r.mapRange (fun q => ⌊(M : ℚ) * q⌋) (by simp)
  have hnv : ∀ v, ((n v : ℤ) : ℚ) = M * r v := by
    intro v
    obtain ⟨m, hm, -⟩ := hn v
    simp [n, ← hm]
  have hn' : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F α = WithZero.exp (-(n v)) := by
    intro v
    obtain ⟨m, hm, hv⟩ := hn v
    have : n v = m := by
      have := hnv v
      rw [← hm] at this
      exact_mod_cast this
    rw [this]
    exact hv
  have h1 := sum_log_embeddings_eq F n α hα hn'
  have h2 := (GlobalTheory.T.product_formula_log_norms F α hα).2
  have h3 : ∀ p, (LogNorms.ofElt α).finSum p = M * N.finSum p := by
    intro p
    simp only [LogNorms.finSum, LogNorms.ofElt, Finset.mul_sum, key]
  have hsupp : (Function.support N.finSum).Finite := by
    refine Set.Finite.subset hadel ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_setOf_eq, not_exists, not_not] at hc
    exact hp (by simp [LogNorms.finSum, hc])
  have h4 : ∑ᶠ p, (LogNorms.ofElt α).finSum p = M * ∑ᶠ p, N.finSum p := by
    simp_rw [h3]
    rw [mul_finsum]
  have h5 : (n.sum fun v k => (k : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) =
      M * r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
    rw [Finsupp.sum_mapRange_index (by simp), Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h6 : ((⌊(M : ℚ) * r v⌋ : ℤ) : ℝ) = M * (r v : ℝ) := by
      have h7 := hnv v
      have h8 : n v = ⌊(M : ℚ) * r v⌋ := by simp [n]
      rw [h8] at h7
      exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) h7
    rw [h6]
    ring
  have h6 : ∑ᶠ p, N.finSum p = -(r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) := by
    apply mul_left_cancel₀ hMR
    rw [← h4, mul_neg, ← h5, ← h1]
    linarith
  rw [LogNorms.deg, h6]
  congr 1
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
