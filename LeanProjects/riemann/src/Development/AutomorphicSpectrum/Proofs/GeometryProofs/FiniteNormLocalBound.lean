import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingsConjugateOfUnitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace GlobalTheory.CompanionTheory.Ar.Br.FinPlace

section Valued

variable {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {N : Type*} [NormedField N]

theorem val_lt_one_iff (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) (a : F) :
    v a < 1 ↔ ‖κ a‖ < 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have hv : 0 < v a := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr ha)
  have hn : 0 < ‖κ a‖ := norm_pos_iff.mpr ((map_ne_zero κ).mpr ha)
  have e := h a⁻¹
  rw [map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hv, inv_le_one₀ hn] at e
  rw [← not_le, ← not_le, e]

theorem norm_le_of_val_le (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) {a b : F} (hb : b ≠ 0)
    (hab : v a ≤ v b) : ‖κ a‖ ≤ ‖κ b‖ := by
  have hv : 0 < v b := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hb)
  have hn : 0 < ‖κ b‖ := norm_pos_iff.mpr ((map_ne_zero κ).mpr hb)
  have e := (h (a / b)).mp (by rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le)
  rw [map_div₀, norm_div] at e
  exact (div_le_one hn).mp e

theorem norm_eq_of_val_eq (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) {a b : F} (hb : b ≠ 0)
    (hab : v a = v b) : ‖κ a‖ = ‖κ b‖ := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact (Valuation.ne_zero_iff v).mpr hb hab.symm
  exact le_antisymm (norm_le_of_val_le v κ h hb hab.le) (norm_le_of_val_le v κ h ha hab.ge)

end Valued

theorem norm_natCast_lt_one_iff (q : Nat.Primes) (n : ℕ) : ‖(n : ℂ_[q])‖ < 1 ↔ (q : ℕ) ∣ n := by
  have e : ‖(n : ℂ_[q])‖ = ‖(n : ℚ_[q])‖ := by
    have h1 := PadicComplex.norm_extends (q : ℕ) ((n : ℚ_[q]) : PadicAlgCl q)
    have h2 := PadicAlgCl.norm_extends (q : ℕ) (n : ℚ_[q])
    simpa using h1.trans h2
  rw [e]
  exact Padic.norm_natCast_lt_one_iff

theorem prime_eq {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    {p q : Nat.Primes} (κ : F →+* ℂ_[p]) (κ₀ : F →+* ℂ_[q]) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1)
    (h₀ : ∀ a, v a ≤ 1 ↔ ‖κ₀ a‖ ≤ 1) : p = q := by
  have h1 : ‖κ ((p : ℕ) : F)‖ < 1 := by
    rw [map_natCast, norm_natCast_lt_one_iff]
  have h2 : ‖κ₀ ((p : ℕ) : F)‖ < 1 := (val_lt_one_iff v κ₀ h₀ _).mp ((val_lt_one_iff v κ h _).mpr h1)
  rw [map_natCast, norm_natCast_lt_one_iff] at h2
  exact Subtype.ext (((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp h2).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem hasFinNorm_of_isometry {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ : FrameFn Xo c} {p : Nat.Primes}
    {κ κ' : c.F →+* ℂ_[p]} {t : ℝ} (g : ℂ_[p] ≃+* ℂ_[p]) (hg : ∀ z, ‖g z‖ = ‖z‖) (hκ : ∀ a, g (κ a) = κ' a)
    (h : HasFinNorm U τ φ p κ t) : HasFinNorm U τ φ p κ' t := by
  have hs : ∀ z, ‖g.symm z‖ = ‖z‖ := fun z => by
    rw [← hg (g.symm z), RingEquiv.apply_symm_apply]
  intro V K _ _ _ _ _ _ j β y v w T tK m m' hj hjβ hF hv hw
  have e := h V K ((g.symm : ℂ_[p] →+* ℂ_[p]).comp j) β y v w T tK m m'
    (fun a => by
      rw [← hj a]
      simp only [RingHom.comp_apply, RingHom.coe_coe, hs])
    (by
      ext a
      have h1 : j (β a) = κ' a := by rw [← hjβ]; rfl
      simp only [RingHom.comp_apply, RingHom.coe_coe, h1, ← hκ, RingEquiv.symm_apply_apply]) hF hv hw
  simpa only [RingHom.comp_apply, RingHom.coe_coe, hs] using e

theorem exists_rho_at (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) [NumberField c.F]
    (hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t)
    (la : HeightOneSpectrum (𝓞 c.F)) :
    ∃ r : ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (π : c.F),
      (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) →
      HasFinNorm U τ φ p κ (r * Real.log ‖κ π‖) := by
  by_cases hex : ∃ (p₀ : Nat.Primes) (κ₀ : c.F →+* ℂ_[p₀]) (π₀ : c.F),
      (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ₀ a‖ ≤ 1) ∧ la.valuation c.F π₀ = WithZero.exp (-1 : ℤ)
  · obtain ⟨p₀, κ₀, π₀, hκ₀, hπ₀⟩ := hex
    obtain ⟨t₀, ht₀⟩ := hfin p₀ κ₀
    have hne : π₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ₀
      exact WithZero.exp_ne_zero hπ₀.symm
    have hlt : ‖κ₀ π₀‖ < 1 := (val_lt_one_iff _ κ₀ hκ₀ π₀).mp (by
      rw [hπ₀, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    have hpos : 0 < ‖κ₀ π₀‖ := norm_pos_iff.mpr ((map_ne_zero κ₀).mpr hne)
    have hlog : Real.log ‖κ₀ π₀‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hlt.ne
    refine ⟨t₀ / Real.log ‖κ₀ π₀‖, fun p κ π hκ hπ => ?_⟩
    have hp : p = p₀ := prime_eq (la.valuation c.F) κ κ₀ hκ hκ₀
    subst hp
    obtain ⟨g, hg, hgκ⟩ := GlobalTheory.T.padic_embeddings_conjugate_of_units c.F p κ₀ κ (fun a => (hκ₀ a).symm.trans (hκ a))
    have e : ‖κ π‖ = ‖κ₀ π₀‖ := by
      rw [norm_eq_of_val_eq _ κ hκ hne (hπ.trans hπ₀.symm), ← hgκ, hg]
    rw [e, div_mul_cancel₀ _ hlog]
    exact hasFinNorm_of_isometry g hg hgκ ht₀
  · exact ⟨0, fun p κ π h1 h2 => (hex ⟨p, κ, π, h1, h2⟩).elim⟩

theorem exists_rho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t) → ∃ ρ : HeightOneSpectrum (𝓞 c.F) → ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm U τ φ p κ (ρ la * Real.log ‖κ π‖) := by
  intro E _ _ _ H D l Xo c _ U τ φ hfin
  choose ρ hρ using exists_rho_at U τ φ hfin
  exact ⟨ρ, fun p κ la π h1 h2 => hρ la p κ π h1 h2⟩

end GlobalTheory.CompanionTheory.Ar.Br.FinPlace
