import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LatticeIndex

theorem intersected_trivAt_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (ℓ : ℕ), ℓ.Prime → Λ.TrivAt ℓ → ∀ la : HeightOneSpectrum (𝓞 c.F), (ℓ : 𝓞 c.F) ∈ la.asIdeal → ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → la.valuation c.F s ≤ 1 := by
  intro E _ _ _ H Dw l c n Λ ℓ hℓ hT la hla s hs
  obtain ⟨k, hk, hkLa, hkstd⟩ := hT
  set w := la.valuation c.F with hwdef
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => la.valuation_le_one r
  have hwi : ∀ x : c.F, IsIntegral ℤ x → w x ≤ 1 := fun x hx => hw ⟨x, hx⟩
  have hk1 : w (k : c.F) = 1 := by
    have h := (la.valuation_eq_one_iff_notMem (K := c.F) (r := (k : 𝓞 c.F))).2 ?_
    · simpa using h
    · intro hm
      obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 c.F) hk)
      have : (1 : 𝓞 c.F) ∈ la.asIdeal := by
        rw [← hab]
        exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hm) (la.asIdeal.mul_mem_left _ hla)
      exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hkv : ∀ τ : E →+* ℂ, w (embF c τ (k : E)) = 1 := fun τ => by rw [map_natCast]; exact hk1
  have hsm : ∀ v : Fin n → Fin n → E,
      (Matrix.of fun i j => ((k : 𝓞 E) • v j) i) = (k : E) • Matrix.of fun i j => v j i := by
    intro v; ext i j; simp [Algebra.smul_def]
  have hdetk : ∀ v : Fin n → Fin n → E,
      Matrix.det (Matrix.of fun i j => ((k : 𝓞 E) • v j) i) = (k : E) ^ n * Matrix.det (Matrix.of fun i j => v j i) := by
    intro v; rw [hsm, Matrix.det_smul, Fintype.card_fin]

  have hei : ∀ i : Fin n, (k : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Λ.Ln := fun i =>
    ⟨hkstd (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (single_std i)),
      Submodule.smul_mem _ _ (single_std i)⟩
  have hdete : Matrix.det (Matrix.of fun i j => ((k : 𝓞 E) • (Pi.single j 1 : Fin n → E)) i) = (k : E) ^ n := by
    rw [hdetk, det_single, _root_.mul_one]
  have hLa : ∀ τ : E →+* ℂ, HasMax w (idealAt c Λ.La τ) 1 := fun τ => by
    refine hasMax_span hw ?_ ⟨_, ⟨_, ⟨_, fun i => (hei i).1, rfl⟩, rfl⟩, ?_⟩
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      have hu : ∀ i, (k : 𝓞 E) • v i ∈ stdLat E n := fun i =>
        hkLa (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hv i))
      obtain ⟨r, hr⟩ := det_std hu
      rw [hdetk] at hr
      have h := hwi _ (map_isIntegral_int (embF c τ) r.isIntegral_coe)
      rw [hr] at h
      simp only [map_mul, map_pow, hkv, one_pow, _root_.one_mul] at h
      exact h
    · rw [hdete]; simp only [map_pow, hkv, one_pow]
  have hLn : ∀ τ : E →+* ℂ, HasMax w (idealAt c Λ.Ln τ) 1 := fun τ => by
    refine hasMax_span hw ?_ ⟨_, ⟨_, ⟨_, hei, rfl⟩, rfl⟩, ?_⟩
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact (hLa τ).1 _ (Submodule.subset_span ⟨_, ⟨v, fun i => (hv i).1, rfl⟩, rfl⟩)
    · rw [hdete]; simp only [map_pow, hkv, one_pow]
  have hb : HasMax w (Submodule.span (𝓞 c.F) {s}) (w s) := hasMax_span hw (by simp) (by simp)
  have e1 := hb.mul (hasMax_prod hw Finset.univ _ _ fun τ => (hLn τ).pow hw (Dw.mult τ))
  have e2 := hasMax_prod hw Finset.univ _ _ fun τ => (hLa τ).pow hw (Dw.mult τ)
  obtain ⟨y, hy, hyw⟩ := e1.2
  have := e2.1 y (hs hy)
  simpa [hyw] using this

end GlobalTheory.LatticeIndex
