import Development.WeilBound.CoreStatements.SesquilinearFractions.DCompl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def projectionCoeffsAddHom (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (a : Fin p) : D.La →+ E :=
  AddMonoidHom.mk' (fun y => projectionCoeffs D x' y a) (fun y y' => by rw [projectionCoeffs_add]; rfl)

theorem exists_common_denominator_coeffs (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (ℓ : Nat.Primes) (hdet : (gramE D x').det ≠ 0)
    (hlog : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) :
    ∃ m : ℕ, ¬ (ℓ : ℕ) ∣ m ∧ ∀ y a, ∃ g : 𝓞 E, (g : E) = m * projectionCoeffs D x' y a := by
  classical
  have := D.fin
  obtain ⟨k, t, ht⟩ := Module.Finite.exists_fin (R := 𝓞 E) (M := D.La)
  have hpt : ∀ i a, ∃ n : ℕ, ¬ (ℓ : ℕ) ∣ n ∧ ∃ b : 𝓞 E, (n : E) * projectionCoeffs D x' (t i) a = b := fun i a => by
    obtain ⟨n, b, hn, hb⟩ := (GlobalTheory.T.padic_integral_iff_denominator E ℓ _).1 (fun j => padic_norm_projectionCoeffs_le D x' ℓ hdet hlog (t i) a j)
    exact ⟨n, hn, b, hb⟩
  choose n hn b hb using hpt
  refine ⟨∏ i, ∏ a, n i a, ?_, fun y a => ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff (Nat.prime_iff.1 ℓ.2) _).1 h
    obtain ⟨a, -, ha⟩ := (Prime.dvd_finset_prod_iff (Nat.prime_iff.1 ℓ.2) _).1 hi
    exact hn i a ha
  · have hy : y ∈ Submodule.span (𝓞 E) (Set.range t) := ht ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hy
    have hdv : ∀ i, ∃ w : ℕ, ∏ i, ∏ a, n i a = n i a * w := fun i =>
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ a)).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    choose w hw using hdv
    have he : projectionCoeffs D x' (∑ i, c i • t i) a = ∑ i, IsCMField.complexConj E (c i : E) * projectionCoeffs D x' (t i) a := by
      show projectionCoeffsAddHom D x' a (∑ i, c i • t i) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show projectionCoeffs D x' (c i • t i) a = _
      rw [projectionCoeffs_smul, Pi.smul_apply, smul_eq_mul]
    have hmem : ((∏ i, ∏ a, n i a : ℕ) : E) * projectionCoeffs D x' (∑ i, c i • t i) a ∈ (algebraMap (𝓞 E) E).range := by
      rw [he, Finset.mul_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      rw [mul_left_comm, hw i, Nat.cast_mul, mul_comm ((n i a : ℕ) : E), _root_.mul_assoc, hb i a]
      exact Subring.mul_mem _ ⟨H.bar (c i), H.bar_eq (c i)⟩ (Subring.mul_mem _ ⟨(w i : 𝓞 E), by simp⟩ ⟨b i a, rfl⟩)
    obtain ⟨g, hg⟩ := hmem
    exact ⟨g, hg⟩

end GlobalTheory.CompanionTheory.Ar.Fl

end
