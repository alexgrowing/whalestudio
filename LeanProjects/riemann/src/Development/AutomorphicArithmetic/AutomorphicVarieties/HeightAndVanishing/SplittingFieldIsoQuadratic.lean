import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.SplitCharY
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsSqEqNegOfDiscr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

open Polynomial in
private theorem splitting_field_iso_quadratic (p : ℕ) (hp : 0 < p) (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (δ : K) (hδ : δ ^ 2 = -(p : K)) (L : Type) [Field L] [NumberField L]
    [hL : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : Nonempty (L ≃ₐ[ℚ] K) := by
  classical
  set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf
  have hsK : (f.map (algebraMap ℚ K)).Splits := by
    have hfac : f.map (algebraMap ℚ K) = (X + C δ) * (X + C (-δ)) := by
      have hpK : (p : K) = -(δ ^ 2) := by rw [hδ]; ring
      rw [hf, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        map_natCast, hpK]
      simp only [map_neg, map_pow]
      ring
    rw [hfac]
    exact (Splits.X_add_C _).mul (Splits.X_add_C _)
  let φ := IsSplittingField.lift L f hsK
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hLK : Module.finrank ℚ L ≤ 2 :=
    hK ▸ LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hinj
  have hL1 : Module.finrank ℚ L ≠ 1 := by
    intro h1
    have hbt := Subalgebra.bot_eq_top_of_finrank_eq_one (F := ℚ) (E := L) h1
    have hsL := IsSplittingField.splits L f
    have hdeg : (f.map (algebraMap ℚ L)).degree ≠ 0 := by
      rw [Polynomial.degree_map, hf, Polynomial.degree_X_pow_add_C (by norm_num)]
      norm_num
    obtain ⟨r, hr⟩ := hsL.exists_eval_eq_zero hdeg
    have hrm : r ∈ (⊥ : Subalgebra ℚ L) := hbt ▸ Algebra.mem_top
    obtain ⟨q, rfl⟩ := Algebra.mem_bot.mp hrm
    have hq : algebraMap ℚ L (q ^ 2 + p) = 0 := by
      simpa [hf, Polynomial.eval_map] using hr
    have hq0 : q ^ 2 + (p : ℚ) = 0 := (algebraMap ℚ L).injective (by rw [hq, map_zero])
    have hpq : (0 : ℚ) < q ^ 2 + p := by
      have : (0 : ℚ) < p := by exact_mod_cast hp
      positivity
    linarith
  have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have h2 : Module.finrank ℚ L = 2 := by omega
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (h2.trans hK.symm)).1 hinj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem UpperTheory.V.HV.kstar :
    ∀ p : ℕ, p.Prime → p % 4 = 3 → discr (Kstar p) = -(p : ℤ) ∧ IsTotallyComplex (Kstar p) ∧ Module.finrank ℚ (Kstar p) = 2 ∧ ∃ s : Kstar p, s ^ 2 = -(p : Kstar p) := by
  intro p hp h3
  obtain ⟨K, _, _, hK2, hd⟩ := KStar.Consta.exists_quadField hp h3
  obtain ⟨⟨δ, hδ⟩, -⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hK2 hp.ne_zero hd
  haveI : Polynomial.IsSplittingField ℚ (Kstar p) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
    have h := Polynomial.IsSplittingField.splittingField (K := ℚ) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ))
    have h' : Polynomial.IsSplittingField ℚ (Polynomial.SplittingField (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)))
        (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
      convert h
      exact Subsingleton.elim _ _
    exact h'
  obtain ⟨e⟩ := splitting_field_iso_quadratic p hp.pos K hK2 δ hδ (Kstar p)
  have hfr : Module.finrank ℚ (Kstar p) = 2 := e.toLinearEquiv.finrank_eq.trans hK2
  have hdisc : discr (Kstar p) = -(p : ℤ) := by
    rw [NumberField.discr_eq_discr_of_algEquiv (Kstar p) e, hd]
  obtain ⟨hs, htc⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hfr hp.ne_zero hdisc
  exact ⟨hdisc, htc, hfr, hs⟩
