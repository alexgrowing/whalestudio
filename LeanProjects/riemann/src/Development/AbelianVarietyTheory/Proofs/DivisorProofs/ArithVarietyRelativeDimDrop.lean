import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory

theorem dim_ne_zero_of_isProjOver {k : Type} [CommRing k] {Z : Scheme.{0}} (q : Z ⟶ Sp k)
    [IsIntegral Z] (hq : IsProjOver q) (hfin : Module.Finite ℤ k) (hc : CharZero Γ(Z, ⊤)) :
    topologicalKrullDim Z ≠ 0 := fun h0 => by
  obtain ⟨N, j, _, hj⟩ := hq
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hfin)
  let t := q ≫ spMap (Int.castRingHom k)
  have : Flat t := (flat_int_iff_charZero t).2 hc
  obtain ⟨z, -, hz⟩ := Flat.generalizingMap t (genericPoint_specializes (t (genericPoint Z)))
  have hs : Set.range t = Set.univ := by
    rw [← t.isClosedMap.isClosed_range.closure_eq]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec (Sp ℤ)).def.ge.trans
      (closure_mono (Set.singleton_subset_iff.2 ⟨z, hz⟩)))
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (TopologicalSpace.IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)
  have hs' := Set.range_eq_univ.1 hs
  obtain ⟨a, ha⟩ := hs' (⊥ : PrimeSpectrum ℤ)
  obtain ⟨b, hb⟩ := hs' (⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2
    Int.prime_two⟩ : PrimeSpectrum ℤ)
  have e := congrArg PrimeSpectrum.asIdeal (hb.symm.trans (((hu b).trans (hu a).symm) ▸ ha))
  exact two_ne_zero (Ideal.span_singleton_eq_bot.1 e)

theorem isArithVar_of_surjective_dim_succ : ∀ (k : Type) [CommRing k] (Y Y₁ : Scheme.{0}) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k) (ρ : Y ⟶ Y₁) (D : ℕ),
    ρ ≫ q₁ = p → IsArithVar p D → IsIntegral Y₁ → IsProjOver q₁ → Surjective ρ →
    topologicalKrullDim Y = topologicalKrullDim Y₁ + 1 → ∃ d₁ : ℕ, D = d₁ + 1 ∧ IsArithVar q₁ d₁ := by
  intro k _ Y Y₁ p q₁ ρ D hρ hX hI hP _ hd
  have hcY : CharZero Γ(Y, ⊤) := hX.charZero
  have hc : CharZero Γ(Y₁, ⊤) := (ρ.appTop).hom.charZero
  have hdim : topologicalKrullDim Y₁ = (D : ℕ) := by
    rw [hX.dim_eq] at hd
    generalize topologicalKrullDim Y₁ = a at hd ⊢
    induction a with
    | bot => exact absurd hd (by simp)
    | coe a =>
      induction a with
      | top =>
        exfalso
        have e1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
        rw [e1] at hd
        first
          | exact ENat.coe_ne_top _ (WithBot.coe_inj.1 hd)
          | exact ENat.coe_ne_top (D + 1) (WithBot.coe_inj.1 hd)
          | (simp at hd; exact WithBot.natCast_ne_top D hd)
          | (simp at hd; exact absurd hd (by simp [WithBot.none_eq_bot]))
      | coe a =>
        congr 2
        have := hd
        norm_cast at this
        omega
  have hD : D ≠ 0 := by
    rintro rfl
    exact dim_ne_zero_of_isProjOver q₁ hP hX.finite hc (by simpa using hdim)
  refine ⟨D - 1, by omega, hX.isDomain, hX.finite, hI, hP, (flat_int_iff_charZero _).2 hc, ?_⟩
  rw [hdim]
  congr 2
  omega

end GlobalTheory
