import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem exists_root_congr_unit : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)),
    IsPlaceOver A P → ∀ u : 𝓞 E, u ∉ P.asIdeal →
      ∃ ζ : Ω, ζ ^ (normV P - 1) = 1 ∧ A.valuation (ζ - algebraMap E Ω (u : E)) < 1 := by
  intro E Ω _ _ _ _ _ A P hA u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field _
  set q := normV P with hq
  have hqc : q = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    rw [hq, normV, Nat.card_eq_fintype_card]
  have hq1 : 1 < q := by rw [hqc]; exact Fintype.one_lt_card
  set n := q - 1 with hn
  have hn0 : 0 < n := by omega

  have hmem : u ^ n - 1 ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
    have h0 : (Ideal.Quotient.mk P.asIdeal u) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have := FiniteField.pow_card_sub_one_eq_one _ h0
    rwa [← hqc] at this
  have hlt : A.valuation (algebraMap E Ω ((u ^ n - 1 : 𝓞 E) : E)) < 1 := (hA _).mpr hmem
  set a : Ω := algebraMap E Ω (u : E) with ha
  have hcast : algebraMap E Ω ((u ^ n - 1 : 𝓞 E) : E) = a ^ n - 1 := by
    simp [ha]
  rw [hcast] at hlt

  set p : Polynomial Ω := Polynomial.X ^ n - Polynomial.C 1 with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_sub_C 1 hn0.ne'
  have hprod := (IsAlgClosed.splits p).eq_prod_roots_of_monic hmon
  have heval : a ^ n - 1 = (p.roots.map (fun ζ => a - ζ)).prod := by
    have := congrArg (Polynomial.eval a) hprod
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at this
    simp only [hp, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Function.comp_def] at this
    rw [this]
  by_contra hcon
  push_neg at hcon
  have hall : ∀ ζ ∈ p.roots, 1 ≤ A.valuation (a - ζ) := by
    intro ζ hζ
    have hroot : ζ ^ n = 1 := by
      have := (Polynomial.mem_roots hmon.ne_zero).mp hζ
      simpa [hp, sub_eq_zero] using this
    rw [Valuation.map_sub_swap]
    exact hcon ζ hroot
  have : 1 ≤ A.valuation (a ^ n - 1) := by
    rw [heval, map_multiset_prod, Multiset.map_map]
    have key : ∀ s : Multiset Ω, (∀ ζ ∈ s, 1 ≤ A.valuation (a - ζ)) →
        1 ≤ (s.map (A.valuation ∘ fun ζ => a - ζ)).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _; simp
      | cons b s ih =>
        intro h
        rw [Multiset.map_cons, Multiset.prod_cons]
        exact one_le_mul (h b (Multiset.mem_cons_self b s))
          (ih fun ζ hζ => h ζ (Multiset.mem_cons_of_mem hζ))
    exact key _ hall
  exact absurd hlt (not_lt.mpr this)

end GlobalTheory.TameTau
