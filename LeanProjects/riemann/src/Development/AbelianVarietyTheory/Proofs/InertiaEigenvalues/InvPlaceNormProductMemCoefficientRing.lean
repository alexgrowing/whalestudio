import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormUnit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem coprime_absNorm {K : Type} [Field K] [NumberField K] (l : ℕ) (hl : l.Prime)
    (P : HeightOneSpectrum (𝓞 K)) (hP : ((l : ℕ) : 𝓞 K) ∉ P.asIdeal) :
    Nat.Coprime l (Ideal.absNorm P.asIdeal) := by
  rw [Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  haveI : Fact l.Prime := ⟨hl⟩
  letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  have hfin : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  haveI := Fintype.ofFinite (𝓞 K ⧸ P.asIdeal)
  have hc : l ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) := by
    rw [Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]; exact hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card l hc
  have h1 : (l : 𝓞 K ⧸ P.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [addOrderOf_zero] at hx; exact hl.one_lt.ne hx
  have h2 : (l : 𝓞 K ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  apply hP
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact h2

theorem isUnit_natCast_of_coprime {R : Type} [CommRing R] [IsLocalRing R] {l n : ℕ}
    (hl : ((l : ℕ) : R) ∈ IsLocalRing.maximalIdeal R) (h : Nat.Coprime l n) : IsUnit ((n : ℕ) : R) := by
  by_contra hn
  have hn' : ((n : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 h : IsCoprime (l : ℤ) (n : ℤ))
  have e : (1 : R) = (a : R) * (l : R) + (b : R) * (n : R) := by
    have := congrArg (Int.cast : ℤ → R) hab
    push_cast at this
    exact this.symm
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [e]; exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hn')
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem normProd_inv_mem (D : D7) (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) (Q : Finset (Pl D.host.E))
    (hQ : Disjoint Q (D.ntw.S0 i)) : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eO i b).range := by
  have hcop : Nat.Coprime (D.ntw.l i) (normProd Q) := by
    unfold normProd
    refine Nat.Coprime.prod_right fun P hP => coprime_absNorm _ (D.ntw.lPrime i).out P fun hl => ?_
    exact Finset.disjoint_left.1 hQ hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime (D.ntw.O_l i) hcop
  refine ⟨(u⁻¹ : (D.ntw.O i)ˣ), ?_⟩
  have h1 : ρ.eO i b (u : D.ntw.O i) = ((normProd Q : ℕ) : ℂ) := by rw [hu, map_natCast]
  rw [← h1]
  exact map_units_inv (ρ.eO i b) u

end GlobalTheory.NormUnit
