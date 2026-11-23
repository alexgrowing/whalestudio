import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixOfStabilizerTrivial

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

namespace GlobalTheory.TypeIdent

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.TypeRec.factG

theorem irreducible_natCast_compl {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {g : ℕ}
    (hin : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (hnot : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) :
    Irreducible ((g : ℕ) : 𝒪[w.adicCompletion E]) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hle : ∀ y : 𝒪[w.adicCompletion E], Valued.v (y : w.adicCompletion E) ≤ 1 := fun y =>
    he.le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 y.2)
  have hunit : ∀ y : 𝒪[w.adicCompletion E], IsUnit y ↔ Valued.v (y : w.adicCompletion E) = 1 := fun y => by
    rw [← he.eq_one_iff_eq_one]
    exact (Valuation.integer.integers (valuation (w.adicCompletion E))).isUnit_iff_valuation_eq_one
  have hv : Valued.v ((g : ℕ) : w.adicCompletion E) = w.intValuation ((g : ℕ) : 𝓞 E) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E), ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    congr 1
    exact ((map_natCast (algebraMap E (w.adicCompletion E)) g).symm).trans
      (congrArg (algebraMap E (w.adicCompletion E)) (map_natCast (algebraMap (𝓞 E) E) g).symm)
  have h1 : w.intValuation ((g : ℕ) : 𝓞 E) ≤ WithZero.exp (-1 : ℤ) := by
    simpa using (w.intValuation_le_pow_iff_mem ((g : ℕ) : 𝓞 E) 1).mpr (by rwa [pow_one])
  have h2 : WithZero.exp (-2 : ℤ) < w.intValuation ((g : ℕ) : 𝓞 E) := by
    by_contra hc
    exact hnot ((w.intValuation_le_pow_iff_mem _ 2).mp (by simpa using not_lt.1 hc))
  have hc : (((g : ℕ) : 𝒪[w.adicCompletion E]) : w.adicCompletion E) = (g : w.adicCompletion E) := by simp
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [hunit, hc, hv]
    intro e
    rw [e, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · have h3 : Valued.v (a : w.adicCompletion E) * Valued.v (b : w.adicCompletion E) =
        w.intValuation ((g : ℕ) : 𝓞 E) := by
      rw [← hv, ← map_mul, ← hc, hab]; rfl
    rw [← h3] at h1 h2
    have h0 := (zero_le.trans_lt h2).ne'
    have ha := left_ne_zero_of_mul h0
    have hb := right_ne_zero_of_mul h0
    have ha1 := hle a
    have hb1 := hle b
    rw [hunit, hunit]
    rw [← WithZero.exp_log ha] at h2 ha1 ⊢
    rw [← WithZero.exp_log hb] at h2 hb1 ⊢
    rw [← WithZero.exp_add, WithZero.exp_lt_exp] at h2
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
    rw [← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
    omega

theorem nonempty_ident : ∀ D : D7, Nonempty (GlobalTheory.TypeRec.Ident D) := by
  intro D
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have key : ∀ k v, ∃ φ : ℚ_[D.host.g k] ≃+* (D.naut.plGw k v).adicCompletion D.host.E, Continuous φ := by
    intro k v
    obtain ⟨h1, h2, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)
    haveI : CharZero ((D.naut.plGw k v).adicCompletion D.host.E) :=
      charZero_of_injective_ringHom (algebraMap D.host.E _).injective
    obtain ⟨φ, h, -⟩ := GlobalTheory.QpChar.exists_ringEquiv_padic ((D.naut.plGw k v).adicCompletion D.host.E) (D.host.g k)
      ((GlobalTheory.LocLanglands.resCard_eq_normV _).trans h1) (irreducible_natCast_compl _ (D.naut.plGw_over k v) h2)
    exact ⟨φ, h⟩
  exact ⟨⟨fun k v => (key k v).choose, fun k v => (key k v).choose_spec⟩⟩

end GlobalTheory.TypeIdent

end
