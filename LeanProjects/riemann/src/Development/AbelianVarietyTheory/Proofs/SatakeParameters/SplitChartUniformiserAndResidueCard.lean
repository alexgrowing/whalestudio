import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitUnif

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (φ : E →+* v.adicCompletion F)

omit [NumberField E] [Algebra F E] in

theorem map_mem (x : 𝓞 E) : φ x ∈ v.adicCompletionIntegers F := by
  have h2 : IsIntegral (v.adicCompletionIntegers F) (φ x) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) φ (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.adicCompletionIntegers F)
    (K := v.adicCompletion F)).1 h2
  rw [← hy]
  exact y.2

theorem lt_one_iff (x : WithZero (Multiplicative ℤ)) : x < 1 ↔ x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem mem_max (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (x : v.adicCompletion F) < 1 :=
  Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))

theorem irreducible_of_valued (p : v.adicCompletionIntegers F)
    (hp : Valued.v (p : v.adicCompletion F) = WithZero.exp (-1)) : Irreducible p := by
  have hp0 : (p : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext x
  rw [mem_max, lt_one_iff, Ideal.mem_span_singleton', ← hp]
  constructor
  · intro h
    refine ⟨⟨(x : v.adicCompletion F) / p, ?_⟩, Subtype.ext (div_mul_cancel₀ _ hp0)⟩
    show Valued.v ((x : v.adicCompletion F) / p) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ h zero_le
  · rintro ⟨a, rfl⟩
    show Valued.v ((a : v.adicCompletion F) * p) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' a.2

variable (P : HeightOneSpectrum (𝓞 E))
  (hφ : ∀ t : F, φ (algebraMap F E t) = algebraMap F (v.adicCompletion F) t)
  (hP : ∀ x : 𝓞 E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1)

include hφ hP in
theorem valued_unif (ϖ : 𝓞 E) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    Valued.v (φ ϖ) = WithZero.exp (-1) := by
  refine le_antisymm ((lt_one_iff _).1 ((hP ϖ).1 h1)) ?_
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  let s : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) t
  have hs : Valued.v (φ s) = WithZero.exp (-1) := by
    have e1 : (s : E) = algebraMap F E (algebraMap (𝓞 F) F t) := rfl
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F t)) =
        v.valuation F (algebraMap (𝓞 F) F t) := v.valuedAdicCompletion_eq_valuation' _
    rw [e1, hφ, e2, HeightOneSpectrum.valuation_of_algebraMap, ht]
  have hsP : s ∈ P.asIdeal := by rw [hP, lt_one_iff, hs]
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply h2
    rw [show ϖ = 0 from Subtype.ext h]
    exact zero_mem _
  have hle : P.intValuation s ≤ P.intValuation ϖ := by
    have a1 := (P.intValuation_le_pow_iff_mem s 1).2 (by simpa using hsP)
    have a2 := mt (P.intValuation_le_pow_iff_mem ϖ 2).1 h2
    have a3 : P.intValuation ϖ ≠ 0 := P.intValuation_ne_zero ϖ (fun h => hϖ0 (by rw [h]; rfl))
    refine a1.trans ?_
    rw [← WithZero.exp_log a3, WithZero.exp_le_exp] at a2 ⊢
    push_cast at a2 ⊢
    omega
  have hx : P.valuation E ((s : E) / ϖ) ≤ 1 := by
    rw [map_div₀]
    refine div_le_one_of_le₀ ?_ zero_le
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact hle
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer _ hx
  have hd : Valued.v (φ ((d : 𝓞 E) : E)) = 1 :=
    le_antisymm (map_mem v φ d) (not_lt.1 (mt (hP d).2 d.2))
  have h3 : (s : E) * ((d : 𝓞 E) : E) = (n : E) * ϖ := by
    have h' : (s : E) / ϖ * ((d : 𝓞 E) : E) = (n : E) := h
    rw [← h']
    field_simp
  have h4 := congrArg (fun z => Valued.v (φ z)) h3
  simp only [map_mul] at h4
  rw [hd, mul_one, hs] at h4
  rw [h4]
  exact mul_le_of_le_one_left' (map_mem v φ n)

include hφ hP in
theorem card_residueField :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm P.asIdeal := by
  let ψ : 𝓞 E →+* v.adicCompletionIntegers F :=
    (φ.comp (algebraMap (𝓞 E) E)).codRestrict _ (map_mem v φ)
  let χ : 𝓞 E →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp ψ
  have hker : RingHom.ker χ = P.asIdeal := by
    ext x
    rw [RingHom.mem_ker, hP]
    show IsLocalRing.residue _ (ψ x) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, mem_max]
    rfl
  have hsurj : Function.Surjective χ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := Formalism.UG.P.glint_exists_approx v x
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r, ?_⟩
    show IsLocalRing.residue _ (ψ _) = _
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max]
    have e1 : ((ψ (algebraMap (𝓞 F) (𝓞 E) r) : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap (𝓞 F) (v.adicCompletion F) r := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← hφ]
      rfl
    rw [AddSubgroupClass.coe_sub, e1]
    exact hr
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

end General

theorem unif_chart : ∀ {D : D7} (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → Chart e v π → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∃ p : Ov D v, algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D (ϖ : D.host.E)) ∧ Irreducible p) ∧ Nat.card (IsLocalRing.ResidueField (Ov D v)) = Ideal.absNorm P.asIdeal := by
  intro D e P v π he hc ϖ h1 h2
  let φ : D.host.E →+* v.adicCompletion D.host.F := π.comp (incA D)
  have hφ : ∀ t : D.host.F, φ (algebraMap D.host.F D.host.E t) =
      algebraMap D.host.F (v.adicCompletion D.host.F) t := by
    intro t
    have e1 : incA D (algebraMap D.host.F D.host.E t) =
        algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t
    show π (incA D _) = _
    rw [e1, hc.2.2.1, AlgHom.commutes, AlgHom.commutes]
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, hc.2.2.2, isInt_Ov]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  exact ⟨⟨⟨φ ϖ, map_mem v φ ϖ⟩, rfl, irreducible_of_valued v _ (valued_unif v φ P hφ hP ϖ h1 h2)⟩,
    card_residueField v φ P hφ hP⟩

end GlobalTheory.SplitUnif

end
