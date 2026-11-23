import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnit

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Neutral.B1
  GlobalTheory.HeckeGal

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Tame

variable {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 M)}

theorem normV_mem (v : HeightOneSpectrum (𝓞 M)) : ((normV v : ℕ) : 𝓞 M) ∈ v.asIdeal := by
  have : Finite (𝓞 M ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let := Fintype.ofFinite (𝓞 M ⧸ v.asIdeal)
  have hc : ((Fintype.card (𝓞 M ⧸ v.asIdeal) : ℕ) : 𝓞 M ⧸ v.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card] at hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact hc

omit [IsAlgClosure M Ω] in

theorem weil_fix_root (h : IsPlaceOver A v) (s : Weil h) (ζ : Ω) (hζ : ζ ^ (normV v - 1) = 1) :
    (s : G M Ω) ζ = ζ := by
  have hq : 1 < normV v := one_lt_normV v
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow (n := normV v - 1) (by omega) (by rw [hζ]; exact isIntegral_one)
  have hζA : A.valuation ζ ≤ 1 := (A.valuation_le_one_iff _).2 (ReciprocityTheory.Gal.mem_of_isIntegral_int A hζi)
  have hζ1 : ζ ^ normV v = ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  have hpow : ∀ (y : Ω), y ^ normV v = y → ∀ k : ℕ, y ^ (normV v ^ k) = y := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, hy]
  have hsζ : ((s : G M Ω) ζ) ^ (normV v - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hsζ1 : ((s : G M Ω) ζ) ^ normV v = (s : G M Ω) ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hsζ, one_mul]
  obtain ⟨a, b, hab⟩ := s.2
  have hc := hab.2 ζ hζA
  rw [hpow _ hsζ1, hpow _ hζ1] at hc
  have hsA : A.valuation ((s : G M Ω) ζ) ≤ 1 := by
    rw [A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hab.1, ← A.valuation_le_one_iff]
    exact hζA
  have hval1 : A.valuation ζ = 1 := by
    refine le_antisymm hζA (not_lt.1 fun hlt => ?_)
    have := pow_lt_one₀ zero_le hlt (show normV v - 1 ≠ 0 by omega)
    rw [← map_pow, hζ, map_one] at this
    exact lt_irrefl _ this
  have hqA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (h ((normV v : ℕ) : 𝓞 M)).2 (normV_mem v)
    simpa using this
  have hd : ¬ A.valuation (aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X]))) < 1 := by
    have e : aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X])) =
        (((normV v - 1 : ℕ) : Ω)) * ζ ^ (normV v - 1 - 1) := by
      simp [derivative_X_pow]
    rw [e, map_mul, map_pow, hval1, one_pow, mul_one]
    have e2 : (((normV v - 1 : ℕ) : Ω)) = -1 + ((normV v : ℕ) : Ω) := by
      rw [Nat.cast_sub hq.le]; ring
    have h' : A.valuation ((normV v : ℕ) : Ω) < A.valuation (-1 : Ω) := by
      rw [Valuation.map_neg, map_one]; exact hqA
    rw [e2, Valuation.map_add_eq_of_lt_left _ h', Valuation.map_neg, map_one]
    exact lt_irrefl _
  exact (GlobalTheory.eq_of_root_congr_of_deriv_unit A (X ^ (normV v - 1) - 1) ζ ((s : G M Ω) ζ) hζA hsA
    (by simp [hζ]) (by simp [hsζ]) hd (by rw [Valuation.map_sub_swap]; exact hc)).symm

end Tame

theorem lTameRec : LTameRec := by
  intro hA hC M Ω _ _ _ _ _ _ g _ A v h hg1 hg2 a ha π hπ t x hx
  classical
  have hq : 1 < normV v := one_lt_normV v
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap M Ω).injective
  have : NeZero (normV v - 1) := ⟨by omega⟩
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hπ
    exact hg0 hπ.symm

  let f : Weil h →* rootsOfUnity (normV v - 1) Ω :=
    { toFun := fun s => ⟨Units.mk0 ((s : G M Ω) π / π) (div_ne_zero ((_root_.map_ne_zero _).2 hπ0) hπ0), by
          rw [mem_rootsOfUnity]
          ext
          simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
          rw [div_pow, ← map_pow, hπ, map_natCast, div_self hg0]⟩
      map_one' := by
        ext
        simp [div_self hπ0]
      map_mul' := fun s s' => by
        ext
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, Subgroup.coe_mul, AlgEquiv.mul_apply]
        have hr : (((s' : G M Ω) π / π)) ^ (normV v - 1) = 1 := by
          rw [div_pow, ← map_pow, hπ, map_natCast, div_self hg0]
        have hfix := weil_fix_root h s _ hr
        have e : (s : G M Ω) ((s' : G M Ω) π) = (s : G M Ω) (((s' : G M Ω) π / π) * π) := by
          rw [div_mul_cancel₀ _ hπ0]
        rw [e, map_mul, hfix]
        field_simp }
  have hf : ∀ s s' : Weil h, f s = f s' → (s : G M Ω) π = (s' : G M Ω) π := fun s s' hss => by
    have := congrArg (fun z : rootsOfUnity (normV v - 1) Ω => ((z : Ωˣ) : Ω)) hss
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0] at this
    exact (div_left_inj' hπ0).1 this
  let d := Nat.card (rootsOfUnity (normV v - 1) Ω)
  have hd : 0 < d := Nat.card_pos
  have : NeZero d := ⟨hd.ne'⟩
  let e : rootsOfUnity (normV v - 1) Ω ≃* rootsOfUnity d ℂ :=
    mulEquivOfCyclicCardEq (Complex.card_rootsOfUnity d).symm
  let η : Weil h →* ℂˣ := (rootsOfUnity d ℂ).subtype.comp (e.toMonoidHom.comp f)
  have hη : ∀ s s' : Weil h, η s = η s' → (s : G M Ω) π = (s' : G M Ω) π := fun s s' hss =>
    hf s s' (e.injective (Subtype.ext hss))

  have hπi : IsIntegral M π := Algebra.IsIntegral.isIntegral π
  have : FiniteDimensional M (IntermediateField.adjoin M ({π} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional hπi
  have hηs : IsSmooth η := by
    let H1 : Subgroup (Ine (F := M) A) :=
      (IntermediateField.adjoin M ({π} : Set Ω)).fixingSubgroup.comap (Ine (F := M) A).subtype
    have hH1 : IsOpen (H1 : Set (Ine (F := M) A)) :=
      (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val
    have hle : H1 ≤ (η.comp (ineIncl h)).ker := fun σ hσ => by
      have hσπ : (σ : G M Ω) π = π :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ π (IntermediateField.mem_adjoin_simple_self _ _)
      have h1 : f (ineIncl h σ) = 1 := by
        ext
        simp [f, hσπ, div_self hπ0]
      show η (ineIncl h σ) = 1
      simp [η, h1]
    exact Subgroup.isOpen_mono hle hH1
  obtain ⟨χ, -, hχ⟩ := ha.factor η hηs

  obtain ⟨art, hart⟩ := hA M Ω
  have hπ' : π ^ (normV v - 1) = algebraMap M Ω (((g : ℕ) : 𝓞 M) : M) := by rw [hπ]; simp
  obtain ⟨σ, hσI, hσab, hσπ⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hA M Ω art hart v A h ((g : ℕ) : 𝓞 M) hg1 hg2 π
    hπ' (a (ineIncl h t)) x (GlobalTheory.ArtinInertia.isUnitAt_artin_ine h a ha t) hx
  let σ' : Ine (F := M) A := ⟨σ, hσI⟩
  have e1 : art (localIdele M v (a (ineIncl h σ'))) = art (localIdele M v (a (ineIncl h t))) := by
    rw [ha.glob art hart, ha.glob art hart]
    exact hσab.trans (ha.glob art hart (ineIncl h t))
  have e2 : a (ineIncl h σ') = a (ineIncl h t) := GlobalTheory.T.globalArtin_localIdele_injective hC M Ω art hart v e1
  have e3 : η (ineIncl h σ') = η (ineIncl h t) := by
    rw [hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, e2]
  have e4 := hη _ _ e3
  have e5 : (t : G M Ω) π = σ π := e4.symm
  rw [e5]
  exact hσπ

end DiscreteGroups.sglob.DzType
