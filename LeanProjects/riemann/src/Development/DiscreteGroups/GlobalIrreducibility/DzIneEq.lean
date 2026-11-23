import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace DiscreteGroups.sglob.DzType

section Fix

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
  [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω]

local notation "LL" => IntermediateField.normalClosure E E' Ω

theorem natCast_mem_of_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (g n : ℕ)
    (hn : 0 < n) (hN : normV v = g ^ n) : ((g : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let := Fintype.ofFinite (𝓞 K ⧸ v.asIdeal)
  have hc : ((Fintype.card (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K ⧸ v.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card, show Nat.card (𝓞 K ⧸ v.asIdeal) = g ^ n from hN, Nat.cast_pow] at hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact (pow_eq_zero_iff hn.ne').1 hc

theorem fix_of_ine (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (he : ∀ [w'.asIdeal.LiesOver w.asIdeal], w'.asIdeal.ramificationIdx (𝓞 E) = 1)
    (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) (e : E') : σ (algebraMap E' Ω e) = algebraMap E' Ω e := by
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NumberField (LL) :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap E (LL)).injective
      to_finiteDimensional := Module.Finite.trans E (LL) }
  have : IsGalois E' (LL) := IsGalois.tower_top_of_isGalois E E' (LL)
  have hmem : ∀ x : 𝓞 (LL), (((x : LL) : Ω)) ∈ A := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A ((x.2).map (IsScalarTower.toAlgHom ℤ (LL) Ω))
  let ψ : 𝓞 (LL) →+* A :=
    { toFun := fun x => ⟨((x : LL) : Ω), hmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let P : Ideal (𝓞 (LL)) := (IsLocalRing.maximalIdeal A).comap ψ
  have hP : ∀ x : 𝓞 (LL), x ∈ P ↔ A.valuation (((x : LL) : Ω)) < 1 := fun x => A.valuation_lt_one_iff (ψ x)
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hcE : ∀ x : 𝓞 E, (((algebraMap (𝓞 E) (𝓞 (LL)) x : 𝓞 (LL)) : LL) : Ω) = algebraMap E Ω (x : E) :=
    fun x => rfl
  have hcE' : ∀ x : 𝓞 E', (((algebraMap (𝓞 E') (𝓞 (LL)) x : 𝓞 (LL)) : LL) : Ω) = algebraMap E' Ω (x : E') :=
    fun x => rfl
  have : P.LiesOver w.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, hP, hcE]
    exact (h x).symm⟩
  have : P.LiesOver w'.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, hP, hcE']
    exact (h' x).symm⟩
  have : w'.asIdeal.LiesOver w.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, ← h' _, ← h x]
    have e1 : algebraMap E' Ω ((algebraMap (𝓞 E) (𝓞 E') x : 𝓞 E') : E') = algebraMap E Ω (x : E) :=
      (IsScalarTower.algebraMap_apply E E' Ω (x : E)).symm
    rw [e1]⟩
  have : IsGaloisGroup (LL ≃ₐ[E] LL) (𝓞 E) (𝓞 (LL)) :=
    IsGaloisGroup.of_isFractionRing (LL ≃ₐ[E] LL) (𝓞 E) (𝓞 (LL)) E (LL)
  have : IsGaloisGroup (LL ≃ₐ[E'] LL) (𝓞 E') (𝓞 (LL)) :=
    IsGaloisGroup.of_isFractionRing (LL ≃ₐ[E'] LL) (𝓞 E') (𝓞 (LL)) E' (LL)
  have c1 := Ideal.card_inertia_eq_ramificationIdxIn (G := LL ≃ₐ[E] LL) w.asIdeal P
  have c2 := Ideal.card_inertia_eq_ramificationIdxIn (G := LL ≃ₐ[E'] LL) w'.asIdeal P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx w.asIdeal P (LL ≃ₐ[E] LL)] at c1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx w'.asIdeal P (LL ≃ₐ[E'] LL)] at c2
  have tower := Ideal.ramificationIdx_tower (R := 𝓞 E) w'.asIdeal P
  have hcard : Nat.card (P.inertia (LL ≃ₐ[E] LL)) ≤ Nat.card (P.inertia (LL ≃ₐ[E'] LL)) := by
    rw [c1, c2, tower, he, one_mul]
  let f : P.inertia (LL ≃ₐ[E'] LL) → P.inertia (LL ≃ₐ[E] LL) := fun τ => ⟨τ.1.restrictScalars E, fun x => τ.2 x⟩
  have hf : Function.Injective f := fun τ τ' hτ =>
    Subtype.ext (AlgEquiv.restrictScalars_injective E (congrArg Subtype.val hτ))
  have hbij := hf.bijective_of_nat_card_le hcard
  let σb : LL ≃ₐ[E] LL := σ.restrictNormal (LL)
  have hcomm : ∀ y : LL, ((σb y : LL) : Ω) = σ ((y : LL) : Ω) := fun y => AlgEquiv.restrictNormal_commutes σ (LL) y
  have hσb : σb ∈ P.inertia (LL ≃ₐ[E] LL) := fun x => by
    show σb • x - x ∈ P
    rw [hP]
    have e2 : (((σb • x - x : 𝓞 (LL)) : LL) : Ω) = ((σb (x : LL) : LL) : Ω) - ((x : LL) : Ω) := rfl
    rw [e2, hcomm]
    exact hσ.2 _ ((A.valuation_le_one_iff _).2 (hmem x))
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨σb, hσb⟩
  have hτ' : τ.1.restrictScalars E = σb := congrArg Subtype.val hτ
  have key : σb (algebraMap E' (LL) e) = algebraMap E' (LL) e := by
    rw [← hτ']
    exact τ.1.commutes e
  have e5 : (((algebraMap E' (LL) e : LL)) : Ω) = algebraMap E' Ω e := rfl
  rw [← e5, ← hcomm, key]

end Fix

theorem ine_lift {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
    [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (n : ℕ) (hn : 0 < n)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) :
    ∃ t : G E' Ω, t ∈ Ine (F := E') A ∧ AlgEquiv.restrictScalars E t = σ := by
  have hgw' := natCast_mem_of_normV w' g n hn hN
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    refine (h _).1 ?_
    have e1 : algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) = algebraMap E' Ω (((g : ℕ) : 𝓞 E') : E') := by simp
    rw [e1]
    exact (h' _).2 hgw'
  have he : ∀ [w'.asIdeal.LiesOver w.asIdeal], w'.asIdeal.ramificationIdx (𝓞 E) = 1 := by
    intro _
    have hmap : ¬ Ideal.map (algebraMap (𝓞 E) (𝓞 E')) w.asIdeal ≤ w'.asIdeal ^ 2 := fun hle => hg (by
      have := hle (Ideal.mem_map_of_mem (algebraMap (𝓞 E) (𝓞 E')) hgw)
      rwa [map_natCast] at this)
    have hlt := Ideal.ramificationIdx'_lt hmap
    rw [Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal w'.asIdeal w.ne_bot] at hlt
    have hpos := Ideal.ramificationIdx_pos w'.asIdeal (𝓞 E)
    omega
  have hfix := fix_of_ine A w h w' h' he σ hσ
  let t : G E' Ω := { σ.toRingEquiv with commutes' := hfix }
  refine ⟨t, ⟨?_, fun x hx => hσ.2 x hx⟩, AlgEquiv.ext fun x => rfl⟩
  show t • A = A
  have hd : σ • A = A := hσ.1
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hd]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

end DiscreteGroups.sglob.DzType
