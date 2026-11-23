import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.GaloisValuations.GlobalB

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def Dec (A : ValuationSubring (Ω)) : Subgroup (G F Ω) := A.decompositionSubgroup F

theorem mem_Dec {A : ValuationSubring (Ω)} {σ : G F Ω} :
    σ ∈ Dec (F := F) A ↔ σ • A = A := Iff.rfl

theorem apply_mem_iff_of_mem_Dec {A : ValuationSubring (Ω)} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) (x : Ω) : σ x ∈ A ↔ x ∈ A := by
  have h := mem_Dec.mp hσ
  have key : σ • x ∈ σ • A ↔ x ∈ A := ValuationSubring.smul_mem_pointwise_smul_iff
  rw [h] at key
  exact key

theorem valuation_lt_one_iff' (A : ValuationSubring (Ω)) (y : Ω) :
    A.valuation y < 1 ↔ y ∈ A ∧ (y = 0 ∨ y⁻¹ ∉ A) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, not_le,
      Valuation.one_lt_val_iff _ (inv_ne_zero hy), inv_inv]
    simp only [hy, false_or]
    exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩

theorem valuation_apply_lt_one_iff {A : ValuationSubring (Ω)} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) (y : Ω) :
    A.valuation (σ y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', (map_inv₀ σ y).symm, apply_mem_iff_of_mem_Dec hσ,
    apply_mem_iff_of_mem_Dec hσ, EmbeddingLike.map_eq_zero_iff]

theorem mul_inv_apply {σ : G F Ω} (x : Ω) : σ ((σ⁻¹ : G F Ω) x) = x := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

def Ine (A : ValuationSubring (Ω)) : Subgroup (G F Ω) where
  carrier := Inertia (F := F) A
  one_mem' := ⟨(Dec (F := F) A).one_mem, fun x _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, hσ'⟩ ⟨hτ, hτ'⟩
    refine ⟨(Dec (F := F) A).mul_mem hσ hτ, fun x hx => ?_⟩
    have e : (σ * τ) x - x = σ (τ x - x) + (σ x - x) := by
      simp [AlgEquiv.mul_apply, map_sub]
    rw [e]
    exact Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hσ _).mpr (hτ' x hx)) (hσ' x hx)
  inv_mem' := by
    rintro σ ⟨hσ, hσ'⟩
    refine ⟨(Dec (F := F) A).inv_mem hσ, fun x hx => ?_⟩
    have hy : A.valuation ((σ⁻¹ : G F Ω) x) ≤ 1 := by
      rw [A.valuation_le_one_iff, ← apply_mem_iff_of_mem_Dec hσ, mul_inv_apply]
      exact (A.valuation_le_one_iff x).mp hx
    have e : (σ⁻¹ : G F Ω) x - x = -(σ ((σ⁻¹ : G F Ω) x) - (σ⁻¹ : G F Ω) x) := by
      rw [mul_inv_apply]; ring
    rw [e, Valuation.map_neg]
    exact hσ' _ hy

theorem mem_Ine {A : ValuationSubring (Ω)} {σ : G F Ω} :
    σ ∈ Ine (F := F) A ↔ σ ∈ Inertia (F := F) A := Iff.rfl

theorem Ine_le_Dec (A : ValuationSubring (Ω)) : Ine (F := F) A ≤ Dec (F := F) A := fun _ h => (mem_Ine.mp h).1

theorem conj_mem_Ine {A : ValuationSubring (Ω)} {g σ : G F Ω} (hg : g ∈ Dec (F := F) A)
    (hσ : σ ∈ Ine (F := F) A) : g * σ * g⁻¹ ∈ Ine (F := F) A := by
  refine ⟨(Dec (F := F) A).mul_mem ((Dec (F := F) A).mul_mem hg hσ.1) ((Dec (F := F) A).inv_mem hg), fun x hx => ?_⟩
  have hy : A.valuation ((g⁻¹ : G F Ω) x) ≤ 1 := by
    rw [A.valuation_le_one_iff, ← apply_mem_iff_of_mem_Dec hg, mul_inv_apply]
    exact (A.valuation_le_one_iff x).mp hx
  have e : (g * σ * g⁻¹) x - x = g (σ ((g⁻¹ : G F Ω) x) - (g⁻¹ : G F Ω) x) := by
    rw [map_sub, mul_inv_apply]; rfl
  rw [e, valuation_apply_lt_one_iff hg]
  exact hσ.2 _ hy

instance normal_Ine_subgroupOf (A : ValuationSubring (Ω)) :
    ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using conj_mem_Ine g.2 hn

variable (F Ω) in

def cycZ (l : ℕ) [Fact l.Prime] : G F Ω →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Ω) l).comp
    (MulSemiringAction.toRingAut (G F Ω) (Ω))

variable (F Ω) in
theorem cyc_eq_map_cycZ (l : ℕ) [Fact l.Prime] (σ : G F Ω) :
    cyc F Ω l σ = Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
      (cycZ F Ω l σ) := rfl

variable (F Ω) in

theorem continuous_cycZ (l : ℕ) [Fact l.Prime] : Continuous (cycZ F Ω l) :=
  cyclotomicCharacter.continuous l F Ω

variable (F Ω) in

def cycMod (l : ℕ) [Fact l.Prime] (r : ℕ) : G F Ω →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp (cycZ F Ω l)

def IsCC (c : G F Ω) : Prop :=
  ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)

variable (Ω) in

def placeOf (v : HeightOneSpectrum (𝓞 F)) : ValuationSubring (Ω) :=
  @Classical.epsilon _ ⟨⊤⟩ (fun A => IsPlaceOver A v)

variable (Ω) in

def frobOf (v : HeightOneSpectrum (𝓞 F)) : G F Ω :=
  @Classical.epsilon _ ⟨1⟩ (fun σ : G F Ω => IsFrob (placeOf Ω v) (normV v) σ)

section unram

variable (S : Set (HeightOneSpectrum (𝓞 F)))

variable (Ω) in

def NS : Subgroup (G F Ω) :=
  (Subgroup.normalClosure
    (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring (Ω) | IsPlaceOver A v}, Inertia (F := F) A)
    ).topologicalClosure

instance normal_NS : (NS Ω S).Normal := by
  unfold NS; exact Subgroup.is_normal_topologicalClosure _

variable (Ω) in
theorem isClosed_NS : IsClosed (NS Ω S : Set (G F Ω)) := Subgroup.isClosed_topologicalClosure _

variable (Ω) in

abbrev GS := G F Ω ⧸ NS Ω S

variable (Ω) in

def toGS : G F Ω →* GS Ω S := QuotientGroup.mk' (NS Ω S)

variable (Ω) in
theorem continuous_toGS : Continuous (toGS Ω S) := by
  unfold toGS
  exact continuous_quot_mk

def locHom (A : ValuationSubring (Ω)) : Dec (F := F) A →* GS Ω S :=
  (toGS Ω S).comp (Dec (F := F) A).subtype

theorem continuous_locHom (A : ValuationSubring (Ω)) :
    Continuous (locHom S A) := (continuous_toGS Ω S).comp continuous_subtype_val

def UnramOutside {H : Type*} [Group H] (ρ : G F Ω →* H) : Prop := ∀ σ ∈ NS Ω S, ρ σ = 1

theorem unramOutside_iff {H : Type*} [Group H] [TopologicalSpace H] [T2Space H]
    (ρ : G F Ω →* H) (hρ : Continuous ρ) :
    UnramOutside S ρ ↔ ∀ v ∉ S, ∀ A, IsPlaceOver A v → ∀ σ ∈ Inertia (F := F) A, ρ σ = 1 := by
  constructor
  · intro h v hv A hA σ hσ
    apply h
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop]
    exact ⟨v, hv, A, hA, hσ⟩
  · intro h σ hσ
    have hker : NS Ω S ≤ ρ.ker := by
      apply Subgroup.topologicalClosure_minimal
      · apply Subgroup.normalClosure_le_normal
        intro τ hτ
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop] at hτ
        obtain ⟨v, hv, A, hA, hτ⟩ := hτ
        exact MonoidHom.mem_ker.mpr (h v hv A hA τ hτ)
      · rw [MonoidHom.coe_ker]
        exact isClosed_singleton.preimage hρ
    exact MonoidHom.mem_ker.mp (hker hσ)

end unram

section Basic₃

theorem valuation_natCast_le_one (A : ValuationSubring (Ω)) (n : ℕ) :
    A.valuation (n : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A n)

theorem not_valuation_lt_one_of_isPlaceOver {l : ℕ} {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    (n : ℕ) : ¬ A.valuation (((l ^ n : ℕ) : Ω)) < 1 := by
  unfold Formalism.ConjugateSelfDual.IsPlaceOver at h
  intro hlt
  have hc : algebraMap F Ω (((l ^ n : ℕ) : 𝓞 F) : F) = ((l ^ n : ℕ) : Ω) := by
    simp
  rw [← hc, h] at hlt
  exact hl (v.isPrime.mem_of_pow_mem n (by simpa using hlt))

theorem cycZ_toZModPow_eq [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} {q : ℕ}
    (hσ : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) (n : ℕ) :
    PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = PadicInt.toZModPow n (q : ℤ_[l]) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hspec := cyclotomicCharacter.spec (L := Ω) l
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) ζ hζ.pow_eq_one
  set m := (((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ)) : ℤ_[l]).toZModPow n |>.val with hm
  have hσζ : σ ζ = ζ ^ m := hspec
  have hζA : A.valuation ζ ≤ 1 := (valuation_eq_one_of_pow_eq_one A hN0 hζ.pow_eq_one).le
  have hlt := hσ ζ hζA
  rw [hσζ] at hlt
  have heq : ζ ^ m = ζ ^ q := by
    refine eq_of_pow_eq_one A (not_valuation_lt_one_of_isPlaceOver hl h n) ?_ ?_ hlt
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have heq' : (hζ.isUnit hN0).unit ^ m = (hζ.isUnit hN0).unit ^ q := Units.ext (by simpa using heq)
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
  rw [map_natCast]
  show ((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) : ℤ_[l]).toZModPow n = _
  rw [← ZMod.natCast_zmod_val (((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) : ℤ_[l]).toZModPow n), ← hm]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heq'

theorem eq_of_isPlaceOver {A : ValuationSubring (Ω)} {v v' : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : v = v' := by
  unfold Formalism.ConjugateSelfDual.IsPlaceOver at h h'
  have e : v.asIdeal = v'.asIdeal := by
    ext x
    rw [← h x, ← h' x]
  exact IsDedekindDomain.HeightOneSpectrum.ext e

theorem inv_mul_mem_Ine_of_isFrob {A : ValuationSubring (Ω)} {q : ℕ} {σ τ : G F Ω}
    (hσ : IsFrob A q σ) (hτ : IsFrob A q τ) : σ⁻¹ * τ ∈ Ine (F := F) A := by
  obtain ⟨hσD, hσF⟩ := hσ
  obtain ⟨hτD, hτF⟩ := hτ
  have hσD' : σ ∈ Dec (F := F) A := mem_Dec.mpr hσD
  have hτD' : τ ∈ Dec (F := F) A := mem_Dec.mpr hτD
  refine mem_Ine.mpr ⟨(Dec (F := F) A).mul_mem ((Dec (F := F) A).inv_mem hσD') hτD', fun x hx => ?_⟩
  rw [← valuation_apply_lt_one_iff hσD']
  have e : σ ((σ⁻¹ * τ) x - x) = (τ x - x ^ q) - (σ x - x ^ q) := by
    rw [map_sub, AlgEquiv.mul_apply, mul_inv_apply]; ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (hτF x hx) (hσF x hx))

theorem isFrob_mul_of_mem_Ine {A : ValuationSubring (Ω)} {q : ℕ} {σ ι : G F Ω}
    (hσ : IsFrob A q σ) (hι : ι ∈ Ine (F := F) A) : IsFrob A q (σ * ι) := by
  obtain ⟨hσD, hσF⟩ := hσ
  obtain ⟨hιD, hιI⟩ := mem_Ine.mp hι
  have hσD' : σ ∈ Dec (F := F) A := mem_Dec.mpr hσD
  refine ⟨mem_Dec.mp ((Dec (F := F) A).mul_mem hσD' hιD), fun x hx => ?_⟩
  have e : (σ * ι) x - x ^ q = σ (ι x - x) + (σ x - x ^ q) := by
    rw [AlgEquiv.mul_apply, map_sub]; ring
  rw [e]
  exact Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hσD' _).mpr (hιI x hx)) (hσF x hx)

variable (Ω) in

theorem exists_isPlaceOver (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : ValuationSubring (Ω), IsPlaceOver A v := by
  classical
  have hinj : Function.Injective (algebraMap F Ω) := (algebraMap F Ω).injective
  haveI hV : IsLocalRing (v.valuation F).valuationSubring.toSubring :=
    inferInstanceAs (IsLocalRing (v.valuation F).valuationSubring)
  haveI hS : IsLocalRing ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)) :=
    IsLocalRing.of_surjective'
      ((v.valuation F).valuationSubring.toSubring.equivMapOfInjective (algebraMap F Ω) hinj).toRingHom
      ((v.valuation F).valuationSubring.toSubring.equivMapOfInjective (algebraMap F Ω) hinj).surjective
  obtain ⟨B, hB⟩ := LocalSubring.exists_le_valuationSubring
    (LocalSubring.mk ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)) : LocalSubring Ω)
  obtain ⟨hsub, hloc⟩ := hB
  have hfx : ∀ z : F, v.valuation F z ≤ 1 → algebraMap F Ω z ∈ B := fun z hz =>
    hsub (Subring.mem_map.mpr ⟨z, hz, rfl⟩)
  have hle : ∀ r : 𝓞 F, v.valuation F (r : F) ≤ 1 := fun r => v.valuation_le_one r
  have hlt : ∀ r : 𝓞 F, v.valuation F (r : F) < 1 ↔ r ∈ v.asIdeal := fun r =>
    v.valuation_lt_one_iff_mem r
  refine ⟨B, ?_⟩
  unfold Formalism.ConjugateSelfDual.IsPlaceOver
  intro x
  constructor
  · intro h
    by_contra hx
    have hx1 : v.valuation F (x : F) = 1 := le_antisymm (hle x) (not_lt.mp (mt (hlt x).mp hx))
    have hx0 : (x : F) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hx1
      exact zero_ne_one hx1
    have hne : algebraMap F Ω (x : F) ≠ 0 := (map_ne_zero _).mpr hx0
    have hinv : v.valuation F ((x : F)⁻¹) ≤ 1 := by rw [map_inv₀, hx1, inv_one]
    have hmem : algebraMap F Ω ((x : F)⁻¹) ∈ B := hfx _ hinv
    rw [map_inv₀] at hmem
    have h1 : B.valuation (algebraMap F Ω (x : F))⁻¹ ≤ 1 := (B.valuation_le_one_iff _).mpr hmem
    have h2 := (Valuation.one_lt_val_iff B.valuation (inv_ne_zero hne)).mpr (by rwa [inv_inv])
    exact absurd h1 (not_le.mpr h2)
  · intro hx
    by_contra hnot
    have hxlt := (hlt x).mpr hx
    by_cases hx0 : (x : F) = 0
    · apply hnot
      rw [hx0, map_zero, map_zero]
      exact zero_lt_one
    have hne : algebraMap F Ω (x : F) ≠ 0 := (map_ne_zero _).mpr hx0
    have hyB : algebraMap F Ω (x : F) ∈ B := hfx _ (hle x)
    have hyv : B.valuation (algebraMap F Ω (x : F)) = 1 :=
      le_antisymm ((B.valuation_le_one_iff _).mpr hyB) (not_lt.mp hnot)
    have hyinvB : (algebraMap F Ω (x : F))⁻¹ ∈ B := by
      rw [← B.valuation_le_one_iff, map_inv₀, hyv, inv_one]
    have hyS : algebraMap F Ω (x : F) ∈ (v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω) :=
      Subring.mem_map.mpr ⟨_, hle x, rfl⟩
    have hunit : IsUnit (Subring.inclusion hsub ⟨_, hyS⟩) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hyinvB⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩
    obtain ⟨u, hu⟩ := hloc.map_nonunit _ hunit
    have ht := ((u⁻¹ : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))ˣ) :
      ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))).2
    have hmul : algebraMap F Ω (x : F) *
        ((u⁻¹ : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))ˣ) :
          ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))).1 = 1 := by
      have h3 := congrArg Subtype.val u.mul_inv
      rw [hu] at h3
      exact h3
    obtain ⟨z, hz, hzt⟩ := Subring.mem_map.mp ht
    have hzx : z = (x : F)⁻¹ := by
      apply hinj
      rw [hzt, map_inv₀]
      exact eq_inv_of_mul_eq_one_right hmul
    have hzle : v.valuation F z ≤ 1 := hz
    rw [hzx] at hzle
    have h4 := (Valuation.one_lt_val_iff (v.valuation F) (inv_ne_zero hx0)).mpr (by rwa [inv_inv])
    exact absurd hzle (not_le.mpr h4)

variable (Ω) in
theorem isPlaceOver_placeOf (v : HeightOneSpectrum (𝓞 F)) : IsPlaceOver (placeOf Ω v) v := Classical.epsilon_spec (exists_isPlaceOver Ω v)

theorem exists_smul_eq_of_isPlaceOver [IsAlgClosure F Ω] {A A' : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (h' : IsPlaceOver A' v) :
    ∃ σ : G F Ω, σ • A = A' := by
  exact exists_smul_eq_of_over h h'

theorem exists_isFrob [IsAlgClosure F Ω] {A : ValuationSubring (Ω)} {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) : ∃ σ : G F Ω, IsFrob A (normV v) σ := by
  exact exists_frob_over h

variable (Ω) in
theorem isFrob_frobOf [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) :
    IsFrob (placeOf Ω v) (normV v) (frobOf Ω v) := Classical.epsilon_spec (exists_isFrob (isPlaceOver_placeOf Ω v))

theorem cyc_eq_one_of_mem_Ine [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : cyc F Ω l σ = 1 := by
  obtain ⟨-, hI⟩ := mem_Ine.mp hσ
  have key : ∀ n, PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) =
      PadicInt.toZModPow n ((1 : ℕ) : ℤ_[l]) :=
    cycZ_toZModPow_eq hl h (fun x hx => by simpa using hI x hx)
  have hz : ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    simpa using PadicInt.ext_of_toZModPow.mp key
  rw [cyc_eq_map_cycZ, show cycZ F Ω l σ = 1 from Units.ext hz, map_one]

theorem cycZ_of_isFrob [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : IsFrob A (normV v) σ) : ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (normV v : ℤ_[l]) := by
  obtain ⟨-, hF⟩ := hσ
  exact PadicInt.ext_of_toZModPow.mp (cycZ_toZModPow_eq hl h hF)

private theorem isClosed_setOf_apply_lemma [IsAlgClosure F Ω] (x : Ω) (P : Ω → Prop) :
    IsClosed {τ : G F Ω | P (τ x)} := by
  have hal : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hfd : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ : G F Ω => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)),
    ?_, hH.preimage (continuous_const.mul continuous_id), ?_⟩
  · intro τ hτ hPτ
    have h1 : (σ⁻¹ * τ) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x (IntermediateField.mem_adjoin_simple_self F x)
    have h2 : τ x = σ x := by
      have h3 := congrArg σ h1
      rwa [AlgEquiv.mul_apply, mul_inv_apply] at h3
    exact hσ (by simpa only [Set.mem_setOf_eq, h2] using hPτ)
  · show σ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _

theorem isClosed_Dec [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Dec (F := F) A : Set (G F Ω)) := by
  have e : (Dec (F := F) A : Set (G F Ω)) = ⋂ x : Ω, {τ : G F Ω | τ x ∈ A ↔ x ∈ A} := by
    ext τ
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => mem_Dec.mpr ?_⟩
    ext y
    have k : τ • ((τ⁻¹ : G F Ω) y) ∈ τ • A ↔ (τ⁻¹ : G F Ω) y ∈ A :=
      ValuationSubring.smul_mem_pointwise_smul_iff
    rw [AlgEquiv.smul_def, mul_inv_apply] at k
    rw [k, ← h ((τ⁻¹ : G F Ω) y), mul_inv_apply]
  rw [e]
  exact isClosed_iInter fun x => isClosed_setOf_apply_lemma x (fun y => y ∈ A ↔ x ∈ A)

theorem isClosed_Ine [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Ine (F := F) A : Set (G F Ω)) := by
  have e : (Ine (F := F) A : Set (G F Ω)) = (Dec (F := F) A : Set (G F Ω)) ∩
      ⋂ x : Ω, {τ : G F Ω | A.valuation x ≤ 1 → A.valuation (τ x - x) < 1} := by
    ext τ
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [e]
  exact (isClosed_Dec A).inter (isClosed_iInter fun x =>
    isClosed_setOf_apply_lemma x (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))

end Basic₃

end ReciprocityTheory.Gal
