import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hkMul_out {G : Type} [Group G] (I : Subgroup G) (g : G) :
    ∃ i ∈ I, (g : G ⧸ I).out = g * i := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I g
  exact ⟨h, h.2, hh⟩

private theorem hkMul_mem {G : Type} [Group G] (I : Subgroup G) (x : G) (p : G ⧸ I) :
    p ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, p = ((a * x : G) : G ⧸ I) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem UpperTheory.V.AlgebraTools.hkMul :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (x y : G), HeckePair I → (∀ b ∈ I, ∃ a ∈ I, ∃ c ∈ I, x * b * y = a * (x * y) * c) → (MulAction.orbit I ((x * y : G) : G ⧸ I)).ncard = (MulAction.orbit I (x : G ⧸ I)).ncard * (MulAction.orbit I (y : G ⧸ I)).ncard → hk ρ I x * hk ρ I y = hk ρ I (x * y) := by
  intro A G M _ _ _ _ ρ I x y hI hb hc
  classical
  haveI fx : Fintype (MulAction.orbit I (x : G ⧸ I)) := (hI x).fintype
  haveI fy : Fintype (MulAction.orbit I (y : G ⧸ I)) := (hI y).fintype
  haveI fxy : Fintype (MulAction.orbit I ((x * y : G) : G ⧸ I)) := (hI (x * y)).fintype
  have hmem : ∀ (p : MulAction.orbit I (x : G ⧸ I)) (q : MulAction.orbit I (y : G ⧸ I)),
      (((p : G ⧸ I).out * (q : G ⧸ I).out : G) : G ⧸ I) ∈ MulAction.orbit I ((x * y : G) : G ⧸ I) := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨a, ha, rfl⟩ := (hkMul_mem I x p).1 hp
    obtain ⟨b, hb', rfl⟩ := (hkMul_mem I y q).1 hq
    obtain ⟨i, hi, e1⟩ := hkMul_out I (a * x)
    obtain ⟨j, hj, e2⟩ := hkMul_out I (b * y)
    obtain ⟨a', ha', c, hc', e3⟩ := hb (i * b) (mul_mem hi hb')
    refine (hkMul_mem I _ _).2 ⟨a * a', mul_mem ha ha', ?_⟩
    simp only [e1, e2]
    have : a * x * i * (b * y * j) = a * a' * (x * y) * (c * j) := by
      calc a * x * i * (b * y * j) = a * (x * (i * b) * y) * j := by group
        _ = _ := by rw [e3]; group
    rw [this]
    exact QuotientGroup.mk_mul_of_mem _ (mul_mem hc' hj)
  let f : MulAction.orbit I (x : G ⧸ I) × MulAction.orbit I (y : G ⧸ I) →
      MulAction.orbit I ((x * y : G) : G ⧸ I) := fun pq => ⟨_, hmem pq.1 pq.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨a, ha, rfl⟩ := (hkMul_mem I _ r).1 hr
    obtain ⟨i, hi, e1⟩ := hkMul_out I (a * x)
    obtain ⟨j, hj, e2⟩ := hkMul_out I (i⁻¹ * y)
    refine ⟨(⟨_, (hkMul_mem I _ _).2 ⟨a, ha, rfl⟩⟩, ⟨_, (hkMul_mem I _ _).2 ⟨i⁻¹, inv_mem hi, rfl⟩⟩), Subtype.ext ?_⟩
    simp only [f, e1, e2]
    have : a * x * i * (i⁻¹ * y * j) = a * (x * y) * j := by group
    rw [this]
    exact QuotientGroup.mk_mul_of_mem _ hj
  have hbij : Function.Bijective f := by
    refine (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, ?_⟩
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, hc]
  refine LinearMap.ext fun v => Subtype.ext ?_
  have h1 := (hkApply A G M ρ I I x (hI x)).1
  have h2 := (hkApply A G M ρ I I y (hI y)).1
  have h3 := (hkApply A G M ρ I I (x * y) (hI _)).1
  rw [Module.End.mul_apply]
  unfold hk
  rw [h1, h2, h3]
  simp only [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum]
  rw [← hbij.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨i, hi, e⟩ := hkMul_out I ((p : G ⧸ I).out * (q : G ⧸ I).out)
  simp only [f, e, map_mul, Module.End.mul_apply]
  rw [v.2 i hi]
