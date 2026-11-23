import Development.EtaleCohomology.KummerTheory.PlacePf

noncomputable section
open GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory.ValAICPf

variable {K : Type} [Field K] [IsAlgClosed K] (T : ValuationSubring K)

theorem mem_of_root (p : T[X]) (hp : p.Monic) (r : K) (hr : (p.map (algebraMap T K)).eval r = 0) : r ∈ T := by
  have hi : IsIntegral T r := ⟨p, hp, by rwa [eval_map] at hr⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := T) (K := K)).mp hi
  rw [← hy]; exact y.2

theorem aic : AIC T := by
  intro p hp hd
  have hd' : (p.map (algebraMap T K)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (IsFractionRing.injective T K)]
    intro h; rw [degree_eq_natDegree hp.ne_zero] at h; norm_cast at h; omega
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hd'
  have hrT := mem_of_root T p hp r hr
  refine ⟨⟨r, hrT⟩, ?_⟩
  apply IsFractionRing.injective T K
  rw [map_zero, ← eval₂_hom, ← eval_map]
  exact hr

theorem prod_lt (s : Multiset K) (hs : ∀ r ∈ s, T.valuation r ≤ 1) (h : T.valuation s.prod < 1) :
    ∃ r ∈ s, T.valuation r < 1 := by
  by_contra hc
  push_neg at hc
  have : T.valuation s.prod = 1 := by
    rw [map_multiset_prod]
    apply Multiset.prod_eq_one
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    exact le_antisymm (hs r hr) (hc r hr)
  rw [this] at h; exact lt_irrefl _ h

theorem hens : HenselianLocalRing T where
  is_henselian := by
    intro f hf a₀ h₁ _
    set q := f.map (algebraMap T K)
    have he : (algebraMap T K) (f.eval a₀) = (q.roots.map (fun r => (a₀ : K) - r)).prod := by
      rw [← eval₂_hom, ← eval_map]
      exact (IsAlgClosed.splits q).eval_eq_prod_roots_of_monic (hf.map _) _
    have hmem : ∀ r ∈ q.roots, r ∈ T := fun r hr =>
      mem_of_root T f hf r ((mem_roots (hf.map _).ne_zero).mp hr)
    have hlt : T.valuation (q.roots.map (fun r => (a₀ : K) - r)).prod < 1 := by
      rw [← he]; exact (T.valuation_lt_one_iff _).mp h₁
    obtain ⟨x, hx, hxv⟩ := prod_lt T _ (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact (T.valuation_le_one_iff _).mpr (T.sub_mem a₀.2 (hmem r hr))) hlt
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    refine ⟨⟨r, hmem r hr⟩, ?_, ?_⟩
    · have h0 := (mem_roots (hf.map _).ne_zero).mp hr
      apply IsFractionRing.injective T K
      rw [map_zero, ← eval₂_hom, ← eval_map]
      exact h0
    · rw [T.valuation_lt_one_iff]
      have hc : (((⟨r, hmem r hr⟩ : T) - a₀ : T) : K) = -((a₀ : K) - r) := by push_cast; ring
      rw [hc, Valuation.map_neg]
      exact hxv

end LateralTheory.KummerTheory.ValAICPf

theorem LateralTheory.KummerTheory.ValAIC_of : LateralTheory.KummerTheory.ValAIC := fun K _ _ T => ⟨LateralTheory.KummerTheory.ValAICPf.aic T, LateralTheory.KummerTheory.ValAICPf.hens T⟩

theorem LateralTheory.KummerTheory.Place_of_ex (h : LateralTheory.KummerTheory.PlaceEx) : LateralTheory.KummerTheory.Place :=
  LateralTheory.KummerTheory.Place_of h LateralTheory.KummerTheory.ValAIC_of
