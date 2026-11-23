import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.TransExists

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.FoldDCUnfold.W

universe u

theorem dc_core {G : Type u} [Group G] (Γ S S' : Subgroup G) (hS : S ≤ Γ) (hS' : S' ≤ Γ)
    (R : Set G) (hR : IsDoubleTransversal Γ S S' R)
    (E : G → Set G) (hE : ∀ r ∈ R, IsRightTransversal S (stab S S' r) (E r))
    (p q : Σ r : R, E (r : G)) (s1 s2 : G) (hs1 : s1 ∈ S') (hs2 : s2 ∈ S')
    (heq : s1 * ((p.1 : G)⁻¹ * (p.2 : G)) = s2 * ((q.1 : G)⁻¹ * (q.2 : G))) :
    p = q ∧ s1 = s2 := by
  obtain ⟨⟨r, hr⟩, e, he⟩ := p
  obtain ⟨⟨r', hr'⟩, e', he'⟩ := q
  change s1 * (r⁻¹ * e) = s2 * (r'⁻¹ * e') at heq
  have heS : e ∈ S := (hE r hr).1 he
  have heS' : e' ∈ S := (hE r' hr').1 he'
  have hrr : (⟨r, hr⟩ : R) = ⟨r', hr'⟩ := by
    refine (hR.2 r (hR.1 hr)).unique ⟨1, S.one_mem, 1, S'.one_mem, by simp⟩
      ⟨e * e'⁻¹, S.mul_mem heS (S.inv_mem heS'), s2⁻¹ * s1, S'.mul_mem (S'.inv_mem hs2) hs1, ?_⟩
    calc e * e'⁻¹ * r' * (s2⁻¹ * s1) = e * (s2 * (r'⁻¹ * e'))⁻¹ * s1 := by group
      _ = e * (s1 * (r⁻¹ * e))⁻¹ * s1 := by rw [heq]
      _ = r := by group
  have hrr' : r = r' := congrArg Subtype.val hrr
  subst hrr'
  have hstab : e * e'⁻¹ ∈ stab S S' r := by
    refine Subgroup.mem_inf.mpr ⟨S.mul_mem heS (S.inv_mem heS'), ?_⟩
    rw [Subgroup.mem_comap]
    have h : r⁻¹ * (e * e'⁻¹) * r = s1⁻¹ * s2 := by
      calc r⁻¹ * (e * e'⁻¹) * r = s1⁻¹ * (s1 * (r⁻¹ * e)) * e'⁻¹ * r := by group
        _ = s1⁻¹ * (s2 * (r⁻¹ * e')) * e'⁻¹ * r := by rw [heq]
        _ = s1⁻¹ * s2 := by group
    show r⁻¹ * (e * e'⁻¹) * r⁻¹⁻¹ ∈ S'
    rw [inv_inv, h]
    exact S'.mul_mem (S'.inv_mem hs1) hs2
  have hee : e = e' := by
    have hu := ((hE r hr).2 e heS).unique (y₁ := (1, ⟨e, he⟩))
      (y₂ := (⟨e * e'⁻¹, hstab⟩, ⟨e', he'⟩)) (by simp) (by simp)
    exact congrArg (fun x => (x.2 : G)) hu
  subst hee
  exact ⟨rfl, mul_right_cancel heq⟩

theorem double_coset_translation : DCTrans.{u} := by
  intro G _ Γ S S' hS hS' R hR E hE
  have hEsub : ∀ r ∈ R, E r ⊆ (S : Set G) := fun r hr => (hE r hr).1
  refine ⟨fun p q hpq => ?_, ?_, fun γ hγ => ?_⟩
  · refine (dc_core Γ S S' hS hS' R hR E hE p q 1 1 S'.one_mem S'.one_mem ?_).1
    rw [one_mul, one_mul]
    exact hpq
  · rintro _ ⟨⟨⟨r, hr⟩, ⟨e, he⟩⟩, rfl⟩
    exact Γ.mul_mem (Γ.inv_mem (hR.1 hr)) (hS (hEsub r hr he))
  · obtain ⟨⟨r, hr⟩, ⟨s, hs, s', hs', hrep⟩, -⟩ := hR.2 γ⁻¹ (Γ.inv_mem hγ)
    change s * r * s' = γ⁻¹ at hrep
    obtain ⟨⟨⟨t, ht⟩, ⟨e, he⟩⟩, hte, -⟩ := (hE r hr).2 s⁻¹ (S.inv_mem hs)
    change t * e = s⁻¹ at hte
    have ht' : r⁻¹ * t * r ∈ S' := by
      have h2 := (Subgroup.mem_inf.mp ht).2
      rw [Subgroup.mem_comap] at h2
      change r⁻¹ * t * r⁻¹⁻¹ ∈ S' at h2
      rwa [inv_inv] at h2
    have hmem : s'⁻¹ * (r⁻¹ * t * r) ∈ S' := S'.mul_mem (S'.inv_mem hs') ht'
    have hγeq : s'⁻¹ * (r⁻¹ * t * r) * (r⁻¹ * e) = γ := by
      calc s'⁻¹ * (r⁻¹ * t * r) * (r⁻¹ * e) = s'⁻¹ * r⁻¹ * (t * e) := by group
        _ = s'⁻¹ * r⁻¹ * s⁻¹ := by rw [hte]
        _ = (s * r * s')⁻¹ := by group
        _ = γ := by rw [hrep, inv_inv]
    refine ⟨(⟨s'⁻¹ * (r⁻¹ * t * r), hmem⟩,
      ⟨r⁻¹ * e, ⟨⟨⟨r, hr⟩, ⟨e, he⟩⟩, rfl⟩⟩), hγeq, ?_⟩
    rintro ⟨⟨a, ha⟩, ⟨d, ⟨p, rfl⟩⟩⟩ hy
    obtain ⟨hp, ha'⟩ := dc_core Γ S S' hS hS' R hR E hE p ⟨⟨r, hr⟩, ⟨e, he⟩⟩ a
      (s'⁻¹ * (r⁻¹ * t * r)) ha hmem (hy.trans hγeq.symm)
    subst hp
    exact Prod.ext (Subtype.ext ha') (Subtype.ext rfl)

end PI.FoldDCUnfold.W
