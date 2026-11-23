import Mathlib
import ReciprocityTheory.Chebotarev.CycStatement
import ReciprocityTheory.Chebotarev.CrossGal
import ReciprocityTheory.Chebotarev.CrossLift
import ReciprocityTheory.Chebotarev.CrossFix
import ReciprocityTheory.Chebotarev.CrossFrobE
import ReciprocityTheory.Chebotarev.CrossRes
import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt

open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem exists_unit_orderOf_eq (l : ℕ) [Fact l.Prime] : ∃ τ : (ZMod l)ˣ, orderOf τ = l - 1 := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  refine ⟨τ, ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_eq_fintype_card, ZMod.card_units]

theorem cross : CycStatement → Statement := by
  intro hB K _ _ _ σ T
  obtain ⟨N, hN⟩ := exists_forall_isUnramifiedAt_of_liesOver K
  obtain ⟨N', hN'⟩ := exists_forall_cyclotomic_irreducible K
  have hk : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  obtain ⟨l, hlp, hlgt, hlmod⟩ := Nat.exists_prime_gt_modEq_one (max N' (T.sup id)) hk
  have : Fact l.Prime := ⟨hlp⟩
  have hσ : orderOf σ ∣ l - 1 := (Nat.modEq_iff_dvd' hlp.one_lt.le).mp hlmod.symm
  have hirr : Irreducible (cyclotomic l K) := hN' l hlp (lt_of_le_of_lt (le_max_left _ _) hlgt)
  have : NeZero l := ⟨hlp.ne_zero⟩
  have := isGalois_cyclotomicField K l
  let M := CyclotomicField l K
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta l K M) l := IsCyclotomicExtension.zeta_spec l K M
  obtain ⟨τ, hτ⟩ := exists_unit_orderOf_eq l
  obtain ⟨g, hg, hgζ⟩ := exists_lift_pow (M := M) l hirr hζ σ τ
  let E := IntermediateField.fixedField (Subgroup.zpowers g)
  have hirrE : Irreducible (cyclotomic l E) := irreducible_cyclotomic_fixedField hζ σ hσ τ hτ g hg hgζ
  obtain ⟨q, hq, hqp, hqT, hqmod⟩ := hB E l hirrE τ (T ∪ Finset.range (N + 1) ∪ {l})
  have hql : Ideal.absNorm q ≠ l := fun h => hqT (by simp [h])
  obtain ⟨P, hP, φ, hPp, hφζ, hφ⟩ := exists_frob_above E l hζ q hq hqp hql
  have hφg : φ.restrictScalars ℚ = g := eq_of_apply_eq_pow hζ σ hσ τ hτ g hg hgζ φ _ hφζ hqmod
  rw [hφg] at hφ
  obtain ⟨hQ, hQp, hQf⟩ := isArithFrobAt_restrictNormal (K := K) g _ P hP hPp hφ
  rw [hg] at hQf
  refine ⟨Ideal.absNorm q, hqp, fun h => hqT (by simp [h]), P.under (𝓞 K), hQ, hQp, ?_, hQf⟩
  have := hQ
  have := hQp
  refine hN _ hqp ?_ _
  by_contra h
  exact hqT (by simp; omega)

end ReciprocityTheory.Cheb
