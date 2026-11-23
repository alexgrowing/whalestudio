import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuationEqOfAdm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnitStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem sUnits_union_sup_finPow_eq_top :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → AdmP p F S → Disjoint S T → (∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F))) → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ := by
  intro p F _ _ _ S T hp hS hST hA
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS.1
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  have key : ∀ v ∈ T, ∃ w ∈ sUnits F S,
      w⁻¹ * (a * x) ∈ powSub p (algebraMap F (v.adicCompletion F)) ∧
        ∀ v' ∈ T, v' ≠ v → w ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
    intro v hv
    obtain ⟨u, hu, hnu, hu'⟩ := hA v hv
    obtain ⟨k, r, hr⟩ := GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit p F v (algebraMap F (v.adicCompletion F) (u : F))
      (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)) hp (hS.2 v (hTS v hv))
      (by rw [hval]; exact (mem_sUnits F S u).1 hu v (hTS v hv))
      (by rw [hval]; exact hy v hv) (fun r h => hnu ⟨r, h⟩)
    refine ⟨u ^ k, pow_mem hu k, ⟨r, ?_⟩, fun v' hv' hne => pow_mem (hu' v' hv' hne) k⟩
    have hu0 : algebraMap F (v.adicCompletion F) (u : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, hr, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
      map_pow, inv_mul_cancel_left₀ (pow_ne_zero k hu0)]
  choose! w hwS hw1 hw2 using key
  have huU : ∏ v ∈ T, w v ∈ sUnits F (S ∪ T) := by
    refine prod_mem fun t ht => ?_
    rw [mem_sUnits]
    intro v hv
    exact (mem_sUnits F S _).1 (hwS t ht) v fun h => hv (Finset.mem_union_left _ h)
  have hsq : (∏ v ∈ T, w v)⁻¹ * (a * x) ∈ finPow p F T := by
    simp only [finPow, Subgroup.mem_iInf]
    intro v hv
    rw [← Finset.mul_prod_erase T w hv, mul_inv, mul_right_comm]
    refine mul_mem (hw1 v hv) (inv_mem (prod_mem fun t ht => ?_))
    exact hw2 t (Finset.mem_of_mem_erase ht) v hv (Finset.ne_of_mem_erase ht).symm
  have hx : x = ((∏ v ∈ T, w v) * a⁻¹) * ((∏ v ∈ T, w v)⁻¹ * (a * x)) := by
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, inv_mul_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup (mul_mem huU (inv_mem haU)) hsq

end GlobalTheory.CNorm
