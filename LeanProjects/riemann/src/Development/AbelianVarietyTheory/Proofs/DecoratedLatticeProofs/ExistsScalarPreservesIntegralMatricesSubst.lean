import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section
namespace GlobalTheory.LocOm

theorem exists_integral_multiplier {k : Type} [Field k] [ValuativeRel k] (a : k) :
    ∃ b : k, b ≠ 0 ∧ b ∈ 𝒪[k] ∧ b * a ∈ 𝒪[k] := by
  by_cases ha : a ∈ 𝒪[k]
  · exact ⟨1, one_ne_zero, Subring.one_mem _, by simpa using ha⟩
  · have ha0 : a ≠ 0 := by rintro rfl; exact ha (Subring.zero_mem _)
    refine ⟨a⁻¹, inv_ne_zero ha0, ?_, by simp [ha0, Subring.one_mem]⟩
    rw [Valuation.mem_integer_iff] at ha ⊢
    rw [map_inv₀]
    push_neg at ha
    exact inv_le_one_of_one_le₀ ha.le

theorem exists_common_integral_multiplier {k : Type} [Field k] [ValuativeRel k]
    {ι : Type} [Fintype ι] (f : ι → k) :
    ∃ c : k, c ≠ 0 ∧ c ∈ 𝒪[k] ∧ ∀ i, c * f i ∈ 𝒪[k] := by
  classical
  choose b hb0 hbO hbf using fun i => exists_integral_multiplier (f i)
  refine ⟨∏ i, b i, Finset.prod_ne_zero_iff.mpr fun i _ => hb0 i,
    Subring.prod_mem _ fun i _ => hbO i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i), mul_comm (b i), mul_assoc]
  exact Subring.mul_mem _ (Subring.prod_mem _ fun j _ => hbO j) (hbf i)

theorem enl_scalar_denominator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k), ∃ c : kˣ, ∀ zk : GL Y k, (zk : Matrix Y Y k) = (c : k) • (1 : Matrix Y Y k) → Enl gk (hk * zk⁻¹) ∧ Enl (1 : GL Y' k) zk⁻¹ := by
  intro k _ _ _ _ Y Y' _ _ _ _ gk hk
  obtain ⟨c, hc0, hcO, hc⟩ := exists_common_integral_multiplier
    (fun p : Y × Y × Y' × Y' => (↑(hk⁻¹) : Matrix Y Y k) p.1 p.2.1 * (↑gk : Matrix Y' Y' k) p.2.2.1 p.2.2.2)
  refine ⟨Units.mk0 c hc0, fun zk hz => ⟨?_, ?_⟩⟩
  · intro x hx r q
    have : ((↑((hk * zk⁻¹)⁻¹) : Matrix Y Y k)) = c • (↑(hk⁻¹) : Matrix Y Y k) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hz]
      simp
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Subring.sum_mem _ fun t _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Subring.sum_mem _ fun s _ => ?_
    have h1 := hc (r, s, t, q)
    have h2 := hx s t
    simp only at h1
    have : c * ((↑(hk⁻¹) : Matrix Y Y k) r s * x s t * (↑gk : Matrix Y' Y' k) t q) =
      (c * ((↑(hk⁻¹) : Matrix Y Y k) r s * (↑gk : Matrix Y' Y' k) t q)) * x s t := by ring
    rw [this]
    exact Subring.mul_mem _ h1 h2
  · intro x hx r q
    rw [inv_inv, hz]
    simp only [Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      smul_eq_mul, Units.val_mk0]
    exact Subring.mul_mem _ hcO (hx r q)

end GlobalTheory.LocOm
end
