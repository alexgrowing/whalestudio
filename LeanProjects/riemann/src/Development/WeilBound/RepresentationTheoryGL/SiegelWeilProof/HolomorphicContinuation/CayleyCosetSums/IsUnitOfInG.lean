import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CosetSumApply
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

theorem herm_herm (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  simp only [conjTranspose_apply, herm]
  apply Complex.ext <;> simp <;> ring

theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_left_inverse (B := -(JJ n * xᴴ * JJ n))
  rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc xᴴ, hx, IwaPf.JJ_mul_self, neg_neg]

def grOf (x : M2 n) (hx : InG x) : GR n := ⟨(isUnit_of_inG hx).unit, hx⟩

theorem mR_grOf (x : M2 n) (hx : InG x) : mR (grOf x hx) = x := IsUnit.unit_spec _

def nG (s : Fin n → Fin n → ℝ) : GR n := grOf (nU (herm s)) (HolB.inG_upper (herm_herm s))

theorem mR_nG (s : Fin n → Fin n → ℝ) : mR (nG s) = nU (herm s) := IsUnit.unit_spec _

private theorem continuous_herm_cayley_coset_sums : Continuous (fun s : Fin n → Fin n → ℝ => herm s) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [herm]
  fun_prop
private theorem continuous_nU_comp_herm :
    Continuous (fun s : Fin n → Fin n → ℝ => nU (herm s)) := by
  simp only [nU]
  exact Continuous.matrix_fromBlocks continuous_const continuous_herm_cayley_coset_sums continuous_const continuous_const

theorem continuous_nG : Continuous (nG (n := n)) := by
  show Continuous fun s => grOf (nU (herm s)) (HolB.inG_upper (herm_herm s))
  unfold grOf
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · simpa only [Function.comp_def, IsUnit.unit_spec] using continuous_nU_comp_herm
  · have hinv : ∀ s : Fin n → Fin n → ℝ,
        ((isUnit_of_inG (HolB.inG_upper (herm_herm s))).unit⁻¹ : GL (Fin n ⊕ Fin n) ℂ).val =
          nU (-herm s) := by
      intro s
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec]
      simp [nU, fromBlocks_multiply]
    have hc : Continuous (fun s : Fin n → Fin n → ℝ => nU (-herm s)) := by
      simp only [nU]
      exact Continuous.matrix_fromBlocks continuous_const continuous_herm_cayley_coset_sums.neg continuous_const
        continuous_const
    exact hc.congr fun s => (hinv s).symm

end PositivityTheory.Rg.Sw.HSt.FarP
