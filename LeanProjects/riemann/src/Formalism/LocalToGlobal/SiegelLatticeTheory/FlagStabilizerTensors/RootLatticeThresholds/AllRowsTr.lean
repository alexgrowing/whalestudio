import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsGA

noncomputable section

open MonoidAlgebra

namespace Formalism.L2.SG.Pf.AllRowsTr

open Formalism.L2.SG.Pf.AllRowsGA

section One

variable {G : Type} [Group G] [Fintype G]

theorem tau_mul_comm (a b : MonoidAlgebra ℂ G) : (a * b).coeff 1 = (b * a).coeff 1 := by
  rw [coeff_mul_fin, coeff_mul_fin]
  simp only [mul_one]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun h => by rw [Equiv.inv_apply, inv_inv, mul_comm])

theorem tau_conj (P : G) (a : MonoidAlgebra ℂ G) :
    (MonoidAlgebra.single P 1 * a * MonoidAlgebra.single P⁻¹ 1).coeff 1 = a.coeff 1 := by
  rw [tau_mul_comm, ← mul_assoc, MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul,
    ← MonoidAlgebra.one_def, one_mul]

theorem tau_normSq (x : MonoidAlgebra ℂ G) :
    (conjA x * x).coeff 1 = ((∑ h : G, Complex.normSq (x.coeff h) : ℝ) : ℂ) := by
  rw [coeff_mul_fin, Complex.ofReal_sum]
  simp only [conjA_coeff, mul_one]
  exact Fintype.sum_equiv (Equiv.inv G) _ _
    (fun h => by rw [Equiv.inv_apply, Complex.star_def, mul_comm, Complex.mul_conj])

theorem tau_proj (a e : MonoidAlgebra ℂ G) (ha : a * a = a) (hsa : conjA a = a) (he : e * e = e)
    (hc : ∀ y, e * y = y * e) (hse : conjA e = e) :
    (a * e).coeff 1 = ((∑ h : G, Complex.normSq ((a * e).coeff h) : ℝ) : ℂ) := by
  have hx : conjA (a * e) * (a * e) = a * e := by
    rw [conjA_mul, hse, hsa, mul_assoc, ← mul_assoc a a e, ha, ← mul_assoc, hc a, mul_assoc, he]
  rw [← tau_normSq (a * e), hx]

end One

section Prod

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]

def pA (f : ∀ i, MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun γ => ∏ i, (f i).coeff (γ i))

theorem pA_coeff (f : ∀ i, MonoidAlgebra ℂ (G i)) (γ : ∀ i, G i) : (pA f).coeff γ = ∏ i, (f i).coeff (γ i) := by
  simp [pA, MonoidAlgebra.coeff_ofCoeff]

theorem pA_mul (f g : ∀ i, MonoidAlgebra ℂ (G i)) : pA f * pA g = pA (fun i => f i * g i) := by
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin, pA_coeff]
  simp only [pA_coeff, coeff_mul_fin]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.prod_mul_distrib]
  rfl

theorem pA_one_coeff (f : ∀ i, MonoidAlgebra ℂ (G i)) : (pA f).coeff 1 = ∏ i, (f i).coeff 1 := by
  rw [pA_coeff]
  rfl

end Prod

end Formalism.L2.SG.Pf.AllRowsTr
