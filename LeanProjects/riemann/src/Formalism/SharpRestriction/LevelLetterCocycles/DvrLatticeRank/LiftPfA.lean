import Formalism.SharpRestriction.LevelLetterCocycles.LocalFormOfThreeInputs
import Formalism.SharpRestriction.LevelLetterCocycles.FinrankMaxUnramifiedSubfieldPadicFinExtPos

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CyclotomicLifting

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finite_roots_l : {x : Om l | x ^ (l ^ 1) = 1}.Finite := by
  classical
  have hl : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
  refine Set.Finite.subset (Polynomial.nthRoots (l ^ 1) (1 : Om l)).toFinset.finite_toSet ?_
  intro x hx
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hl]
  exact hx

theorem fd_Ks (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(Ks K 1) := by
  have h0 : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.finite_of_finrank_pos (Formalism.MainNotions.N.PreambleDegrees.finrank_maxUnramifiedSubfield_padicFinExt_pos K)
  have : Finite {x : Om l | x ^ (l ^ 1) = 1} := finite_roots_l.to_subtype
  have h1 : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}) :=
    IntermediateField.finiteDimensional_adjoin (fun x hx => by
      have hl : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
      apply IsIntegral.of_pow hl
      rw [show x ^ (l ^ 1) = 1 from hx]
      exact isIntegral_one)
  unfold Ks
  infer_instance

def cycL (K : FinExt l) : FinExt l := ⟨Ks K 1, fd_Ks K⟩

theorem cycL_val (K : FinExt l) : (cycL K).1 = Ks K 1 := rfl

theorem max_unramified_le_cyclotomic (K : FinExt l) : K0 K ≤ K0 (cycL K) :=
  le_inf (le_sup_left : K0 K ≤ Ks K 1) inf_le_right

theorem Ks_cycL (K : FinExt l) : Ks (cycL K) 1 = Ks K 1 := by
  apply le_antisymm
  · exact sup_le (inf_le_left : K0 (cycL K) ≤ (cycL K).1) le_sup_right
  · exact sup_le_sup_right (max_unramified_le_cyclotomic K) _

theorem cyclotomic_degree_max_unramified (K : FinExt l) : (K0 K).relfinrank (Ks K 1) = l - 1 := by
  have hp : 0 < finrank ℚ_[l] ↥(K0 K) := Formalism.MainNotions.N.PreambleDegrees.finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have h1 := IntermediateField.finrank_bot_mul_relfinrank (le_sup_left : K0 K ≤ Ks K 1)
  have h2 := Formalism.MainNotions.N.PreambleDegrees.finrank_Ks K one_pos
  rw [Nat.sub_self, pow_zero, one_mul] at h2
  exact Nat.eq_of_mul_eq_mul_left hp (h1.trans h2)

theorem max_unramified_cyclotomic_eq (K : FinExt l) : K0 (cycL K) = K0 K := by
  have h1 := cyclotomic_degree_max_unramified K
  have h2 := cyclotomic_degree_max_unramified (cycL K)
  rw [Ks_cycL] at h2
  have hm := IntermediateField.relfinrank_mul_relfinrank (max_unramified_le_cyclotomic K)
    (inf_le_left : K0 (cycL K) ≤ (cycL K).1)
  rw [cycL_val, h1, h2] at hm
  have hpos : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have h3 : (K0 K).relfinrank (K0 (cycL K)) = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [hm, one_mul])
  exact le_antisymm (IntermediateField.relfinrank_eq_one_iff.1 h3) (max_unramified_le_cyclotomic K)

theorem finrank_eq_relfinrank (K : FinExt l) :
    finrank ↥(K0 K) ↥K.1 = (K0 K).relfinrank K.1 := by
  have hle : K0 K ≤ K.1 := inf_le_left
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  exact LinearEquiv.finrank_eq
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem finrank_cycL (K : FinExt l) : finrank ↥(K0 (cycL K)) ↥(cycL K).1 = l - 1 := by
  rw [finrank_eq_relfinrank, cycL_val, ← Ks_cycL K, cyclotomic_degree_max_unramified]

end Formalism.MainNotions.N.Ln34.CyclotomicLifting

end
