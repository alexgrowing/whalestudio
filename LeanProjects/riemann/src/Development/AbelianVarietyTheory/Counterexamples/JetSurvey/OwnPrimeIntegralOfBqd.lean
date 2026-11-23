import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlace

noncomputable section

namespace GlobalTheory.OwnPrimeRam

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections

def hostOwnQ {R : Ranks} (H : Formalism.BasicNotions.Host R) (h15 : H.q % 15 = 1) (h' : H.q ≠ H.pde') (hg : ∀ i, H.q ≠ H.g i) :
    Formalism.BasicNotions.Host R :=
  { H with
    levelPrimes := insert H.q H.levelPrimes
    g_level := fun i => Finset.mem_insert_of_mem (H.g_level i)
    pde := H.q
    pde_prime := H.hyp.1
    pde_ne := h'
    pde_level := ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem H.pde_level.2⟩
    pde_mod := ⟨h15, H.pde_mod.2⟩
    pde_ne_g := fun i => ⟨hg i, (H.pde_ne_g i).2⟩
    level_coprimeS := by
      intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact (Nat.Coprime.coprime_mul_right_right H.QS_coprime).symm
      · exact H.level_coprimeS p hp
    ccK_coprime := by
      intro p hp
      apply H.ccK_coprime p
      simp only [Finset.mem_insert] at hp ⊢
      tauto }

example : Nat.Prime 211 ∧ 211 % 8 = 3 ∧ 211 % 15 = 1 := by norm_num

end GlobalTheory.OwnPrimeRam
