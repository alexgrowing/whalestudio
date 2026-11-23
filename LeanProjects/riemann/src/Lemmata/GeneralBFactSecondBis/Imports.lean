import Mathlib
import Formalism.CyclotomicNorms.StatementT
import Formalism.GaloisIrreducibility.NoSolvableTransitive

namespace Bl.general_b_fact_second_bis

theorem goal1 :
  ∀ {g : Nat} [hg : Fact (Nat.Prime g)] (c : Formalism.CyclotomicNorms.Fbar g),
  Eq.{1} (HPow.hPow.{0, 0, 0} c g) c →
    Membership.mem.{0, 0}
      (Set.range.{0, 1} (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} (ZMod g) (Formalism.CyclotomicNorms.Fbar g)))) c := by
  intro g hg c hc
  classical
  have hp : 1 < g := hg.out.one_lt
  set f : Polynomial (Formalism.CyclotomicNorms.Fbar g) := Polynomial.X ^ g - Polynomial.X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero (Formalism.CyclotomicNorms.Fbar g) hp
  have hroot : ∀ x : Formalism.CyclotomicNorms.Fbar g, x ^ g = x → x ∈ f.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot.def, hf,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hx, sub_self]
  by_contra hcn
  have hinj : Function.Injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) :=
    (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
  set S : Finset (Formalism.CyclotomicNorms.Fbar g) := Finset.univ.image (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) with hS
  have hScard : S.card = g := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  have hcS : c ∉ S := by
    intro h
    apply hcn
    rw [hS, Finset.mem_image] at h
    obtain ⟨a, -, ha⟩ := h
    exact ⟨a, ha⟩
  have hsub : insert c S ⊆ f.roots.toFinset := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hroot x hc
    · rw [hS, Finset.mem_image] at hx
      obtain ⟨a, -, rfl⟩ := hx
      apply hroot
      rw [← map_pow, ZMod.pow_card]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hcS, hScard] at h1
  have h2 : f.roots.toFinset.card ≤ g :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' f).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq (Formalism.CyclotomicNorms.Fbar g) hp).le)
  omega

end Bl.general_b_fact_second_bis
