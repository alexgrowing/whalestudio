import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinaryIdeal_saturators_conj_invariant : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG 3 C) (h : GL (Fin 3) C), HasMult D.η r → GlobalTheory.OrdLoc.ordIdeal D (conjBy h r) = GlobalTheory.OrdLoc.ordIdeal D r ∧ (∀ a, GlobalTheory.OrdLoc.dd D (conjBy h r) a = GlobalTheory.OrdLoc.dd D r a) ∧ GlobalTheory.OrdLoc.del D (conjBy h r) = GlobalTheory.OrdLoc.del D r := by
  intro l _ O _ _ _ D C _ _ r h hr
  have hone : ∀ s ∈ D.HL, (r s).right = 1 := by
    intro s hs
    rw [hr s]
    exact MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).1
  have hmat := fun s (hs : s ∈ D.HL) => GlobalTheory.OrdLoc.conjBy_mat h r s (hone s hs)
  have hsh : ∀ s ∈ D.HL, ∀ a, D.sh (conjBy h r) a s =
      (h : Matrix (Fin 3) (Fin 3) C) * D.sh r a s * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro s hs a
    simp only [UpperTheory.V.Loc.Dat3.sh]
    rw [hmat s hs, GlobalTheory.OrdLoc.conj_sub_scalar]
  have hs0 : D.s0 ∈ D.HL := (GlobalTheory.OrdLoc.hl_basic D).2.2.2.2.1
  obtain ⟨hfr, -⟩ := (GlobalTheory.OrdLoc.fr_isFr D).1
  have htr : ∀ a, D.tr (conjBy h r) a = D.tr r a := by
    intro a
    simp only [UpperTheory.V.Loc.Dat3.tr]
    rw [hsh _ hs0, hsh _ hs0, hmat _ hfr, GlobalTheory.OrdLoc.conj_mul_three_alt, GlobalTheory.OrdLoc.trace_conj]
  have hdd : ∀ a, D.dd (conjBy h r) a = D.dd r a := by
    intro a
    simp only [UpperTheory.V.Loc.Dat3.dd, htr]
  have hprod : ∀ t : Fin 3 → GQ l, (∀ a, t a ∈ D.HL ⊓ Iq l) →
      D.sh (conjBy h r) 0 (t 0) * D.sh (conjBy h r) 1 (t 1) * D.sh (conjBy h r) 2 (t 2) =
        (h : Matrix (Fin 3) (Fin 3) C) * (D.sh r 0 (t 0) * D.sh r 1 (t 1) * D.sh r 2 (t 2)) *
          ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro t ht
    rw [hsh _ (Subgroup.mem_inf.1 (ht 0)).1, hsh _ (Subgroup.mem_inf.1 (ht 1)).1,
      hsh _ (Subgroup.mem_inf.1 (ht 2)).1, GlobalTheory.OrdLoc.conj_mul_three_alt]
  refine ⟨?_, hdd, by simp only [UpperTheory.V.Loc.Dat3.del, hdd]⟩
  unfold UpperTheory.V.Loc.Dat3.ordIdeal
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (⟨s, hs, i, rfl⟩ | ⟨t, ht, i, j, rfl⟩)
    · exact Ideal.subset_span
        (Or.inl ⟨s, hs, i, by rw [hmat s (Subgroup.mem_inf.1 hs).1, GlobalTheory.OrdLoc.charpoly_conj]⟩)
    · rw [hprod t ht]
      apply GlobalTheory.OrdLoc.ent_mem_mul
      intro a b
      exact Ideal.subset_span (Or.inr ⟨t, ht, a, b, rfl⟩)
  · rw [Ideal.span_le]
    rintro x (⟨s, hs, i, rfl⟩ | ⟨t, ht, i, j, rfl⟩)
    · exact Ideal.subset_span
        (Or.inl ⟨s, hs, i, by rw [hmat s (Subgroup.mem_inf.1 hs).1, GlobalTheory.OrdLoc.charpoly_conj]⟩)
    · rw [GlobalTheory.OrdLoc.unconj h (D.sh r 0 (t 0) * D.sh r 1 (t 1) * D.sh r 2 (t 2)), ← hprod t ht]
      apply GlobalTheory.OrdLoc.ent_mem_mul
      intro a b
      exact Ideal.subset_span (Or.inr ⟨t, ht, a, b, rfl⟩)
