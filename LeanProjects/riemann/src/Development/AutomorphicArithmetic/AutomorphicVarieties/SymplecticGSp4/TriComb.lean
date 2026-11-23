import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsThirdIndexLinkedPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GeAlgTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.tri_comb (P : Fin 4 → Fin 4 → Prop) (h1 : ∀ i, P i i)
    (h2 : ∀ i j k, P i j → P j k → P i k) (h3 : ∀ i j, P i j → P j.rev i.rev)
    (h4 : ∀ i j, lamW i ≠ lamW j → P i j → P j i → ∃ k, k ≠ i ∧ k ≠ j ∧ P i k ∧ P k i) :
    (∀ i j, P i j) ∨ (∀ i j, i ≠ j → P i j → ¬ P j i) ∨
      (P 0 2 ∧ P 2 0 ∧ ((∀ i j, lamW i < lamW j → ¬ P i j) ∨ ∀ i j, lamW j < lamW i → ¬ P i j)) := by
  have r01 : P 0 1 ↔ P 2 3 := ⟨h3 0 1, h3 2 3⟩
  have r10 : P 1 0 ↔ P 3 2 := ⟨h3 1 0, h3 3 2⟩
  have r02 : P 0 2 ↔ P 1 3 := ⟨h3 0 2, h3 1 3⟩
  have r20 : P 2 0 ↔ P 3 1 := ⟨h3 2 0, h3 3 1⟩
  have a01 := h4 0 1 (by decide)
  have a03 := h4 0 3 (by decide)
  have a21 := h4 2 1 (by decide)
  have a23 := h4 2 3 (by decide)
  have e0 := h1 0
  have e1 := h1 1
  have e2 := h1 2
  have e3 := h1 3
  simp only [Fin.exists_fin_succ, Fin.forall_fin_succ, lamW] at *
  simp at *
  grind (splits := 200)

theorem UpperTheory.V.GradeZeroInterpolatingElement.tri :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → ∀ r, D.EPt r → Irr r ∨ DiagType r ∨ (Ge r 0 2 ∧ Ge r 2 0 ∧ ((∀ i j, lamW i < lamW j → ¬ Ge r i j) ∨ ∀ i j, lamW j < lamW i → ¬ Ge r i j)) := by
  intro Ω _ _ _ l _ c D hD hP r hr
  obtain ⟨hm, -, -, -, -, he, -⟩ := ptIn D hD (PadicAlgCl l) r hr
  obtain ⟨-, h1, h2, h3, h5, -⟩ := geAlg (PadicAlgCl l) r _ hm he
  rw [h5]
  exact tri_comb (Ge r) h1 h2 h3 (exists_third_index_linked_pair D hD hP r hr)
