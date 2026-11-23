import Mathlib
import Formalism.SharpRestriction.GrowthBounds.ColumnSystems
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm
import Formalism.SharpRestriction.GrowthBounds.ObjSeg
import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinalTheorems

private theorem UpperTheory.Reformulated.B.SymmetricFamilySpan.prod_span_mem {R A ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [Fintype ι] {V : ι → Type*} [∀ j, AddCommMonoid (V j)] [∀ j, Module R (V j)] (L : ∀ j, V j →ₗ[R] A)
    (G : ∀ j, Set (V j)) (M : Submodule R A) (h : ∀ s : ∀ j, V j, (∀ j, s j ∈ G j) → ∏ j, L j (s j) ∈ M)
    (s : ∀ j, V j) (hs : ∀ j, s j ∈ Submodule.span R (G j)) : ∏ j, L j (s j) ∈ M := by
  have h1 : ∏ j, L j (s j) ∈ ∏ j, Submodule.span R (L j '' G j) :=
    Finset.prod_hom_rel (r := fun (a : A) (N : Submodule R A) => a ∈ N) (Submodule.one_le.1 le_rfl)
      (fun j a N ha => Submodule.mul_mem_mul (Submodule.apply_mem_span_image_of_mem_span _ (hs j)) ha)
  rw [Submodule.prod_span] at h1
  refine Submodule.span_le.2 (fun x hx => ?_) h1
  obtain ⟨f, hf, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
  choose t ht e using hf
  simpa only [e, SetLike.mem_coe] using h t ht

theorem UpperTheory.Reformulated.B.SymmetricFamilySpan.symFam_span :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] {C0 CE1 CE2 : ℝ}
    {X : Formalism.MainNotions.ColumnSystems.Loc} (β : Formalism.MainNotions.ColumnSystems.Pf.GlobalTheory X)
    (G :
      (j : Fin (Formalism.MainNotions.G.numSeg X.TT)) →
        Set
          (MvPolynomial (Formalism.MainNotions.G.BVar ((2 : ℕ) * Formalism.MainNotions.G.segS X.TT j + (1 : ℕ)) X.m (X.seg C0 CE1 CE2 j).t)
            (Formalism.MainNotions.G.KK O)))
    (M : Submodule O (MvPolynomial ((↥X.TT × Bool) × Fin (X.m + (1 : ℕ))) (Formalism.MainNotions.G.KK O))),
    (∀ (s : Formalism.MainNotions.ColumnSystems.Pf.Syms O C0 CE1 CE2 X),
        (∀ (j : Fin (Formalism.MainNotions.G.numSeg X.TT)), s j ∈ G j) → Formalism.MainNotions.ColumnSystems.Pf.symFam (Formalism.MainNotions.G.KK O) X.p C0 CE1 CE2 X β s ∈ M) →
      ∀ (s : Formalism.MainNotions.ColumnSystems.Pf.Syms O C0 CE1 CE2 X),
        (∀ (j : Fin (Formalism.MainNotions.G.numSeg X.TT)), s j ∈ Submodule.span O (G j)) →
          Formalism.MainNotions.ColumnSystems.Pf.symFam (Formalism.MainNotions.G.KK O) X.p C0 CE1 CE2 X β s ∈
            M := by
  intro O _ _ C0 CE1 CE2 X β G M h s hs
  open Formalism.MainNotions.ColumnSystems.Pf Formalism.MainNotions.G in exact UpperTheory.Reformulated.B.SymmetricFamilySpan.prod_span_mem (fun j =>
                                            (LinearMap.mulLeft O (digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j))).comp
                                            ((MvPolynomial.aeval (R := KK O) (fun v => MvPolynomial.X (symVar C0 CE1 CE2 X j v) ^
                                              symLev X.p C0 CE1 CE2 X j v)).toLinearMap.restrictScalars O)) G M h s hs
