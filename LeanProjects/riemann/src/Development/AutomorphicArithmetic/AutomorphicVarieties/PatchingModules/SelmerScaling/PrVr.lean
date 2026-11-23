import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prVr :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ g (i j : Fin S.n), S.rF (S.pr0 (S.U.vr g i j)) = S.ρ S.F g i j ∧ ((((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr1 (S.U.vr g i j) = 0) ∧ (¬ (((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr0 (S.U.vr g i j) = 0) := by
  intro l _ S g i j
  have hm : S.U.vr g ∈ blkMat S.n S.x.a (1 : Submodule S.Bh S.U.AA) S.U.N := by
    rw [← S.U.span]; exact Submodule.subset_span ⟨g, rfl⟩
  have hN : S.U.vr g i j - algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ S.U.N := (S.pr1 (S.U.vr g i j)).2
  have hd := Submodule.disjoint_def.1 S.U.compl.disjoint
  have h1 : algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ (1 : Submodule S.Bh S.U.AA) :=
    Submodule.mem_one.2 ⟨_, rfl⟩
  refine ⟨S.U.red g i j _ hN, fun e => ?_, fun e => ?_⟩
  · exact Subtype.ext (hd _ (Submodule.sub_mem _ ((hm i j).1 e) h1) hN)
  · apply S.U.inj
    rw [map_zero]
    refine hd _ h1 ?_
    have := S.U.N.sub_mem ((hm i j).2 e) hN
    rwa [sub_sub_cancel] at this
