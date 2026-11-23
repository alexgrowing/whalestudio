import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne

theorem UpperTheory.Reformulated.B.Qm13.cov_of_local :
    ∀ {O : Type} [inst : CommRing O] {X : AlgebraicGeometry.Scheme} (Q : X.Opens → Prop)
    (q : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of O)) [AlgebraicGeometry.IsSeparated q]
    [AlgebraicGeometry.QuasiCompact q],
    (∀ (x : ↥X), ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ Q V ∧ Nonempty (CrystallineSemistableComparison.Pb.Coord q V d)) →
      ∃ (U : CrystallineSemistableComparison.Pb.Cov q),
        ∀ (α : U.ι),
          Q
            (U.U
              α) := by
  intro O _ X Q q _ _ h
  choose V d hx hQ hc using h
  have : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace q
  have : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from q]; infer_instance⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨⟨s, fun a => V a, fun a => d a, fun a => (hc a).some, ?_, fun S hS => ?_⟩, fun a => hQ _⟩
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  · exact AlgebraicGeometry.IsAffineOpen.biInf (S : Set s) S.finite_toSet hS
      fun a _ => (hc a).some.affine
