import Mathlib

theorem UpperTheory.Reformulated.B.Qf31.isCompact_box :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
    [ProperSpace L] (c : Matrix (Fin m) (Fin m) L) (r : ℝ),
    IsCompact
      {g : GL (Fin m) L |
        (∀ (i j : Fin m), ‖(↑g : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r) ∧
          ∀ (i j : Fin m), ‖(↑g⁻¹ : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r} := by
  intro L _ _ m _ c r
  have hK : IsCompact {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} := by
    have h : IsCompact (Set.univ.pi fun i : Fin m =>
        Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall (c i j) r
    have e : {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} =
        (Set.univ.pi fun i : Fin m =>
          Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) := by
      ext A
      constructor
      · intro hA i _ j _
        exact mem_closedBall_iff_norm.2 (hA i j)
      · intro hA i j
        exact mem_closedBall_iff_norm.1 (hA i (Set.mem_univ i) j (Set.mem_univ j))
    rw [e]
    exact h
  have hK' : IsCompact (MulOpposite.unop ⁻¹'
      {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r}) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin m) (Fin m) L)).symm.isCompact_preimage.2 hK
  exact (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin m) (Fin m) L)).isCompact_preimage (hK.prod hK')
