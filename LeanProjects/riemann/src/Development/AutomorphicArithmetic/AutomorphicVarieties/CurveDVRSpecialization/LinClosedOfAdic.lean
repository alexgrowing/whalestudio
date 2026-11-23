import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

set_option maxHeartbeats 1000000 in
open IsLocalRing Filter Topology in
theorem UpperTheory.V.Pr.linClosedOfAdic :
    UpperTheory.V.Pr.LinClosedOfAdic := by
  intro G A κ _ _ _ _ _ _ j hj n a ha f
  classical
  let e : (Fin n × Fin n → A) → Matrix (Fin n) (Fin n) κ :=
    fun y => Matrix.of fun s t => j (y (s, t))
  let K : Submodule A (Fin n × Fin n → A) :=
    { carrier := {y | f (e y) = 0}
      add_mem' := by
        intro x y hx hy
        have h : e (x + y) = e x + e y := by
          ext s t
          simp [e]
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [h, map_add, hx, hy, add_zero]
      zero_mem' := by
        have h : e 0 = 0 := by
          ext s t
          simp [e]
        simp only [Set.mem_setOf_eq]
        rw [h, map_zero]
      smul_mem' := by
        intro r x hx
        have h : e (r • x) = j r • e x := by
          ext s t
          simp [e]
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [h, map_smul, hx, smul_zero] }
  let y : G → (Fin n × Fin n → A) := fun g p => a g p.1 p.2
  have hy : ∀ g, (a g).map j = e (y g) := fun g => by
    ext s t
    simp [e, y]
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro g0 hg0
  have hK : K.mkQ (y g0) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    intro h
    apply hg0
    show f ((a g0).map j) = 0
    rw [hy]
    exact h
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := A)
    (M := (Fin n × Fin n → A) ⧸ K) (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
  obtain ⟨N, hN⟩ : ∃ N : ℕ, K.mkQ (y g0) ∉
      (maximalIdeal A ^ N • ⊤ : Submodule A ((Fin n × Fin n → A) ⧸ K)) := by
    by_contra h
    push_neg at h
    apply hK
    have hm : K.mkQ (y g0) ∈
        (⨅ i : ℕ, maximalIdeal A ^ i • ⊤ : Submodule A ((Fin n × Fin n → A) ⧸ K)) :=
      Submodule.mem_iInf _ |>.mpr h
    rw [hbot] at hm
    exact (Submodule.mem_bot A).mp hm
  let U : Set G := ⋂ p : Fin n × Fin n, {g | Ideal.Quotient.mk (maximalIdeal A ^ N) (a g p.1 p.2) =
    Ideal.Quotient.mk (maximalIdeal A ^ N) (a g0 p.1 p.2)}
  refine ⟨U, ?_, ?_, ?_⟩
  · intro g hg hgS
    apply hN
    have hd : ∀ p, y g p - y g0 p ∈ maximalIdeal A ^ N := by
      intro p
      have hp := Set.mem_iInter.mp hg p
      simp only [Set.mem_setOf_eq] at hp
      rw [← Ideal.Quotient.eq]
      exact hp
    have h0 : K.mkQ (y g) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      show f (e (y g)) = 0
      rw [← hy]
      exact hgS
    have hsum : y g - y g0 = ∑ p, (y g p - y g0 p) • Pi.single p (1 : A) := by
      funext q
      rw [Finset.sum_apply]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hmem : K.mkQ (y g - y g0) ∈
        (maximalIdeal A ^ N • ⊤ : Submodule A ((Fin n × Fin n → A) ⧸ K)) := by
      rw [hsum, map_sum]
      refine Submodule.sum_mem _ fun p _ => ?_
      rw [LinearMap.map_smul]
      exact Submodule.smul_mem_smul (hd p) Submodule.mem_top
    rw [map_sub, h0, zero_sub] at hmem
    exact neg_mem_iff.mp hmem
  · apply isOpen_iInter_of_finite
    intro p
    exact (ha p.1 p.2 N).isOpen_fiber _
  · exact Set.mem_iInter.mpr fun p => rfl
