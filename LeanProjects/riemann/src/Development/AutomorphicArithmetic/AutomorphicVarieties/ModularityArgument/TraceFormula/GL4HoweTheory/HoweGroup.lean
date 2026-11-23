import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.V.Z.Tf.L4

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem mul_bd {X Y : Matrix (Fin n) (Fin n) E} {s : ValueGroupWithZero E}
    (hX : ∀ i j, valuation E (X i j) ≤ s) (hY : ∀ i j, valuation E (Y i j) ≤ 1) (i j : Fin n) :
    valuation E ((X * Y) i j) ≤ s := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  simpa using mul_le_mul' (hX i l) (hY l j)

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem one_bd (i j : Fin n) : valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem val_bd {g : GL (Fin n) E} (h : ∀ i j, valuation E ((g.val - 1) i j) < 1) (i j : Fin n) :
    valuation E (g.val i j) ≤ 1 := by
  have e : g.val i j = (g.val - 1) i j + (1 : Matrix (Fin n) (Fin n) E) i j := by simp
  rw [e]
  exact Valuation.map_add_le _ (h i j).le (one_bd i j)

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem inv_bd {g : GL (Fin n) E} (h : ∀ i j, valuation E ((g.val - 1) i j) < 1) (i j : Fin n) :
    valuation E ((g⁻¹).val i j) ≤ 1 := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => valuation E ((g⁻¹).val i j)) ⟨i, Finset.mem_univ _⟩
  refine (hm i (Finset.mem_univ _)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : 0 < valuation E ((g⁻¹).val m j) := lt_of_le_of_lt zero_le hlt
  have e0 : (g⁻¹).val = 1 - (g.val - 1) * (g⁻¹).val := by
    rw [sub_mul, Units.mul_inv]; noncomm_ring
  have e : (g⁻¹).val m j = (1 : Matrix (Fin n) (Fin n) E) m j - ((g.val - 1) * (g⁻¹).val) m j :=
    congrFun (congrFun e0 m) j
  have h1 : valuation E (((g.val - 1) * (g⁻¹).val) m j) < valuation E ((g⁻¹).val m j) := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ h0.ne' fun l _ => ?_
    rw [map_mul]
    calc _ ≤ valuation E ((g.val - 1) m l) * valuation E ((g⁻¹).val m j) :=
          mul_le_mul' le_rfl (hm l (Finset.mem_univ _))
      _ < 1 * valuation E ((g⁻¹).val m j) := mul_lt_mul_of_pos_right (h _ _) h0
      _ = _ := one_mul _
  have h2 := Valuation.map_sub_lt (valuation E) ((one_bd m j).trans_lt hlt) h1
  rw [← e] at h2
  exact lt_irrefl _ h2

private def cg (n : ℕ) (c : Eˣ) (hc : valuation E (c : E) < 1) : Subgroup (GL (Fin n) E) where
  carrier := {g | ∀ i j, valuation E ((g.val - 1) i j) ≤ valuation E (c : E)}
  one_mem' := fun i j => by simp
  mul_mem' := by
    intro x y hx hy i j
    have e : (x * y).val - 1 = (x.val - 1) * y.val + (y.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e, Matrix.add_apply]
    exact Valuation.map_add_le _ (mul_bd hx (val_bd fun i j => (hy i j).trans_lt hc) i j) (hy i j)
  inv_mem' := by
    intro x hx i j
    have e : (x⁻¹).val - 1 = -((x.val - 1) * (x⁻¹).val) := by
      rw [sub_mul, Units.mul_inv]; noncomm_ring
    rw [e, Matrix.neg_apply, Valuation.map_neg]
    exact mul_bd hx (inv_bd fun i j => (hx i j).trans_lt hc) i j

private theorem isOpen_cg (n : ℕ) (c : Eˣ) (hc : valuation E (c : E) < 1) :
    IsOpen (cg n c hc : Set (GL (Fin n) E)) := by
  have e : (cg n c hc : Set (GL (Fin n) E)) =
      (fun g : GL (Fin n) E => ((c⁻¹ : Eˣ) : E) • (g.val - 1)) ⁻¹' {A : Matrix (Fin n) (Fin n) E | ∀ i j, A i j ∈ 𝒪[E]} := by
    ext g
    refine forall_congr' fun i => forall_congr' fun j => ?_
    change _ ↔ valuation E (((c⁻¹ : Eˣ) : E) * (g.val - 1) i j) ≤ 1
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀,
      inv_mul_le_one₀ ((Valuation.pos_iff _).2 c.ne_zero)]
  rw [e]
  have hc : Continuous fun g : GL (Fin n) E => ((c⁻¹ : Eˣ) : E) • (g.val - 1) :=
    (Units.continuous_val.sub continuous_const).const_smul ((c⁻¹ : Eˣ) : E)
  exact GlobalTheory.SplitFlip.isOpen_intMatrix.preimage hc

private theorem isCompact_cg (n : ℕ) (c : Eˣ) (hc : valuation E (c : E) < 1) :
    IsCompact (cg n c hc : Set (GL (Fin n) E)) :=
  GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_cg n c hc)) fun g hg =>
    (GlobalTheory.SplitFlip.mem_KO_iff g).2
      ⟨val_bd fun i j => (hg i j).trans_lt hc, inv_bd fun i j => (hg i j).trans_lt hc⟩

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem conj_entry (t : Fin n → Eˣ) (g : GL (Fin n) E) (i j : Fin n) :
    ((GlobalTheory.SplitFlip.diagGL t * g * (GlobalTheory.SplitFlip.diagGL t)⁻¹).val - 1) i j =
      (g.val i j - (1 : Matrix (Fin n) (Fin n) E) i j) * ((t i * (t j)⁻¹ : Eˣ) : E) := by
  have e : (GlobalTheory.SplitFlip.diagGL t * g * (GlobalTheory.SplitFlip.diagGL t)⁻¹).val =
      (Matrix.diagonal fun i => (t i : E)) * g.val * Matrix.diagonal fun i => (((t i)⁻¹ : Eˣ) : E) := rfl
  rw [e, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i = j
  · subst h
    simp [sub_mul, mul_right_comm]
  · simp [Matrix.one_apply_ne h]
    ring

end UpperTheory.V.Z.Tf.L4

theorem UpperTheory.V.Z.Tf.L4.howeGroup :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∃ J : Subgroup (GL (Fin n) E), (J : Set (GL (Fin n) E)) = howeSet n ϖ a c ∧ IsOpen (J : Set (GL (Fin n) E)) ∧ IsCompact (J : Set (GL (Fin n) E)) := by
  intro E _ _ _ _ n ϖ hϖ a c ha
  have hlt : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    exact zpow_lt_one₀ (by rw [← hϖ]; exact (Valuation.pos_iff _).2 ϖ.ne_zero) uniformizer_lt_one (by omega)
  let t : Fin n → Eˣ := fun i => ϖ ^ (-(c * ((i : ℕ) : ℤ)))
  let d : GL (Fin n) E := GlobalTheory.SplitFlip.diagGL t
  let φ : GL (Fin n) E ≃ₜ GL (Fin n) E := (Homeomorph.mulLeft d).trans (Homeomorph.mulRight d⁻¹)
  refine ⟨(cg n (ϖ ^ a) hlt).comap (MulAut.conj d).toMonoidHom, ?_, (isOpen_cg n _ hlt).preimage φ.continuous,
    φ.isCompact_preimage.2 (isCompact_cg n _ hlt)⟩
  ext g
  change (∀ i j, valuation E (((d * g * d⁻¹).val - 1) i j) ≤ valuation E ((ϖ ^ a : Eˣ) : E)) ↔ _
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have e : (ϖ ^ a : Eˣ) = ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) * (t i * (t j)⁻¹) := by
    simp only [t]
    rw [← zpow_neg, ← zpow_add, ← zpow_add]
    congr 1
    ring
  rw [conj_entry, e, Units.val_mul (ϖ ^ (a + _)), map_mul, map_mul]
  exact mul_le_mul_iff_left₀ ((Valuation.pos_iff (valuation E)).2 (t i * (t j)⁻¹).ne_zero)
