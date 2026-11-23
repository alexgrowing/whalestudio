import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw.TypeDatum

section Mat

variable {κ : Type} [CommRing κ] {a b r t j : ℕ}

theorem blkOf_le {n : ℕ} (ea : a = r + j * t) (i : Fin n) (hi : i.val < a) : blkOf r t i ≤ j := by
  unfold blkOf
  split_ifs with h
  · exact Nat.zero_le _
  · have : (i.val - r) / t < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)
    omega

theorem blkOf_eq (ea : a = r + j * t) (eb : b = r + (j + 1) * t) (i : Fin b) (hi : a ≤ i.val) :
    blkOf r t i = j + 1 := by
  unfold blkOf
  have h2 := i.2
  rw [if_neg (by omega), Nat.div_eq_of_lt_le (k := j) (by omega) (by omega)]

theorem mem_twoBlockTriangular_of_blockTriangular (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {g : GL (Fin b) κ}
    (hg : g ∈ blockTri (blkOf r t)) : g ∈ blockTri (blk2 a) := by
  intro p q hpq
  refine hg ?_
  unfold blk2 at hpq
  have hq : q.val < a := by
    by_contra hq
    split_ifs at hpq <;> omega
  have hp : a ≤ p.val := by
    by_contra hp
    split_ifs at hpq <;> omega
  rw [blkOf_eq ea eb p hp]
  exact Nat.lt_succ_of_le (blkOf_le ea q hq)

theorem top_mem (hab : a ≤ b) {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a))
    (hg : g ∈ blockTri (blkOf r t)) : upperLeftBlock hab g ∈ blockTri (blkOf r t) := by
  rw [mem_blockTri]
  intro p q hpq
  rw [upper_block_val_submatrix hab h2]
  exact hg (show blkOf r t (Fin.castLE hab q) < blkOf r t (Fin.castLE hab p) from hpq)

theorem restrictTopBlock_restrictTopBlock (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a))
    (hg : g ∈ blockTri (blkOf r t)) : upperLeftBlock ha (upperLeftBlock hab g) = upperLeftBlock hb g := by
  apply Units.ext
  rw [upper_block_val_submatrix ha (blockTri_blkOf_le r t (top_mem hab h2 hg)), upper_block_val_submatrix hab h2, upper_block_val_submatrix hb (blockTri_blkOf_le r t hg)]
  rfl

theorem diagonalBlock_restrictTopBlock (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {g : GL (Fin b) κ}
    (hg : g ∈ blockTri (blkOf r t)) {c : ℕ} (hc : c ≤ j) :
    dBlk (blkOf r t) c (upperLeftBlock hab g) = dBlk (blkOf r t) c g := by
  have h2 := mem_twoBlockTriangular_of_blockTriangular ea eb hg
  apply Units.ext
  rw [diag_block_det_val c (top_mem hab h2 hg), diag_block_det_val c hg, upper_block_val_submatrix hab h2]
  have hlt : ∀ i : {i : Fin b // blkOf r t i = c}, i.1.val < a := fun i => by
    by_contra hi
    have := blkOf_eq ea eb i.1 (not_lt.1 hi)
    have := i.2
    omega
  let e : {i : Fin a // blkOf r t i = c} ≃ {i : Fin b // blkOf r t i = c} :=
    { toFun := fun i => ⟨Fin.castLE hab i.1, i.2⟩
      invFun := fun i => ⟨⟨i.1.val, hlt i⟩, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem det_top (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {g : GL (Fin b) κ}
    (hg : g ∈ blockTri (blkOf r t)) :
    Matrix.GeneralLinearGroup.det g =
      Matrix.GeneralLinearGroup.det (upperLeftBlock hab g) * dBlk (blkOf r t) (j + 1) g := by
  have h2 := mem_twoBlockTriangular_of_blockTriangular ea eb hg
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    diag_block_det_val _ hg, upper_block_val_submatrix hab h2,
    Matrix.twoBlockTriangular_det (g : Matrix (Fin b) (Fin b) κ) (fun i => i.val < a) (fun p hp q hq =>
      h2 (show blk2 a q < blk2 a p by simp [blk2, hp, hq]))]
  let e : Fin a ≃ {i : Fin b // i.val < a} :=
    { toFun := fun i => ⟨Fin.castLE hab i, i.2⟩
      invFun := fun i => ⟨i.1.val, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e' : {i : Fin b // blkOf r t i = j + 1} ≃ {i : Fin b // ¬ i.val < a} :=
    Equiv.subtypeEquivRight fun i =>
      ⟨fun h h' => by have := blkOf_le ea i h'; omega, fun h => blkOf_eq ea eb i (not_lt.1 h)⟩
  rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_submatrix_equiv_self e']
  rfl

theorem topL_apply (hab : a ≤ b) (y : Matrix (Fin b) (Fin a) κ) (p q : Fin a) :
    topL a y p q = y (Fin.castLE hab p) q := by
  unfold topL
  rw [dif_pos ⟨lt_of_lt_of_le p.2 hab, q.2⟩]
  rfl

theorem lowZero_mul {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a)) {y : Matrix (Fin b) (Fin a) κ}
    (hy : LowZero a y) (s : Matrix (Fin a) (Fin a) κ) : LowZero a (g.val * y * s) := by
  intro p q hp _
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_zero fun m _ => ?_, zero_mul]
  by_cases hm : m.val < a
  · rw [h2 (show blk2 a m < blk2 a p by simp [blk2, hm, not_lt.2 hp]), zero_mul]
  · rw [hy m l (not_lt.1 hm) l.2, mul_zero]

theorem topL_mul (hab : a ≤ b) {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a)) {y : Matrix (Fin b) (Fin a) κ}
    (hy : LowZero a y) (s : Matrix (Fin a) (Fin a) κ) :
    topL a (g.val * y * s) = (upperLeftBlock hab g).val * topL a y * s := by
  ext p q
  rw [topL_apply hab, upper_block_val_submatrix hab h2, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective (Fin.castLE hab) (Fin.castLE_injective hab) _ _ (fun m hm => ?_) fun m => ?_).symm
  · have hm' : ¬ m.val < a := fun h => hm ⟨⟨m.val, h⟩, by ext; rfl⟩
    rw [hy m l (not_lt.1 hm') l.2, mul_zero]
  · rw [topL_apply hab]; rfl

def IsTop (t : ℕ) (ha : r ≤ a) (y : Matrix (Fin b) (Fin a) κ) (g : GL (Fin a) κ) : Prop :=
  LowZero a y ∧ g.val = topL a y ∧ g ∈ blockTri (blkOf r t) ∧ upperLeftBlock ha g = 1

theorem IsTop.move (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {y : Matrix (Fin b) (Fin a) κ} {g gS : GL (Fin a) κ} {gT : GL (Fin b) κ} (h : IsTop t ha y g)
    (hS : gS ∈ blockTri (blkOf r t)) (hT : gT ∈ blockTri (blkOf r t)) (hST : upperLeftBlock ha gS = upperLeftBlock hb gT) :
    IsTop t ha ((gT⁻¹).val * y * gS.val) ((upperLeftBlock hab gT)⁻¹ * g * gS) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have t2 := mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := top_mem hab t2 hT
  have hinv : upperLeftBlock hab gT⁻¹ = (upperLeftBlock hab gT)⁻¹ := extendOne_inv _ t2
  refine ⟨lowZero_mul (Subgroup.inv_mem _ t2) h1 _, ?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3) hS, ?_⟩
  · rw [topL_mul hab (Subgroup.inv_mem _ t2) h1, hinv, ← h2, Units.val_mul, Units.val_mul]
  · have le := blockTri_blkOf_le (κ := κ) (n := a) r t
    have m1 : upperLeftBlock ha ((upperLeftBlock hab gT)⁻¹ * g * gS) = upperLeftBlock ha ((upperLeftBlock hab gT)⁻¹ * g) * upperLeftBlock ha gS :=
      extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3)) (le hS)
    have m2 : upperLeftBlock ha ((upperLeftBlock hab gT)⁻¹ * g) = upperLeftBlock ha (upperLeftBlock hab gT)⁻¹ * upperLeftBlock ha g :=
      extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.inv_mem _ tm)) (le h3)
    have m3 : upperLeftBlock ha (upperLeftBlock hab gT)⁻¹ = (upperLeftBlock ha (upperLeftBlock hab gT))⁻¹ := extendOne_inv _ (le tm)
    rw [m1, m2, m3, h4, restrictTopBlock_restrictTopBlock hab ha hb t2 hT, hST, mul_one, inv_mul_cancel]

theorem char_law (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {A : Type} [CommGroup A]
    (χ : ℕ → κˣ →* A) {g gS : GL (Fin a) κ} {gT : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t))
    (hS : gS ∈ blockTri (blkOf r t)) (hT : gT ∈ blockTri (blkOf r t)) :
    (χ (j + 1) (Matrix.GeneralLinearGroup.det gS) * (χ (j + 1) (Matrix.GeneralLinearGroup.det gT))⁻¹) *
      ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab gT)⁻¹ * g * gS))) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab gT)⁻¹ * g * gS)))⁻¹) =
    (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) gS)) *
      (∏ c ∈ Finset.range (j + 1), χ (c + 1) (dBlk (blkOf r t) (c + 1) gT))⁻¹ *
      ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det g))⁻¹) := by
  have tm := top_mem hab (mem_twoBlockTriangular_of_blockTriangular ea eb hT) hT
  have e1 : ∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab gT)⁻¹ * g * gS)) =
      (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) gT))⁻¹ *
      (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
      (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) gS)) := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c hc => ?_
    have hi : dBlk (blkOf r t) (c + 1) (upperLeftBlock hab gT)⁻¹ = (dBlk (blkOf r t) (c + 1) (upperLeftBlock hab gT))⁻¹ :=
      extendOne_inv _ tm
    rw [diag_block_det_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) hg) hS, diag_block_det_mul (Subgroup.inv_mem _ tm) hg, hi,
      diagonalBlock_restrictTopBlock hab ea eb hT (Finset.mem_range.1 hc), map_mul, map_mul, map_inv]
  rw [e1, Finset.prod_range_succ, det_top hab ea eb hT]
  simp only [map_mul, map_inv, mul_inv, inv_inv]
  generalize χ (j + 1) (Matrix.GeneralLinearGroup.det gS) = x1
  generalize χ (j + 1) (Matrix.GeneralLinearGroup.det (upperLeftBlock hab gT)) = x2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Mat

section Dat

variable {D : D7} {a b r t j : ℕ} (ha : r ≤ a) (Pg Q : Finset (Pl D.host.E))
  (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
  (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP))

theorem omegaG_of_isTop (g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1)) (hg : ∀ PP : ↥Pg, IsTop t ha (y PP.1) (g PP)) :
    omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) χj y =
      ((∏ PP : ↥Pg, ((∏ c ∈ Finset.range j, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
        (χj PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) : ℂˣ) : ℂ) := by
  unfold omegaG
  split_ifs with h
  · have e : ∀ PP, h.2.choose PP = g PP := fun PP =>
      Units.ext ((h.2.choose_spec.1 PP).trans (hg PP).2.1.symm)
    have e2 : ∀ x, (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B).P.chi x = 1 := fun _ => rfl
    rw [e2]
    simp only [e, Units.val_one, one_mul, Finset.prod_mul_distrib, Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val]
    rfl
  · exfalso
    refine h ⟨fun PP hP => (hg ⟨PP, hP⟩).1, g, fun PP => (hg PP).2.1, fun PP => (hg PP).2.2.1, ?_⟩
    exact Subgroup.mem_bot.2 (funext fun PP => (hg PP).2.2.2)

theorem omegaG_of_not (hg : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), ∀ PP : ↥Pg, IsTop t ha (y PP.1) (g PP)) :
    omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) χj y = 0 := by
  unfold omegaG
  split_ifs with h
  · exfalso
    obtain ⟨h1, g, g1, g2, g3⟩ := h
    exact hg ⟨g, fun PP => ⟨h1 PP.1 PP.2, g1 PP, g2 PP, congrFun (Subgroup.mem_bot.1 g3) PP⟩⟩
  · rfl

end Dat

theorem omegaG_law : ∀ (D : D7) (a b r t j : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + j * t → b = r + (j + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Pg, gS PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, gT PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, upperLeftBlock ha (gS PP) = upperLeftBlock hb (gT PP)) → (∀ PP ∈ Pg, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Pg, (((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ) * ((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ)⁻¹)) * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y' = ((∏ PP ∈ Pg, ∏ c ∈ Finset.range j, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gS PP)) : ℂˣ) : ℂ) * ((∏ PP ∈ Pg, ∏ c ∈ Finset.range (j + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gT PP)) : ℂˣ) : ℂ)⁻¹ * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y := by
  intro D a b r t j ha hb ea eb Pg Q χ ξ gS gT y y' hS hT hST hy
  have hab : a ≤ b := by rw [ea, eb, add_mul]; omega
  by_cases h : ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), ∀ PP : ↥Pg, IsTop t ha (y PP.1) (g PP)
  · obtain ⟨g, hg⟩ := h
    have hg' : ∀ PP : ↥Pg, IsTop t ha (y' PP.1) ((upperLeftBlock hab (gT PP.1))⁻¹ * g PP * gS PP.1) := fun PP => by
      rw [hy PP.1 PP.2]
      exact (hg PP).move hab ha hb ea eb (hS _ PP.2) (hT _ PP.2) (hST _ PP.2)
    rw [omegaG_of_isTop ha Pg Q χ ξ _ y g hg, omegaG_of_isTop ha Pg Q χ ξ _ y' _ hg']
    simp only [← Units.val_inv_eq_inv_val, ← Units.val_mul, ← Units.coe_prod]
    congr 1
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort Pg, ← Finset.prod_coe_sort Pg,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun PP _ =>
      char_law hab ea eb (fun c => χ c PP.1) (hg PP).2.2.1 (hS _ PP.2) (hT _ PP.2)
  · have h' : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), ∀ PP : ↥Pg, IsTop t ha (y' PP.1) (g PP) := by
      rintro ⟨g, hg⟩
      refine h ⟨fun PP => (upperLeftBlock hab (gT PP.1)⁻¹)⁻¹ * g PP * (gS PP.1)⁻¹, fun PP => ?_⟩
      have e : y PP.1 = ((gT PP.1)⁻¹⁻¹).val * y' PP.1 * ((gS PP.1)⁻¹).val := by
        rw [hy PP.1 PP.2, inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.one_mul]
      have i1 : upperLeftBlock ha (gS PP.1)⁻¹ = (upperLeftBlock ha (gS PP.1))⁻¹ := extendOne_inv _ (blockTri_blkOf_le r t (hS _ PP.2))
      have i2 : upperLeftBlock hb (gT PP.1)⁻¹ = (upperLeftBlock hb (gT PP.1))⁻¹ := extendOne_inv _ (blockTri_blkOf_le r t (hT _ PP.2))
      rw [e]
      exact (hg PP).move hab ha hb ea eb (Subgroup.inv_mem _ (hS _ PP.2)) (Subgroup.inv_mem _ (hT _ PP.2))
        (by rw [i1, i2, hST _ PP.2])
    rw [omegaG_of_not ha Pg Q χ ξ _ y h, omegaG_of_not ha Pg Q χ ξ _ y' h', mul_zero, mul_zero]

end GlobalTheory.StepLaw.TypeDatum

end
