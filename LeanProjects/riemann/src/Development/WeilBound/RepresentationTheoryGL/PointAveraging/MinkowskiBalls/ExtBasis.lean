import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt

open ValuativeRel Matrix GlobalTheory.SplitWeil PositivityTheory.Tls2.Ming3

noncomputable section

namespace PositivityTheory.Rg.Ming.NfX

def E (R : Type*) [Semiring R] (a b j : ℕ) : Matrix (Fin a) (Fin b) R :=
  Matrix.of fun i l => if (i : ℕ) = l ∧ (l : ℕ) < j then 1 else 0

theorem E_apply {R : Type*} [Semiring R] {a b j : ℕ} (i : Fin a) (l : Fin b) :
    E R a b j i l = if (i : ℕ) = l ∧ (l : ℕ) < j then 1 else 0 := rfl

theorem E_mul {R : Type*} [Semiring R] {a b c j : ℕ} (hb : j ≤ b) :
    E R a b j * E R b c j = E R a c j := by
  ext i l
  simp only [mul_apply, E_apply]
  by_cases h : (i : ℕ) = l ∧ (l : ℕ) < j
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := h
    have hi : (i : ℕ) < j := h1 ▸ h2
    rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin b)]
    · simp [hi, h1, h2]
    · intro m _ hm
      have hne : ¬ ((i : ℕ) = m ∧ (m : ℕ) < j) := fun e => hm (Fin.ext e.1.symm)
      rw [if_neg hne, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases h1 : (i : ℕ) = m ∧ (m : ℕ) < j
    · have h2 : ¬ ((m : ℕ) = l ∧ (l : ℕ) < j) := fun h2 => h ⟨h1.1.trans h2.1, h2.2⟩
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

theorem E_diag {R : Type*} [Semiring R] {a j : ℕ} :
    E R a a j = diagonal fun i : Fin a => if (i : ℕ) < j then 1 else 0 := by
  ext i l
  simp only [E_apply, diagonal_apply]
  by_cases h : i = l
  · subst h; simp
  · have : (i : ℕ) ≠ l := fun e => h (Fin.ext e)
    simp [h, this]

theorem rank_E {k : Type*} [Field k] {a j : ℕ} (hj : j ≤ a) : (E k a a j).rank = j := by
  classical
  rw [E_diag, rank_diagonal]
  refine (Fintype.card_congr ?_).trans (Fintype.card_fin j)
  exact
    { toFun := fun i => ⟨i.1, by
        have := i.2
        by_contra hlt
        simp [hlt] at this⟩
      invFun := fun l => ⟨Fin.castLE hj l, by simp [l.2]⟩
      left_inv := fun i => Subtype.ext (Fin.ext rfl)
      right_inv := fun l => Fin.ext rfl }

theorem what₂ {k : Type*} [Field k] {n r j : ℕ} (hj : j ≤ n) (y : Matrix (Fin n) (Fin r) k) (hy : y.rank ≤ j)
    (hc : LinearMap.range (E k n n j).mulVecLin ≤ LinearMap.range y.mulVecLin) : E k n n j * y = y := by
  classical
  have hE : (E k n n j).rank = j := rank_E hj
  have heq : LinearMap.range (E k n n j).mulVecLin = LinearMap.range y.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le hc
    exact (hy.trans hE.ge : y.rank ≤ (E k n n j).rank)
  have hEE : E k n n j * E k n n j = E k n n j := E_mul hj
  ext i l
  have hcol : y.mulVecLin (Pi.single l 1) ∈ LinearMap.range (E k n n j).mulVecLin := by
    rw [heq]
    exact LinearMap.mem_range_self _ _
  obtain ⟨v, hv⟩ := hcol
  have hv' : (E k n n j).mulVec v = y.mulVec (Pi.single l 1) := hv
  have key : (E k n n j * y).mulVec (Pi.single l 1) = y.mulVec (Pi.single l 1) := by
    rw [← Matrix.mulVec_mulVec, ← hv', Matrix.mulVec_mulVec, hEE]
  have := congrFun key i
  simpa [Matrix.mulVec_single_one] using this

theorem ext_basis {k : Type*} [Field k] {a j : ℕ} (hj : j ≤ a) (v : Fin j → (Fin a → k))
    (hv : LinearIndependent k v) : ∃ H : GL (Fin a) k, ∀ i (l : Fin j), H.val i (Fin.castLE hj l) = v l i := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range v))
  have hfin : Module.finrank k C = a - j := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 : Module.finrank k (Submodule.span k (Set.range v)) = j := by
      rw [finrank_span_eq_card hv, Fintype.card_fin]
    have h3 : Module.finrank k (Fin a → k) = a := Module.finrank_fin_fun k
    omega
  obtain ⟨bC, -⟩ : ∃ bC : Module.Basis (Fin (a - j)) k C, True :=
    ⟨Module.finBasisOfFinrankEq k C hfin, trivial⟩
  have hw : LinearIndependent k (C.subtype ∘ bC) :=
    bC.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
  have hdisj : Disjoint (Submodule.span k (Set.range v)) (Submodule.span k (Set.range (C.subtype ∘ bC))) := by
    have hle : Submodule.span k (Set.range (C.subtype ∘ bC)) ≤ C := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact (bC m).2
    exact hC.disjoint.mono_right hle
  have hvw := hv.sum_type hw hdisj
  obtain ⟨e, he⟩ : ∃ e : Fin a ≃ Fin j ⊕ Fin (a - j),
      e = (finCongr (by omega : a = j + (a - j))).trans finSumFinEquiv.symm := ⟨_, rfl⟩
  have hf := hvw.comp e e.injective
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin a) (Fin a) k, M = Matrix.of fun i m => (Sum.elim v (C.subtype ∘ bC) (e m)) i :=
    ⟨_, rfl⟩
  have hcolM : M.col = Sum.elim v (C.subtype ∘ bC) ∘ e := by
    ext m i
    simp [hM, Matrix.col]
  have hMu : IsUnit M := by
    rw [← linearIndependent_cols_iff_isUnit, hcolM]
    exact hf
  refine ⟨hMu.unit, fun i l => ?_⟩
  have hel : e (Fin.castLE hj l) = Sum.inl l := by
    rw [he, Equiv.trans_apply, Equiv.symm_apply_eq]
    apply Fin.ext
    simp
  show M i (Fin.castLE hj l) = v l i
  rw [hM, Matrix.of_apply, hel]
  rfl

private theorem E_mul_apply_eq_dite_lt {R : Type*} [Semiring R] {a b c j : ℕ} (hb : j ≤ b)
    (M : Matrix (Fin b) (Fin c) R) (i : Fin a) (m : Fin c) :
    (E R a b j * M) i m = if h : (i : ℕ) < j then M ⟨i, by omega⟩ m else 0 := by
  rw [mul_apply]
  simp only [E_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin b)]
    · simp [h]
    · intro t _ ht
      have hne : ¬ ((i : ℕ) = t ∧ (t : ℕ) < j) := fun e => ht (Fin.ext e.1.symm)
      rw [if_neg hne, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun t _ => ?_
    have hne : ¬ ((i : ℕ) = t ∧ (t : ℕ) < j) := fun e => h (by rw [e.1]; exact e.2)
    rw [if_neg hne, zero_mul]

set_option maxHeartbeats 1000000 in
theorem nf1 {k : Type*} [Field k] {n r j : ℕ} (x : Matrix (Fin n) (Fin r) k) (hx : x.rank = j) :
    ∃ (H : GL (Fin n) k) (G : GL (Fin r) k), x = H.val * E k n r j * G.val := by
  classical
  have hn : j ≤ n := hx ▸ (by simpa using x.rank_le_card_height)
  have hr : j ≤ r := hx ▸ (by simpa using x.rank_le_card_width)
  obtain ⟨bb, -⟩ : ∃ bb : Module.Basis (Fin j) k (LinearMap.range x.mulVecLin), True :=
    ⟨Module.finBasisOfFinrankEq k _ hx, trivial⟩
  obtain ⟨H, hH⟩ := ext_basis hn ((LinearMap.range x.mulVecLin).subtype ∘ bb)
    (bb.linearIndependent.map' _ (Submodule.ker_subtype _))
  have hcol : LinearMap.range (H.val * E k n n j).mulVecLin ≤ LinearMap.range x.mulVecLin := by
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    by_cases hm : (m : ℕ) < j
    · have hc : (H.val * E k n n j).col m = (bb ⟨m, hm⟩ : Fin n → k) := by
        ext i
        show (H.val * E k n n j) i m = _
        simp only [E_diag, mul_diagonal, hm, if_true, mul_one]
        exact hH i ⟨m, hm⟩
      rw [hc]
      exact (bb ⟨m, hm⟩).2
    · have hc : (H.val * E k n n j).col m = 0 := by
        ext i
        show (H.val * E k n n j) i m = 0
        simp [E_diag, mul_diagonal, hm]
      rw [hc]
      exact zero_mem _
  obtain ⟨y, hy⟩ : ∃ y, y = (H⁻¹).val * x := ⟨_, rfl⟩
  have hcr : LinearMap.range (E k n n j).mulVecLin ≤ LinearMap.range y.mulVecLin := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, hu⟩ := hcol (LinearMap.mem_range_self _ w)
    refine ⟨u, ?_⟩
    have hu' : x.mulVec u = (H.val * E k n n j).mulVec w := hu
    show y.mulVec u = (E k n n j).mulVec w
    rw [hy, ← Matrix.mulVec_mulVec, hu', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul,
      Matrix.one_mul]
  have hyr : y.rank = j := by
    rw [hy, rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 (H⁻¹).isUnit), hx]
  have hrows : E k n n j * y = y := what₂ hn y hyr.le hcr
  have hzero : ∀ i : Fin n, ¬ (i : ℕ) < j → y i = 0 := by
    intro i hi
    ext m
    rw [← hrows, E_mul_apply_eq_dite_lt hn, dif_neg hi]
    rfl
  obtain ⟨z, hzd⟩ : ∃ z : Fin j → (Fin r → k), z = fun l => y (Fin.castLE hn l) := ⟨_, rfl⟩
  have hz : LinearIndependent k z := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    apply le_antisymm
    · have h1 : Submodule.span k (Set.range y) ≤ Submodule.span k (Set.range z) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        by_cases hi : (i : ℕ) < j
        · exact Submodule.subset_span ⟨⟨i, hi⟩, by rw [hzd]; rfl⟩
        · rw [hzero i hi]
          exact zero_mem _
      have h2 := Submodule.finrank_mono h1
      have h3 : y.rank = Module.finrank k (Submodule.span k (Set.range y)) := rank_eq_finrank_span_row y
      rw [← h3, hyr] at h2
      exact h2
    · simpa using finrank_range_le_card (R := k) (b := z)
  obtain ⟨G', hG'⟩ := ext_basis hr z hz
  have hT : IsUnit (G'.val)ᵀ := by
    rw [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det]
    exact G'.isUnit
  refine ⟨H, hT.unit, ?_⟩
  have hEG : E k n r j * hT.unit.val = y := by
    ext i m
    rw [E_mul_apply_eq_dite_lt hr]
    split_ifs with hi
    · have := hG' m ⟨i, hi⟩
      rw [hzd] at this
      exact this
    · rw [hzero i hi]
      rfl
  rw [Matrix.mul_assoc, hEG, hy, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Bd {a b : ℕ} (γ : ValueGroupWithZero k) (M : Matrix (Fin a) (Fin b) k) : Prop :=
  ∀ i l, valuation k (M i l) ≤ γ

theorem bd_mul {a b d : ℕ} {γ δ : ValueGroupWithZero k} {P : Matrix (Fin a) (Fin b) k}
    {Q : Matrix (Fin b) (Fin d) k} (hP : Bd γ P) (hQ : Bd δ Q) : Bd (γ * δ) (P * Q) := fun i m => by
  rw [mul_apply]
  exact Valuation.map_sum_le _ fun l _ => by rw [map_mul]; exact mul_le_mul' (hP i l) (hQ l m)

theorem bd_sub {a b : ℕ} {γ : ValueGroupWithZero k} {P Q : Matrix (Fin a) (Fin b) k}
    (hP : Bd γ P) (hQ : Bd γ Q) : Bd γ (P - Q) := by
  intro i l
  rw [Matrix.sub_apply]
  exact (Valuation.map_sub _ _ _).trans (max_le (hP i l) (hQ i l))

theorem bd_E {a b j : ℕ} : Bd (1 : ValueGroupWithZero k) (E k a b j) := fun i l => by
  rw [E_apply]; split_ifs <;> simp

theorem bd_one {a : ℕ} : Bd (1 : ValueGroupWithZero k) (1 : Matrix (Fin a) (Fin a) k) := by
  intro i l
  rw [one_apply]
  split_ifs <;> simp

theorem bd_KO {a : ℕ} {H : GL (Fin a) k} (hH : H ∈ KO k (Fin a)) : Bd (1 : ValueGroupWithZero k) H.val := by
  obtain ⟨u, rfl⟩ := hH
  intro i l
  show valuation k (algebraMap 𝒪[k] k (u.val i l)) ≤ 1
  exact (u.val i l).2

theorem mem_KO {a : ℕ} {γ : ValueGroupWithZero k} (hc : γ < 1) (A : Matrix (Fin a) (Fin a) k)
    (hA : Bd γ (A - 1)) : ∃ H ∈ KO k (Fin a), H.val = A := by
  classical
  have hint : ∀ i l, valuation k (A i l) ≤ 1 := by
    intro i l
    have h1 : A i l = (A - 1) i l + (1 : Matrix (Fin a) (Fin a) k) i l := by simp
    rw [h1]
    refine (Valuation.map_add _ _ _).trans (max_le ((hA i l).trans hc.le) ?_)
    rw [one_apply]
    split_ifs <;> simp
  have hI : (valuation k).Integers 𝒪[k] := Valuation.integer.integers (valuation k)
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin a) (Fin a) 𝒪[k], B = Matrix.of fun i l => ⟨A i l, hint i l⟩ :=
    ⟨_, rfl⟩
  have hsmall : ∀ x : 𝒪[k], valuation k (x : k) < 1 → x ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
    exact hx.ne
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix B = 1 := by
    ext i l
    have hm : B i l - (1 : Matrix (Fin a) (Fin a) 𝒪[k]) i l ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      apply hsmall
      have e : ((B i l - (1 : Matrix (Fin a) (Fin a) 𝒪[k]) i l : 𝒪[k]) : k) = (A - 1) i l := by
        rw [Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply, hB]
        split_ifs <;> simp
      rw [e]
      exact lt_of_le_of_lt (hA i l) hc
    have h0 := (IsLocalRing.residue_eq_zero_iff _).2 hm
    rw [map_sub, sub_eq_zero] at h0
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h0, one_apply, one_apply]
    split_ifs <;> simp
  have hdet : IsUnit B.det := by
    by_contra hnu
    have hm : B.det ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have h0 := (IsLocalRing.residue_eq_zero_iff _).2 hm
    rw [RingHom.map_det, hres, det_one] at h0
    exact one_ne_zero h0
  have hBu : IsUnit B := (isUnit_iff_isUnit_det B).2 hdet
  refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[k] k) hBu.unit, ⟨hBu.unit, rfl⟩, ?_⟩
  subst hB
  rfl

theorem nf2 {n r j : ℕ} (x : Matrix (Fin n) (Fin r) k) (hx : x.rank = j) (c : kˣ)
    (hc : valuation k (c : k) < 1) (hb : ∀ i l, valuation k (x i l - E k n r j i l) ≤ valuation k (c : k)) :
    ∃ h ∈ KO k (Fin n), ∃ g ∈ KO k (Fin r), x = h.val * E k n r j * g.val := by
  have hn : j ≤ n := hx ▸ (by simpa using x.rank_le_card_height)
  have hr : j ≤ r := hx ▸ (by simpa using x.rank_le_card_width)
  have Enr_rn : E k n r j * E k r n j = E k n n j := E_mul hr
  have Ern_nr : E k r n j * E k n r j = E k r r j := E_mul hn
  have Enn_nr : E k n n j * E k n r j = E k n r j := E_mul hn
  have Enr_rr : E k n r j * E k r r j = E k n r j := E_mul hr
  have Err_rn : E k r r j * E k r n j = E k r n j := E_mul hr
  have hE1 : ∀ {a b : ℕ}, Bd (1 : ValueGroupWithZero k) (E k a b j) := fun {a b} => bd_E
  have hx' : Bd (valuation k (c : k)) (x - E k n r j) := fun i l => by
    rw [Matrix.sub_apply]
    exact hb i l
  have hh1 : x * E k r n j + (1 - E k n n j) - 1 = (x - E k n r j) * E k r n j := by
    rw [Matrix.sub_mul, Enr_rn]
    abel
  obtain ⟨H, hHK, hH⟩ := mem_KO hc (x * E k r n j + (1 - E k n n j)) (by
    rw [hh1]
    simpa using bd_mul hx' hE1)
  have hxE : x * E k r r j = H.val * E k n r j := by
    rw [hH, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Ern_nr, Enn_nr,
      sub_self, add_zero]
  obtain ⟨y, hy⟩ : ∃ y, y = (H⁻¹).val * x := ⟨_, rfl⟩
  have hyE : y * E k r r j = E k n r j := by
    rw [hy, Matrix.mul_assoc, hxE, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hyEn : y * E k r n j = E k n n j := by
    rw [← Err_rn, ← Matrix.mul_assoc, hyE, Enr_rn]
  have hcr : LinearMap.range (E k n n j).mulVecLin ≤ LinearMap.range y.mulVecLin := by
    rw [← hyEn, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hyr : y.rank ≤ j := by
    rw [hy]
    exact (rank_mul_le_right _ _).trans hx.le
  have hrows : E k n n j * y = y := what₂ hn y hyr hcr
  have hsplit : (x - E k n r j) * (1 - E k r r j) = x - x * E k r r j := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_one, Enr_rr]
    abel
  have hyd : y - E k n r j = (H⁻¹).val * ((x - E k n r j) * (1 - E k r r j)) := by
    rw [hsplit, Matrix.mul_sub, ← Matrix.mul_assoc, ← hy, hyE]
  have hinv : H⁻¹ ∈ KO k (Fin n) := (KO k (Fin n)).inv_mem hHK
  have hyb : Bd (valuation k (c : k)) (y - E k n r j) := by
    rw [hyd]
    simpa using bd_mul (bd_KO hinv) (bd_mul hx' (bd_sub bd_one hE1))
  have hg1 : E k r n j * y + (1 - E k r r j) - 1 = E k r n j * (y - E k n r j) := by
    rw [Matrix.mul_sub, Ern_nr]
    abel
  obtain ⟨G, hGK, hG⟩ := mem_KO hc (E k r n j * y + (1 - E k r r j)) (by
    rw [hg1]
    simpa using bd_mul hE1 hyb)
  refine ⟨H, hHK, G, hGK, ?_⟩
  calc x = H.val * y := by rw [hy, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    _ = H.val * (E k n r j * G.val) := by
      rw [hG, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Enr_rn, hrows,
        Enr_rr, sub_self, add_zero]
    _ = H.val * E k n r j * G.val := (Matrix.mul_assoc _ _ _).symm

end PositivityTheory.Rg.Ming.NfX

namespace PositivityTheory.Rg.Ming

theorem nf : NfSt := by
  intro k _ _ _ _ n r j x hx
  exact ⟨NfX.nf1 x hx, fun c hc hb => NfX.nf2 x hx c hc hb⟩

end PositivityTheory.Rg.Ming

end
