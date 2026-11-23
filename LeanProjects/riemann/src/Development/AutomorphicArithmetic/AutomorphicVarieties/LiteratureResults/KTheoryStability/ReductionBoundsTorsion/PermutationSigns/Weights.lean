import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PStab

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped Kronecker

namespace PositivityTheory.KB.BlockInvariants

namespace AlternatingWeights

variable {L : Type} [Field L] [NumberField L]

theorem tmC_pos {N q : ℕ} {σ : Equiv.Perm (Fin q)} {w : Fin q → InfinitePlace L}
    (hw : ∀ i, w (σ i) = w i) (Y : Fin q → HS L N) :
    tmC σ w Y = ∑ a : Fin q → Fin N, ∏ i, mat (Y i) (w i) (a i) (a (σ i)) := by
  rw [tmC, if_pos hw]
  simp [ent]
  rfl

theorem tmC_neg {N q : ℕ} {σ : Equiv.Perm (Fin q)} {w : Fin q → InfinitePlace L}
    (hw : ¬ ∀ i, w (σ i) = w i) (Y : Fin q → HS L N) : tmC σ w Y = 0 := by
  rw [tmC, if_neg hw]; rfl

theorem alt_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (v : Fin q → E) :
    ContinuousMultilinearMap.alternatization f v = ∑ π : Equiv.Perm (Fin q), Equiv.Perm.sign π • f (v ∘ π) := by
  simp [ContinuousMultilinearMap.alternatization_apply_apply]

theorem alt_comp {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {q : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => F) ℝ) (P : E →L[ℝ] F) :
    (ContinuousMultilinearMap.alternatization f).compContinuousLinearMap P =
      ContinuousMultilinearMap.alternatization (f.compContinuousLinearMap fun _ => P) := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, alt_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

theorem alt_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (c : ℝ) :
    ContinuousMultilinearMap.alternatization (c • f) = c • ContinuousMultilinearMap.alternatization f := by
  ext v
  simp only [alt_apply, ContinuousAlternatingMap.smul_apply, _root_.smul_apply,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [smul_comm]

theorem alt_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (σ : Equiv.Perm (Fin q))
    (hf : ∀ v, f (v ∘ σ) = f v) (hs : Equiv.Perm.sign σ = -1) :
    ContinuousMultilinearMap.alternatization f = 0 := by
  ext v
  have h1 : ContinuousMultilinearMap.alternatization f v =
      Equiv.Perm.sign σ • ContinuousMultilinearMap.alternatization f v := by
    conv_lhs => rw [alt_apply, ← Equiv.sum_comp (Equiv.mulRight σ)]
    conv_rhs => rw [alt_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    have : v ∘ ⇑(π * σ) = (v ∘ π) ∘ σ := by
      ext i; simp [Equiv.Perm.coe_mul]
    simp only [Equiv.coe_mulRight]
    rw [this, hf, Equiv.Perm.sign_mul, mul_comm, mul_smul]
  rw [hs] at h1
  have h2 : ContinuousMultilinearMap.alternatization f v = -ContinuousMultilinearMap.alternatization f v := by
    rw [Units.neg_smul, one_smul] at h1
    exact h1
  have h3 : ContinuousMultilinearMap.alternatization f v = 0 := by linarith
  simpa using h3

theorem cyc_move {N q : ℕ} (σ : Equiv.Perm (Fin q)) (X Z : Fin q → Matrix (Fin N) (Fin N) ℂ) :
    ∑ a : Fin q → Fin N, ∏ i, (X i * Z i) (a i) (a (σ i)) =
      ∑ a : Fin q → Fin N, ∏ i, (Z (σ⁻¹ i) * X i) (a i) (a (σ i)) := by
  simp only [Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.prod_mul_distrib]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin N)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id]
  rw [mul_comm]
  congr 1
  exact Fintype.prod_equiv σ _ _ (fun j => by simp)

theorem mat_padL (n M : ℕ) (h : HS L n) (w : InfinitePlace L) : mat (padL n M h) w = padM (mat h w) := rfl

theorem mat_blkL (d n : ℕ) (h : HS L n) (w : InfinitePlace L) :
    mat (blkL d n h) w = Matrix.reindex finProdFinEquiv finProdFinEquiv
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ mat h w) := rfl

theorem tmC_pad {n M q : ℕ} (hnm : n ≤ M) (σ : Equiv.Perm (Fin q)) (w : Fin q → InfinitePlace L)
    (Y : Fin q → HS L n) : tmC (N := M) σ w (fun i => padL n M (Y i)) = tmC σ w Y := by
  by_cases hw : ∀ i, w (σ i) = w i
  · rw [tmC_pos hw, tmC_pos hw]
    simp only [mat_padL]
    refine (Fintype.sum_of_injective (fun b : Fin q → Fin n => fun i => Fin.castLE hnm (b i)) ?_ _ _ ?_ ?_).symm
    · intro b b' hb
      funext i
      have := congrFun hb i
      exact Fin.castLE_injective hnm this
    · intro a ha
      have : ∃ i, ¬ ((a i : ℕ) < n) := by
        by_contra hc
        push Not at hc
        exact ha ⟨fun i => ⟨a i, hc i⟩, funext fun i => Fin.ext rfl⟩
      obtain ⟨i, hi⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [padM, hi])
    · intro b
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [padM]
  · rw [tmC_neg hw, tmC_neg hw]

theorem card_inv (d q : ℕ) (σ : Equiv.Perm (Fin q)) :
    Fintype.card {β : Fin q → Fin d // ∀ i, β i = β (σ i)} = d ^ ncyc σ := by
  classical
  have key : ∀ β : Fin q → Fin d, (∀ i, β i = β (σ i)) → ∀ x y, σ.SameCycle x y → β x = β y := by
    intro β hβ x y hxy
    obtain ⟨k, -, rfl⟩ := hxy.exists_pow_eq'
    clear hxy
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ← hβ]; exact ih
  let s := Equiv.Perm.SameCycle.setoid σ
  let e : {β : Fin q → Fin d // ∀ i, β i = β (σ i)} ≃ (Quotient s → Fin d) :=
    { toFun := fun β => Quotient.lift β.1 (fun x y hxy => key β.1 β.2 x y hxy)
      invFun := fun f => ⟨fun i => f (Quotient.mk s i), fun i => congrArg f (Quotient.sound
        (show σ.SameCycle i (σ i) from Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl σ i)))⟩
      left_inv := fun β => rfl
      right_inv := fun f => funext fun x => Quotient.inductionOn x fun i => rfl }
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin]
  rfl

theorem tmC_blk {d n q : ℕ} (σ : Equiv.Perm (Fin q)) (w : Fin q → InfinitePlace L) (Y : Fin q → HS L n) :
    tmC (N := d * n) σ w (fun i => blkL d n (Y i)) = ((d ^ ncyc σ : ℕ) : ℂ) * tmC σ w Y := by
  classical
  by_cases hw : ∀ i, w (σ i) = w i
  · rw [tmC_pos hw, tmC_pos hw, ← card_inv d q σ]
    simp only [mat_blkL]
    set A : Fin q → Matrix (Fin n) (Fin n) ℂ := fun i => mat (Y i) (w i)
    let E : (Fin q → Fin d) × (Fin q → Fin n) ≃ (Fin q → Fin (d * n)) :=
      (Equiv.arrowProdEquivProdArrow (Fin q) (fun _ => Fin d) (fun _ => Fin n)).symm.trans
        (Equiv.arrowCongr (Equiv.refl _) finProdFinEquiv)
    have hE : ∀ p, E p = fun i => finProdFinEquiv (p.1 i, p.2 i) := fun p => rfl
    rw [← Fintype.sum_equiv E (fun p => ∏ i, (Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A i)) (E p i) (E p (σ i))) _ (fun p => rfl)]
    have hA : ∀ p : (Fin q → Fin d) × (Fin q → Fin n),
        ∏ i, (Matrix.reindex finProdFinEquiv finProdFinEquiv
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A i)) (E p i) (E p (σ i)) =
        (∏ i, if p.1 i = p.1 (σ i) then (1 : ℂ) else 0) * ∏ i, A i (p.2 i) (p.2 (σ i)) := by
      intro p
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [hE, reindex_apply, kroneckerMap_apply, one_apply]
    simp only [hA]
    rw [Fintype.sum_prod_type]
    dsimp only
    calc _ = (∑ x : Fin q → Fin d, ∏ i, if x i = x (σ i) then (1 : ℂ) else 0) *
          ∑ y : Fin q → Fin n, ∏ i, A i (y i) (y (σ i)) := (Finset.sum_mul_sum _ _ _ _).symm
      _ = _ := by
        congr 1
        rw [Fintype.card_subtype]
        simp [Finset.prod_boole, Finset.sum_boole]
  · rw [tmC_neg hw, tmC_neg hw, mul_zero]

theorem mat_one (N : ℕ) (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

theorem tmC_conj {N q : ℕ} (σ : Equiv.Perm (Fin q)) (w : Fin q → InfinitePlace L) (u : Gp L N)
    (hu : actL u (one L N).1 = (one L N).1) (Y : Fin q → HS L N) :
    tmC σ w (fun i => actL u (Y i)) = tmC σ w Y := by
  by_cases hw : ∀ i, w (σ i) = w i
  · rw [tmC_pos hw, tmC_pos hw]
    simp only [mat_actL]
    set V : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ := fun v => (((u v)⁻¹ : GL (Fin N) ℂ) : Matrix _ _ ℂ)
    have hV : ∀ v, V v * (V v)ᴴ = 1 := by
      intro v
      have h2 := congrArg (fun h => mat h v) hu
      rw [mat_actL, mat_one, Matrix.mul_one] at h2
      exact mul_eq_one_comm.1 h2
    have := cyc_move σ (fun i => (V (w i))ᴴ * mat (Y i) (w i)) (fun i => V (w i))
    rw [this]
    refine Finset.sum_congr rfl fun a _ => Finset.prod_congr rfl fun i _ => ?_
    have hwi : w (σ⁻¹ i) = w i := by
      exact (by simpa using hw (σ⁻¹ i) : w i = w (σ⁻¹ i)).symm
    rw [hwi, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  · rw [tmC_neg hw, tmC_neg hw]

theorem tmC_perm {N q : ℕ} (σ : Equiv.Perm (Fin q)) (w : Fin q → InfinitePlace L) (Y : Fin q → HS L N) :
    tmC σ w (Y ∘ σ) = tmC σ w Y := by
  by_cases hw : ∀ i, w (σ i) = w i
  · rw [tmC_pos hw, tmC_pos hw]
    have h1 : ∀ a : Fin q → Fin N, ∏ i, mat ((Y ∘ σ) i) (w i) (a i) (a (σ i)) =
        ∏ j, mat (Y j) (w j) (a (σ⁻¹ j)) (a j) := by
      intro a
      rw [← Equiv.prod_comp σ (fun j => mat (Y j) (w j) (a (σ⁻¹ j)) (a j))]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [hw i]
    simp only [h1]
    rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin N)))]
    refine Finset.sum_congr rfl fun b _ => Finset.prod_congr rfl fun j _ => ?_
    simp
  · rw [tmC_neg hw, tmC_neg hw]

theorem sign_of_ncyc {q : ℕ} (σ : Equiv.Perm (Fin q)) (hq : Even q) (h : ncyc σ = 1) :
    Equiv.Perm.sign σ = -1 := by
  classical
  have hsub : ∀ x y : Fin q, σ.SameCycle x y := by
    have : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) = 1 := h
    obtain ⟨u⟩ := Nat.card_eq_one_iff_unique.1 this
    intro x y
    exact Quotient.exact (Subsingleton.elim (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x) (Quotient.mk _ y))
  have hq0 : q ≠ 0 := by
    rintro rfl
    have : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) = 0 := by
      rw [Nat.card_eq_zero]; left
      exact ⟨fun x => Quotient.inductionOn x fun i => i.elim0⟩
    rw [ncyc] at h; omega
  have hq2 : 2 ≤ q := by
    obtain ⟨r, hr⟩ := hq; omega
  have hfix : ∀ x, σ x ≠ x := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y : Fin q, y ≠ x := by
      by_cases h0 : (x : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
      · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
    obtain ⟨k, -, hk⟩ := (hsub x y).exists_pow_eq'
    rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hx] at hk
    exact hy hk.symm
  have hcyc : σ.IsCycle := ⟨⟨0, by omega⟩, hfix _, fun y _ => hsub _ y⟩
  have hsupp : σ.support = Finset.univ := by
    ext x; simp [hfix x]
  rw [hcyc.sign, hsupp, Finset.card_univ, Fintype.card_fin, hq.neg_one_pow]

theorem tmR_comp_pad {L : Type} [Field L] [NumberField L] {n M q : ℕ} (hnm : n ≤ M) (x : Pat L q) :
    (tmR (N := M) x.1 x.2.1 x.2.2).compContinuousLinearMap (fun _ => padL n M) = tmR (N := n) x.1 x.2.1 x.2.2 := by
  ext Y
  cases h : x.2.2 <;> simp [tmR, tmC_pad hnm]

theorem natpow_re (d k : ℕ) : ((d : ℂ) ^ k).re = (d : ℝ) ^ k := by
  rw [← Nat.cast_pow, Complex.natCast_re, Nat.cast_pow]

theorem natpow_im (d k : ℕ) : ((d : ℂ) ^ k).im = 0 := by
  rw [← Nat.cast_pow, Complex.natCast_im]

end AlternatingWeights

open AlternatingWeights

theorem wPad : WPad := by
  intro L _ _ n M q hnm x
  rw [AT, AT, alt_comp, tmR_comp_pad hnm]

theorem weylTwoBlockMatrix : WBlk := by
  intro L _ _ d n q x
  rw [AT, AT, alt_comp, ← alt_smul]
  congr 1
  ext Y
  cases h : x.2.2 <;> simp [tmR, tmC_blk, natpow_re, natpow_im]

theorem wInv : WInv := by
  intro L _ _ N q x u hu
  rw [AT, alt_comp]
  congr 1
  ext Y
  cases h : x.2.2 <;> simp [tmR, tmC_conj _ _ u hu]

theorem wOne : WOne := by
  intro L _ _ N q x hq h1
  rw [AT]
  refine alt_zero _ x.1 (fun v => ?_) (sign_of_ncyc x.1 hq h1)
  cases h : x.2.2 <;> simp [tmR, tmC_perm]

theorem wCyc : WCyc := by
  intro q σ hq
  constructor
  · have : Nonempty (Quotient (Equiv.Perm.SameCycle.setoid σ)) := ⟨Quotient.mk _ ⟨0, hq⟩⟩
    exact Nat.card_pos
  · have := Nat.card_le_card_of_surjective (Quotient.mk (Equiv.Perm.SameCycle.setoid σ))
      Quotient.mk_surjective
    simpa [ncyc] using this

end PositivityTheory.KB.BlockInvariants

end
