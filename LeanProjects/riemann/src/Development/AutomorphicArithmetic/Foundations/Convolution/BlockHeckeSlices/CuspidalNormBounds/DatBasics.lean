import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapPoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup
open UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

private theorem posIdele_inf (s : ℝ) (hs : 0 < s) (w : InfinitePlace E) :
    ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ) := by
  have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  change GroundTheory.Global.posRealElem w _ = _
  unfold GroundTheory.Global.posRealElem
  rw [dif_neg hw]
  simp [InfinitePlace.mult, hw, Real.sqrt_sq hs.le]

private noncomputable def eU (E : Type) [Field E] (x : ℝ) : (Cinf E)ˣ where
  val := fun _ => (Real.exp x : ℂ)
  inv := fun _ => (Real.exp (-x) : ℂ)
  val_inv := funext fun _ => by simp [← Complex.exp_add]
  inv_val := funext fun _ => by simp [← Complex.exp_add]

private theorem diag_eq (a : Fin n → ℝ) :
    (diagUnits n fun i => posIdele (K := E) (Real.exp (a i)) (Real.exp_pos _) : GA E n) =
      infGL E n (diagUnits n fun i => eU E (a i)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  set y : GL (Fin n) (Cinf E) := diagUnits n fun i => eU E (a i) with hy
  have h2 : ((infGL E n y).val i j).2 = (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j :=
    congrArg (fun g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) => g.val i j) (pFin_infGL y)
  have h1 : ∀ w, ((infGL E n y).val i j).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val i j w) :=
    fun w => congrFun (infGL_entry y i j) w
  have hyv : y.val = Matrix.diagonal fun i => (fun _ : InfinitePlace E => (Real.exp (a i) : ℂ)) := rfl
  rw [coe_diagUnits]
  refine Prod.ext (funext fun w => ?_) ?_
  · rw [h1, hyv]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdele_inf]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
      exact (map_zero _).symm
  · rw [h2]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact FiniteAdeleRing.ext E fun v => posIdele_finite _ _ v
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rfl

private theorem sum_Eop (i : Fin n) : ∑ τ : E →+* ℂ, Eop τ i i = lie E n (toL (Matrix.single i i 1)) := by
  rw [lie_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ∀ k l, coord τ (toL (Matrix.single i i (1 : Cinf E)) k l) = if i = k then if i = l then 1 else 0 else 0 := by
    intro k l
    change coord τ (Matrix.single i i (1 : Cinf E) k l) = _
    rw [Matrix.single_apply]
    by_cases h1 : i = k <;> by_cases h2 : i = l <;> simp [h1, h2]
  simp only [e]
  simp

private theorem lie_one : lie E n (oneL E n) = ∑ τ : E →+* ℂ, ∑ i, Eop τ i i := by
  rw [lie_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ l, coord τ (oneL E n k l) = if k = l then 1 else 0 := by
    intro l
    change coord τ ((1 : Matrix (Fin n) (Fin n) (Cinf E)) k l) = _
    rw [Matrix.one_apply]
    split_ifs <;> simp
  simp only [e]
  simp

private theorem lie_one_eq_zero (hn : 0 < n) (f : Sm E n) (h : ∀ t g, f.1 (zt E n t * g) = f.1 g) :
    lie E n (oneL E n) f = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have hd : HasDerivAt (fun t : ℝ => toL (diagUnits n fun _ => eU E t : GL (Fin n) (Cinf E)).val) (oneL E n) 0 := by
    have e : (fun t : ℝ => toL (diagUnits n fun _ => eU E t : GL (Fin n) (Cinf E)).val) =
        fun t : ℝ => Real.exp t • oneL E n := by
      funext t k l w
      change (Matrix.diagonal fun _ => (fun _ : InfinitePlace E => (Real.exp t : ℂ))) k l w =
        Real.exp t • (1 : Matrix (Fin n) (Fin n) (Cinf E)) k l w
      by_cases h : k = l
      · subst h; simp
      · simp [h]
    rw [e]
    simpa using (Real.hasDerivAt_exp 0).smul_const (oneL E n)
  have h0 : (diagUnits n fun _ => eU E 0 : GL (Fin n) (Cinf E)) = 1 := by
    rw [← map_one (diagUnits n)]
    congr 1
    funext i
    exact Units.ext (funext fun _ => by simp [eU])
  have h1 := hasDerivAt_curve f g (fun t => diagUnits n fun _ => eU E t) _ h0 hd
  have e : (fun t : ℝ => f.1 (g * infGL E n (diagUnits n fun _ => eU E t))) = fun _ => f.1 g := by
    funext t
    have ha : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    have e : rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹ ⟨Real.exp (n * Module.finrank ℚ E * t), Real.exp_pos _⟩ =
        ⟨Real.exp t, Real.exp_pos t⟩ := by
      refine Subtype.ext ?_
      change Real.exp (n * Module.finrank ℚ E * t) ^ ((n * Module.finrank ℚ E : ℝ))⁻¹ = Real.exp t
      rw [← Real.exp_mul]
      congr 1
      field_simp
    rw [← h (n * Module.finrank ℚ E * t) g, ← diag_eq, zt, centralSection_mul_comm, centralSection, MonoidHom.comp_apply,
      MonoidHom.comp_apply, e]
    rfl
  rw [e] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem trace_eq {f : Sm E n} {τ : E →+* ℂ} {Λ : Fin n → ℂ} (hn : 0 < n)
    (h : ∀ u, cap τ u f = (∏ i, (u + Λ i)) • f) : (∑ i, Eop τ i i) f = (∑ i, Λ i) • f := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨p, -, -, h3, h4⟩ := exists_capPoly (Eop (a := m + 1) τ) (ℓ ∘ₗ LinearMap.applyₗ f)
  have e : p = Polynomial.C (ℓ f) * ∏ i, (Polynomial.X - Polynomial.C (-Λ i)) := by
    refine Polynomial.funext fun u => ?_
    rw [h4]
    change ℓ (cap τ u f) = _
    rw [h, map_smul]
    simp [Polynomial.eval_prod, mul_comm]
  have h5 := h3 m rfl
  have h6 := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (m + 1))) (fun i => -Λ i) (by simp)
  rw [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h6
  rw [e, Polynomial.coeff_C_mul, h6] at h5
  rw [map_sub, map_smul, sub_eq_zero]
  refine h5.symm.trans ?_
  simp [mul_comm]

private theorem blo_sum {S : Set (Pl E)} (b : Blo S n) : ∑ τ, ∑ i, b.Λ τ i = 0 := by
  have h := lie_one_eq_zero b.pos b.f b.cen
  rw [lie_one, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => trace_eq b.pos (b.inf τ), ← Finset.sum_smul] at h
  exact (smul_eq_zero.1 h).resolve_right b.ne

private theorem J_eq {S : Set (Pl E)} (d : Dat S n) (j : Fin d.len) : ∃ c : ℂ,
    d.J j = c • ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, lie E n (toL (Matrix.single i i 1)) :=
  ⟨_, by rw [Dat.J, Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop i]⟩

private theorem comm_lie (i l : Fin n) :
    Commute (lie E n (toL (Matrix.single i i 1))) (lie E n (toL (Matrix.single l l 1))) := by
  have h := isLieHom_ιC (E := E) (a := n) (Matrix.single i i 1) (Matrix.single l l 1)
  have e : Matrix.single i i (1 : Cinf E) * Matrix.single l l 1 - Matrix.single l l 1 * Matrix.single i i 1 = 0 := by
    by_cases h : i = l
    · subst h; simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h), sub_zero]
  rw [e] at h
  have h2 := congrArg (uC E n) h
  simp only [map_sub, map_mul, uC_ιC] at h2
  have z : lie E n (toL 0) = 0 := map_zero (lie E n)
  rw [z] at h2
  first | exact sub_eq_zero.1 h2 | exact sub_eq_zero.1 h2.symm

private theorem comm_rt (i : Fin n) (a : Fin n → (Cinf E)ˣ) :
    Commute (lie E n (toL (Matrix.single i i 1))) (rt E n (infGL E n (diagUnits n a))) := by
  have h := GlobalTheory.CapAdInv.rt_lie (E := E) (diagUnits n a) (Matrix.single i i 1)
  have e : (diagUnits n a).val * Matrix.single i i (1 : Cinf E) * ((diagUnits n a)⁻¹).val = Matrix.single i i 1 := by
    rw [Units.mul_inv_eq_iff_eq_mul, coe_diagUnits]
    ext k l
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp
  rw [e] at h
  exact h.symm

private theorem comb {S : Set (Pl E)} (d : Dat S n) : Function.Surjective d.idx ∧ d.len ≤ n ∧
    (∀ j, ∑ τ, ∑ i, (if d.idx i = j then d.lam τ i else 0) = 0) ∧
    ∀ j w, w ∉ S → (d.sat j w).card = ∑ i, if d.idx i = j then 1 else 0 := by
  induction d with
  | nil => exact ⟨fun j => j.elim0, le_rfl, fun j => j.elim0, fun j => j.elim0⟩
  | @cons r s b d ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    let I : Fin (r + s) → Fin (d.len + 1) := Fin.addCases (fun _ => 0) fun i => (d.idx i).succ
    refine ⟨?_, ?_, ?_, ?_⟩
    · change ∀ j : Fin (d.len + 1), ∃ i, I i = j
      refine Fin.cases ⟨Fin.castAdd s ⟨0, b.pos⟩, Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _⟩ fun j => ?_
      obtain ⟨i, rfl⟩ := h1 j
      exact ⟨Fin.natAdd r i, by simp [I]⟩
    · have := b.pos
      change d.len + 1 ≤ _
      omega
    · change ∀ j : Fin (d.len + 1), ∑ τ, ∑ i, (if I i = j then
        Fin.addCases (motive := fun _ => ℂ) (b.Λ τ) (d.lam τ) i else 0) = 0
      simp only [Fin.sum_univ_add, I, Fin.addCases_left, Fin.addCases_right]
      refine Fin.cases ?_ fun j => ?_
      · simpa [Fin.succ_ne_zero] using blo_sum b
      · simpa [(Fin.succ_ne_zero _).symm] using h3 j
    · change ∀ (j : Fin (d.len + 1)) w, w ∉ S →
        (Fin.cases (motive := fun _ => Pl E → Multiset ℂˣ) b.sat d.sat j w).card = ∑ i, if I i = j then 1 else 0
      simp only [Fin.sum_univ_add, I, Fin.addCases_left, Fin.addCases_right]
      refine Fin.cases (fun w hw => ?_) fun j w hw => ?_
      · simpa [Fin.succ_ne_zero] using (b.isSat w hw).2.2.1
      · simpa [(Fin.succ_ne_zero _).symm] using h4 j w hw

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.datBasics :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.DatBasics E := by
  intro E _ _ _
  refine ⟨fun S r b => blo_sum b, fun S n d => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := comb d
  have hp : ∀ x : ℝ, posIdele (K := E) (Real.exp x) (Real.exp_pos x) = posIdeleHom E ⟨Real.exp x, Real.exp_pos x⟩ :=
    fun _ => rfl
  refine ⟨h1, h2, fun j => ?_, fun j w hw => ?_, ?_, fun v v' => ?_, fun v => ⟨_, diag_eq _⟩, fun j l => ?_,
    fun j v => ?_, fun j => ?_⟩
  · rw [Finset.sum_filter, Fintype.sum_prod_type]
    exact h3 j
  · rw [h4 j w hw, Dat.size, Finset.card_filter]
  · rw [Dat.tr, ← map_one (diagUnits n)]
    congr 1
    funext i
    rw [hp, Pi.one_apply, ← map_one (posIdeleHom E)]
    congr 1
    exact Subtype.ext (by simp)
  · rw [Dat.tr, Dat.tr, Dat.tr, ← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, hp, hp, hp, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [add_div, Real.exp_add])
  · obtain ⟨c, hc⟩ := J_eq d j
    obtain ⟨c', hc'⟩ := J_eq d l
    rw [hc, hc']
    exact ((Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun k _ => comm_lie i k).smul_left c).smul_right c'
  · obtain ⟨c, hc⟩ := J_eq d j
    obtain ⟨a, ha⟩ : ∃ a : Fin n → (Cinf E)ˣ, d.tr v = infGL E n (diagUnits n a) := ⟨_, diag_eq _⟩
    rw [hc, ha]
    exact (Commute.sum_left _ _ _ fun i _ => comm_rt i a).smul_left c
  · obtain ⟨c, hc⟩ := J_eq d j
    exact ⟨c • ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, ιC E n (toL (Matrix.single i i 1)), by
      rw [map_smul, map_sum, Finset.sum_congr rfl fun i _ => uC_ιC _]
      exact hc⟩
