import Formalism.PieriBlockIdeals.LastGradedOfGradedAlone
import Formalism.PieriBlockIdeals.PieriColumnMinors.LastGradedImpliesOneBlock
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightShiftEqDetMul
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas

open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA

theorem dualWtSpec : DualWtSpec := by
  intro r M κ
  refine ⟨fun h => ?_, fun a => Nat.sub_le _ _, fun h a b hab => ?_⟩
  · funext a
    simp only [dualWt, Fin.rev_rev]
    have := h a
    omega
  · exact Nat.sub_le_sub_left (h (Fin.rev_le_rev.mpr hab)) M

theorem rev_cast_castAdd_eq_natAdd (p q : ℕ) (a : Fin p) :
    Fin.rev (Fin.cast (Nat.add_comm p q) (Fin.castAdd q a)) = Fin.natAdd q (Fin.rev a) := by
  apply Fin.ext
  have := a.isLt
  simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
  omega

theorem rev_cast_natAdd_eq_castAdd (p q : ℕ) (a : Fin q) :
    Fin.rev (Fin.cast (Nat.add_comm p q) (Fin.natAdd p a)) = Fin.castAdd p (Fin.rev a) := by
  apply Fin.ext
  have := a.isLt
  simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
  omega

theorem blockDual : BlockDual := by
  intro p q w M κ
  funext a
  refine Fin.addCases (fun a' => ?_) (fun a' => ?_) a
  · simp only [dualWt, blockWt, blockWtLast, rev_cast_castAdd_eq_natAdd, Fin.append_left, Fin.append_right]
  · simp only [dualWt, blockWt, blockWtLast, rev_cast_natAdd_eq_castAdd, Fin.append_left, Fin.append_right]

theorem sum_complement_add_sum {p : ℕ} (M : ℕ) (f : Fin p → ℕ) (hf : ∀ a, f a ≤ M) :
    ∑ a, (M - f a) + ∑ a, f a = p * M := by
  rw [← Finset.sum_add_distrib]
  simp [Nat.sub_add_cancel (hf _)]

theorem depthDual : DepthDual := by
  intro p q w M i μ hw hμ
  unfold IsDepthLast IsDepth
  simp only [rev_cast_castAdd_eq_natAdd]
  have h0 : ∑ x : Fin p, (M - μ (Fin.natAdd q x.rev)) = ∑ a : Fin p, (M - μ (Fin.natAdd q a)) :=
    Equiv.sum_comp Fin.revPerm fun a : Fin p => M - μ (Fin.natAdd q a)
  rw [h0]
  have h1 := sum_complement_add_sum M (fun a : Fin p => μ (Fin.natAdd q a)) fun a => hμ _
  have h2 : p * w ≤ p * M := Nat.mul_le_mul_left p hw
  rw [Nat.mul_sub]
  generalize p * w = pw at *
  generalize p * M = pM at *
  omega

theorem initial_minor_degree_le_one {r s : ℕ} (I : Fin s → Fin r) (hs : s ≤ r) (a : Fin r)
    (m : Fin r × Fin r →₀ ℕ) (hm : m ∈ (initMinor ℤ I hs).support) :
    rowDeg m a ≤ if 0 < s then 1 else 0 := by
  classical
  by_cases hI : Function.Injective I
  · unfold initMinor at hm
    rw [Matrix.det_apply] at hm
    have h1 := support_sum hm
    rw [Finset.mem_biUnion] at h1
    obtain ⟨σ, -, hσ⟩ := h1
    rw [Units.smul_def] at hσ
    have hσ' := support_smul hσ
    simp only [Matrix.of_apply] at hσ'
    have h := support_prod_eq_of_additive (fun m => rowDeg m a) (rowDeg_zero a)
      (fun x y => rowDeg_add x y a) Finset.univ
      (fun i : Fin s => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin r) ℤ))
      (fun i => if I (σ i) = a then 1 else 0)
      (by
        intro i _ m' hm'
        have := support_X_subset' (R := ℤ) _ hm'
        rw [Finset.mem_singleton] at this
        subst this
        exact rowDeg_single _ _ _) m hσ'
    rw [h, Equiv.sum_comp σ (fun p => if I p = a then 1 else 0), Finset.sum_boole]
    have hc : (Finset.univ.filter fun p => I p = a).card ≤ 1 := Finset.card_le_one.mpr (by
      intro p hp q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      exact hI (hp.trans hq.symm))
    split_ifs with h0
    · simpa using hc
    · have : s = 0 := by omega
      subst this
      simp
  · exfalso
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨p, q, hpq, hne⟩ := hI
    have h0 : initMinor ℤ I hs = 0 := by
      unfold initMinor
      apply Matrix.det_zero_of_row_eq hne
      funext j
      simp [hpq]
    rw [h0, support_zero] at hm
    exact Finset.notMem_empty _ hm

theorem dual_weyl_degree_bound {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (a : Fin r)
    (x : MvPolynomial (Fin r × Fin r) ℤ) (hx : x ∈ dualWeyl ℤ r r ν) :
    ∀ m ∈ x.support, rowDeg m a ≤ ν ⟨0, a.pos⟩ := by
  classical
  rw [standardMonomialSpan r r ν hν] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := support_prod_le_of_additive (fun m => rowDeg m a) (rowDeg_zero a)
      (fun x y => rowDeg_add x y a) Finset.univ
      (fun k' => initMinor ℤ (I k') (hsz k')) (fun k' => if 0 < sz k' then 1 else 0)
      (fun k' _ m' hm' => initial_minor_degree_le_one (I k') (hsz k') a m' hm') m hm
    rw [← hshape]
    unfold shapeDeg
    rw [Finset.sum_boole] at h
    simpa using h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

theorem wtBound : WtBound := by
  intro r M ν μ hν hM hne a
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hx0
  have hwt : Finsupp.weight (rowW r r) d = μ := hx.2 (MvPolynomial.mem_support_iff.mp hd)
  have h1 : rowDeg d a = μ a := by rw [← ldrow_weight_rowW, hwt]
  rw [← h1]
  exact (dual_weyl_degree_bound ν hν a x hx.1 d hd).trans (hM _)

theorem det_weighted_homog_ones (r : ℕ) : IsWeightedHomogeneous (rowW r r) (genericDet ℤ r) (fun _ => 1) := by
  have h := lpMinor_rowHom ℤ (r := r) (n := r) r le_rfl le_rfl
  rw [leading_minor_full_eq_det ℤ r rfl] at h
  have e : (fun a : Fin r => if a.val < r then 1 else 0) = fun _ => 1 := by
    funext a
    simp [a.isLt]
  rwa [e] at h

theorem exp_le_shift_by_one_iff (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) (hν : Antitone ν) :
    ExpLe l r (fun a => ν a + 1) (fun a => μ a + 1) e ↔ ExpLe l r ν μ e := by
  have e1 : (fun a => μ a + 1) = (fun _ : Fin r => 1) + μ := by
    funext a
    simp [add_comm]
  constructor
  · intro h x hx
    have hx' : genericDet ℤ r * x ∈ nablaWt r (fun a => ν a + 1) (fun a => μ a + 1) := by
      refine ⟨det_mul_mem_dual_weyl_shift ν hx.1, ?_⟩
      rw [e1]
      exact (det_weighted_homog_ones r).mul hx.2
    obtain ⟨m, hm, h1⟩ := h _ hx'
    refine ⟨m, hm, ?_⟩
    rw [weyl_shift_eq_map_det_mul] at h1
    obtain ⟨z, hz, hzz⟩ := h1
    simp only [LinearMap.mulLeft_apply] at hzz
    rw [← mul_smul_comm] at hzz
    rw [← mul_left_cancel₀ (generic_det_ne_zero r) hzz]
    exact hz
  · intro h x hx
    obtain ⟨y, rfl⟩ := det_dvd_of_mem_dual_weyl_shift ν hν hx.1
    have hy : y ∈ nablaWt r ν μ := by
      refine ⟨mem_dual_weyl_of_det_mul ν hx.1, ?_⟩
      have h2 := hx.2
      rw [e1] at h2
      exact weighted_homogeneous_cancel _ _ y (fun _ => 1) μ (generic_det_ne_zero r) (det_weighted_homog_ones r) h2
    obtain ⟨m, hm, h1⟩ := h y hy
    refine ⟨m, hm, ?_⟩
    rw [weyl_shift_eq_map_det_mul]
    refine ⟨_, h1, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    rw [mul_smul_comm]

theorem expTwist : ExpTwist := by
  intro l r c ν μ e hν
  induction c with
  | zero => exact Iff.rfl
  | succ c ih =>
    have hν' : Antitone (fun a => ν a + c) := fun a b hab => Nat.add_le_add_right (hν hab) c
    exact (exp_le_shift_by_one_iff l r (fun a => ν a + c) (fun a => μ a + c) e hν').trans ih

theorem exp_le_cast_iff (l : ℕ) {r r' : ℕ} (h : r' = r) (ν μ : Fin r → ℕ) (e : ℕ) :
    ExpLe l r' (fun a => ν (Fin.cast h a)) (fun a => μ (Fin.cast h a)) e ↔ ExpLe l r ν μ e := by
  subst h
  exact Iff.rfl

theorem depth_two_cast {r r' : ℕ} (h : r' = r) (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ) :
    depth2 (fun a => ξ (Fin.cast h a)) (fun a => lam (Fin.cast h a)) (fun a => μ (Fin.cast h a)) =
      depth2 ξ lam μ := by
  subst h
  rfl

theorem depth_two_of_dual_weights (p q M : ℕ) (ξ : Fin (q + p) → ℤ) (lam μ : Fin (q + p) → ℕ)
    (hl : ∀ a, lam a ≤ M) (hm : ∀ a, μ a ≤ M) :
    depth2 (fun a : Fin (p + q) => -ξ (Fin.rev (Fin.cast (Nat.add_comm p q) a)))
      (fun a => dualWt M lam (Fin.cast (Nat.add_comm p q) a))
      (fun a => dualWt M μ (Fin.cast (Nat.add_comm p q) a)) = depth2 ξ lam μ :=
  (depth_two_cast (Nat.add_comm p q) (fun a => -ξ (Fin.rev a)) (dualWt M lam) (dualWt M μ)).trans
    (depth2Dual _ M ξ lam μ hl hm).1

theorem d_n_empty_eq_one (p w i : ℕ) (f : Fin 0 → ℕ) : Dn p w i f = 1 := by
  unfold Dn
  refine Finset.prod_eq_one fun k _ => ?_
  have h : mu p w i f ((k : ℤ) - ((0 : ℕ) : ℤ)) = 0 := by
    unfold mu
    refine Nat.le_zero.mp (Finset.sup_le fun tau _ => ?_)
    simp [boxesOfContent]
  rw [h, pow_zero]

theorem block_weight_last_le_bound (p q w M : ℕ) (κ : Fin q → ℕ) (hκ : ∀ b, κ b ≤ M) (hw : w ≤ M) (a : Fin (q + p)) :
    blockWtLast p q w κ a ≤ M := by
  unfold blockWtLast
  refine Fin.addCases (fun b => ?_) (fun b => ?_) a
  · rw [Fin.append_left]
    exact hκ b
  · rw [Fin.append_right]
    exact hw

theorem weight_space_ne_bot {r : ℕ} {ν μ : Fin r → ℕ} {x : MvPolynomial (Fin r × Fin r) ℤ} (hx : x ∈ nablaWt r ν μ)
    (hne : x ≠ 0) : nablaWt r ν μ ≠ ⊥ := by
  intro h
  rw [h] at hx
  exact hne ((Submodule.mem_bot _).1 hx)

theorem last_graded_at_of_exp_dual (hE : ExpDual) (hD : LemmaDGraded) (l p q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + p) → ℤ)
    (hl : l.Prime) (ha : Antitone lam2) (hb : ∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) (hwM : w ≤ M) (hξ : Antitone ξ) :
    LemmaDLastGradedAt l p q w M lam2 ξ := by
  intro i' eL heL i μ hd hd2
  have hlamA : Antitone (blockWtLast p q w lam2) := block_weight_last_antitone p q w lam2 ha (fun b => (hb b).1)
  have hlamM := block_weight_last_le_bound p q w M lam2 (fun b => (hb b).2) hwM
  refine exp_le_of_nonzero_weight_vectors l _ _ μ _ hl fun x hx hne => ?_
  have hμM : ∀ a, μ a ≤ M := wtBound _ M _ μ hlamA hlamM (weight_space_ne_bot hx hne)
  rw [hE l (q + p) M _ μ _ hl hlamA hlamM hμM, ← exp_le_cast_iff l (Nat.add_comm p q)]
  have hB := blockDual p q w M lam2
  simp only [dualWt] at hB
  rw [hB]
  have hξs : Antitone fun a : Fin (p + q) => -ξ (Fin.rev (Fin.cast (Nat.add_comm p q) a)) := by
    intro a b hab
    refine neg_le_neg (hξ (Fin.rev_le_rev.mpr ?_))
    exact hab
  refine hD l p q (M - w) (dualWt M lam2) _ hl ((dualWtSpec q M lam2).2.2 ha)
    (fun b => Nat.sub_le_sub_left (hb _).1 M) hξs i' eL ?_ i _ ((depthDual p q w M i μ hwM hμM).1 hd) ?_
  · intro μ2' hdep
    refine exp_le_of_nonzero_weight_vectors l _ _ μ2' _ hl fun y hy hyne => ?_
    have hM2 : ∀ a, μ2' a ≤ M :=
      wtBound _ M _ μ2' ((dualWtSpec q M lam2).2.2 ha) (dualWtSpec q M lam2).2.1 (weight_space_ne_bot hy hyne)
    have e2 : dualWt M (dualWt M μ2') = μ2' := (dualWtSpec q M μ2').1 hM2
    have h3 := (hE l q M lam2 (dualWt M μ2') eL hl ha (fun b => (hb b).2) (dualWtSpec q M μ2').2.1).1
    have h4 : ExpLe l q (dualWt M lam2) (dualWt M (dualWt M μ2')) eL := by
      refine h3 (heL _ ?_)
      rw [← e2, ← blockDual, ← blockDual, depth_two_of_dual_weights p q M ξ _ _ hlamM
        (block_weight_last_le_bound p q w M _ (dualWtSpec q M μ2').2.1 hwM)] at hdep
      exact hdep
    rwa [e2] at h4
  · rw [← blockDual]
    exact (depth_two_of_dual_weights p q M ξ _ μ hlamM hμM).le.trans hd2

theorem lastGradedOfGraded : LastGradedOfGraded := by
  intro hE hD l p q w M lam2 ξ hl ha hb hξ
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have h := last_graded_at_of_exp_dual hE hD l p 0 w (max M w) lam2 ξ hl ha (fun b => b.elim0) (le_max_right _ _) hξ
    intro i' eL heL i μ hd hd2
    have h1 := h i' eL heL i μ hd hd2
    rw [d_n_empty_eq_one] at h1 ⊢
    exact h1
  · exact last_graded_at_of_exp_dual hE hD l p q w M lam2 ξ hl ha hb ((hb ⟨0, hq⟩).1.trans (hb ⟨0, hq⟩).2) hξ

theorem jacobi_complementary_minor {R : Type*} [CommRing R] {m n₁ n₂ : Type*} [Fintype m] [DecidableEq m]
    [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
    (A : Matrix m m R) (ρ γ : n₁ ⊕ n₂ ≃ m) :
    (A.submatrix ρ γ).det * (Matrix.of fun i j : n₁ => A.adjugate (γ (Sum.inl j)) (ρ (Sum.inl i))).det =
      A.det ^ Fintype.card n₁ * (Matrix.of fun i j : n₂ => A (ρ (Sum.inr i)) (γ (Sum.inr j))).det := by
  have hAB : A.submatrix ρ γ * A.adjugate.submatrix γ ρ = A.det • (1 : Matrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) R) := by
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_adjugate, Matrix.submatrix_smul, Pi.smul_apply, Pi.smul_apply,
      Matrix.submatrix_one_equiv]
  generalize hA' : A.submatrix ρ γ = A' at *
  generalize hB : A.adjugate.submatrix γ ρ = B at *
  have h1 := hAB
  rw [← Matrix.fromBlocks_toBlocks A', ← Matrix.fromBlocks_toBlocks B, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_inj] at h1
  obtain ⟨h11, -, h21, -⟩ := h1
  have key : A' * Matrix.fromBlocks B.toBlocks₁₁ 0 B.toBlocks₂₁ 1 =
      Matrix.fromBlocks (A.det • 1) A'.toBlocks₁₂ 0 A'.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks A']
    rw [Matrix.fromBlocks_multiply, h11, h21]
    simp
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  rw [← Matrix.det_transpose (Matrix.of fun i j : n₁ => A.adjugate (γ (Sum.inl j)) (ρ (Sum.inl i)))]
  subst hA' hB
  exact hdet

theorem det_submatrix_eq_or_neg {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m m R) (ρ γ : n ≃ m) :
    (A.submatrix ρ γ).det = A.det ∨ (A.submatrix ρ γ).det = -A.det := by
  have e : A.submatrix ρ γ = (A.submatrix ρ ρ).submatrix id (γ.trans ρ.symm) := by
    ext i j
    simp
  rw [e, Matrix.det_permute', Matrix.det_submatrix_equiv_self]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (γ.trans ρ.symm)) with h | h <;> rw [h] <;> simp

theorem injective_extends_to_equiv {r s t : ℕ} (h : s + t = r) (f : Fin s → Fin r) (hf : Function.Injective f) :
    ∃ ρ : Fin s ⊕ Fin t ≃ Fin r, ∀ p, ρ (Sum.inl p) = f p := by
  classical
  have hc : Fintype.card ↥(Set.range f)ᶜ = t := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective hf]
    simp
    omega
  let e1 : Fin s ≃ ↥(Set.range f) := Equiv.ofInjective f hf
  let e2 : Fin t ≃ ↥(Set.range f)ᶜ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨(Equiv.sumCongr e1 e2).trans (Equiv.Set.sumCompl (Set.range f)), fun p => ?_⟩
  simp [e1]

def finSumEquivOfAddEq {r s t : ℕ} (h : s + t = r) : Fin s ⊕ Fin t ≃ Fin r :=
  ((Equiv.sumCongr Fin.revPerm (Equiv.refl (Fin t))).trans (Equiv.sumComm _ _)).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

theorem ld3Gam_inl {r s t : ℕ} (h : s + t = r) (q : Fin s) :
    finSumEquivOfAddEq h (Sum.inl q) = Fin.rev (Fin.castLE (by omega) q) := by
  apply Fin.ext
  have := q.isLt
  simp [finSumEquivOfAddEq]
  omega

theorem ld3Gam_inr {r s t : ℕ} (h : s + t = r) (q : Fin t) :
    finSumEquivOfAddEq h (Sum.inr q) = Fin.castLE (by omega) q := by
  apply Fin.ext
  simp [finSumEquivOfAddEq]

theorem gen_det_eq_det (r : ℕ) : genDet r = genericDet ℤ r := rfl

theorem cofactor_of_variable (r : ℕ) (a s : Fin r) :
    cofMap r (X (a, s)) = (genericMatrix' ℤ r).adjugate (Fin.rev s) (Fin.rev a) := by
  unfold cofMap
  rw [aeval_X]
  rfl

theorem cofactor_initial_minor {r s t : ℕ} (h : s + t = r) (I : Fin s → Fin r) (hs : s ≤ r) :
    ∃ g ∈ dualWeyl ℤ r r (initW r t), genericDet ℤ r * cofMap r (initMinor ℤ I hs) = genericDet ℤ r ^ s * g := by
  by_cases hI : Function.Injective I
  · obtain ⟨ρ, hρ⟩ := injective_extends_to_equiv h (fun p => Fin.rev (I p)) (fun p q hpq => hI (Fin.rev_injective hpq))
    have J := jacobi_complementary_minor (genericMatrix' ℤ r) ρ (finSumEquivOfAddEq h)
    have e1 : (Matrix.of fun i j : Fin s =>
        (genericMatrix' ℤ r).adjugate (finSumEquivOfAddEq h (Sum.inl j)) (ρ (Sum.inl i))).det = cofMap r (initMinor ℤ I hs) := by
      unfold initMinor
      rw [algHom_det_of]
      congr 1
      ext i j
      simp only [Matrix.of_apply, cofactor_of_variable, hρ, ld3Gam_inl]
    have e2 : (Matrix.of fun i j : Fin t => genericMatrix' ℤ r (ρ (Sum.inr i)) (finSumEquivOfAddEq h (Sum.inr j))).det =
        initMinor ℤ (fun i => ρ (Sum.inr i)) (by omega : t ≤ r) := by
      unfold initMinor
      refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
      simp only [Matrix.of_apply, ld3Gam_inr, genericMatrix']
    rw [e1, e2, Fintype.card_fin] at J
    change _ = genericDet ℤ r ^ s * _ at J
    rcases det_submatrix_eq_or_neg (genericMatrix' ℤ r) ρ (finSumEquivOfAddEq h) with hd | hd
    · rw [hd] at J
      exact ⟨_, initMinor_mem _ _, J⟩
    · rw [hd] at J
      refine ⟨-_, Submodule.neg_mem _ (initMinor_mem (fun i => ρ (Sum.inr i)) (by omega : t ≤ r)), ?_⟩
      rw [mul_neg, ← J]
      unfold genericDet
      ring
  · simp only [Function.Injective, not_forall] at hI
    obtain ⟨p, q, hpq, hne⟩ := hI
    have h0 : initMinor ℤ I hs = 0 := by
      unfold initMinor
      apply Matrix.det_zero_of_row_eq hne
      funext j
      simp [hpq]
    exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero, mul_zero, mul_zero]⟩

theorem cofactor_leading_minor {r s t : ℕ} (h : s + t = r) (hs : s ≤ r) (ht : t ≤ r) :
    genericDet ℤ r * cofMap r (lpMinor ℤ s hs hs) = genericDet ℤ r ^ s * lpMinor ℤ t ht ht := by
  have J := jacobi_complementary_minor (genericMatrix' ℤ r) (finSumEquivOfAddEq h) (finSumEquivOfAddEq h)
  have e1 : (Matrix.of fun i j : Fin s =>
      (genericMatrix' ℤ r).adjugate (finSumEquivOfAddEq h (Sum.inl j)) (finSumEquivOfAddEq h (Sum.inl i))).det =
        cofMap r (lpMinor ℤ s hs hs) := by
    unfold lpMinor
    rw [algHom_det_of]
    congr 1
    ext i j
    simp only [Matrix.of_apply, cofactor_of_variable, ld3Gam_inl]
  have e2 : (Matrix.of fun i j : Fin t => genericMatrix' ℤ r (finSumEquivOfAddEq h (Sum.inr i)) (finSumEquivOfAddEq h (Sum.inr j))).det =
      lpMinor ℤ t ht ht := by
    unfold lpMinor
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [Matrix.of_apply, ld3Gam_inr, genericMatrix']
  rw [e1, e2, Fintype.card_fin, Matrix.det_submatrix_equiv_self] at J
  exact J

theorem cofactor_bideterminant {r K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r) (I : ∀ k, Fin (sz k) → Fin r) :
    ∃ g ∈ dualWeyl ℤ r r (∑ k, initW r (r - sz k)),
      genericDet ℤ r ^ K * cofMap r (bideterminant ℤ sz hsz I) = genericDet ℤ r ^ (∑ k, sz k) * g := by
  choose g hg hg' using fun k => cofactor_initial_minor (Nat.add_sub_cancel' (hsz k)) (I k) (hsz k)
  refine ⟨∏ k, g k, dualWeyl_prod _ _ _ fun k _ => hg k, ?_⟩
  unfold bideterminant
  rw [map_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  simp only [← hg']
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem shape_complement_sum {r K : ℕ} (sz : Fin K → ℕ) (t : Fin r) :
    (∑ k, initW r (r - sz k)) t + shapeDeg sz (Fin.rev t) = K := by
  unfold shapeDeg
  rw [Finset.sum_apply, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ k : Fin K, initW r (r - sz k) t + (if (Fin.rev t).val < sz k then 1 else 0) = 1 := by
    intro k
    have := t.isLt
    unfold initW
    rw [Fin.val_rev]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl fun k _ => h k]
  simp

theorem shape_total_degree {r K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r) :
    ∑ k, sz k = ∑ t : Fin r, shapeDeg sz t := by
  have e := sum_min_eq_shapeDeg sz hsz r
  have e1 : ∀ k', min r (sz k') = sz k' := fun k' => min_eq_right (hsz k')
  simp only [e1] at e
  rw [Finset.filter_true_of_mem (fun t _ => t.isLt)] at e
  exact e

theorem det_pow_mul_mem_dual_weyl {r : ℕ} (ν : Fin r → ℕ) (c : ℕ) {g : MvPolynomial (Fin r × Fin r) ℤ}
    (hg : g ∈ dualWeyl ℤ r r ν) : genericDet ℤ r ^ c * g ∈ dualWeyl ℤ r r (fun a => ν a + c) := by
  induction c with
  | zero => simpa using hg
  | succ c ih =>
    rw [pow_succ', mul_assoc]
    exact det_mul_mem_dual_weyl_shift (fun a => ν a + c) ih

theorem dual_weyl_shift_eq_det_pow_mul {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (c : ℕ)
    {f : MvPolynomial (Fin r × Fin r) ℤ} (hf : f ∈ dualWeyl ℤ r r (fun a => ν a + c)) :
    ∃ g ∈ dualWeyl ℤ r r ν, f = genericDet ℤ r ^ c * g := by
  induction c generalizing f with
  | zero => exact ⟨f, by simpa using hf, by simp⟩
  | succ c ih =>
    have hν' : Antitone (fun a => ν a + c) := fun a b hab => Nat.add_le_add_right (hν hab) c
    obtain ⟨y, rfl⟩ := det_dvd_of_mem_dual_weyl_shift (fun a => ν a + c) hν' hf
    obtain ⟨g, hg, rfl⟩ := ih (mem_dual_weyl_of_det_mul (fun a => ν a + c) hf)
    exact ⟨g, hg, by rw [pow_succ', mul_assoc]⟩

theorem genericDet_pow_ne_zero (r c : ℕ) : genericDet ℤ r ^ c ≠ 0 := pow_ne_zero _ (generic_det_ne_zero r)

theorem nablaDual : NablaDual := by
  intro r M ν hν hM x hx
  rw [gen_det_eq_det]
  have hνs : Antitone (dualWt M ν) := (dualWtSpec r M ν).2.2 hν
  rw [standardMonomialSpan r r ν hν] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    obtain ⟨g, hg, hg'⟩ := cofactor_bideterminant sz hsz I
    rw [shape_total_degree sz hsz, hshape] at hg'
    have hK : ∀ t : Fin r, (∑ k, initW r (r - sz k)) t + ν (Fin.rev t) = K := by
      intro t
      rw [← hshape]
      exact shape_complement_sum sz t
    rcases le_total K M with hKM | hKM
    · refine ⟨genericDet ℤ r ^ (M - K) * g, dualWeyl_of_eq (det_pow_mul_mem_dual_weyl _ (M - K) hg) ?_, ?_⟩
      · funext t
        have := hK t
        unfold dualWt
        omega
      · rw [mul_left_comm, ← hg', ← mul_assoc, ← pow_add, Nat.sub_add_cancel hKM]
    · have hg2 : g ∈ dualWeyl ℤ r r (fun a => dualWt M ν a + (K - M)) := by
        refine dualWeyl_of_eq hg ?_
        funext t
        have := hK t
        have := hM (Fin.rev t)
        unfold dualWt
        omega
      obtain ⟨g', hg3, rfl⟩ := dual_weyl_shift_eq_det_pow_mul _ hνs (K - M) hg2
      refine ⟨g', hg3, mul_left_cancel₀ (genericDet_pow_ne_zero r (K - M)) ?_⟩
      rw [mul_left_comm, ← hg', ← mul_assoc, ← pow_add, Nat.sub_add_cancel hKM]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨g, hg, hg'⟩ := hx
    obtain ⟨g2, hg2, hg2'⟩ := hy
    exact ⟨g + g2, Submodule.add_mem _ hg hg2, by rw [mul_add, map_add, mul_add, hg', hg2']⟩
  | smul c x _ hx =>
    obtain ⟨g, hg, hg'⟩ := hx
    exact ⟨c • g, Submodule.smul_mem _ c hg, by rw [mul_smul_comm, map_smul, mul_smul_comm, hg']⟩

theorem adjugate_entry_weighted_homog (r : ℕ) (i j : Fin r) :
    IsWeightedHomogeneous (rowW r r) ((genericMatrix' ℤ r).adjugate i j) (fun c => if c = j then 0 else 1) := by
  classical
  rw [Matrix.adjugate_apply, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [← mem_weightedHomogeneousSubmodule]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule]
  have e : (fun c : Fin r => if c = j then 0 else 1) =
      ∑ k, (if σ k = j then (0 : Fin r → ℕ) else Pi.single (σ k) 1) := by
    rw [Equiv.sum_comp σ (fun c => if c = j then (0 : Fin r → ℕ) else Pi.single c 1)]
    funext c
    rw [Finset.sum_apply, Finset.sum_eq_single c]
    · split_ifs <;> simp
    · intro b _ hb
      split_ifs
      · rfl
      · simp [hb]
    · simp
  rw [e]
  refine IsWeightedHomogeneous.prod _ _ _ fun k _ => ?_
  by_cases h : σ k = j
  · rw [if_pos h, h, Matrix.updateRow_self, Pi.single_apply]
    split_ifs
    · exact isWeightedHomogeneous_one _ _
    · exact isWeightedHomogeneous_zero _ _ _
  · rw [if_neg h, Matrix.updateRow_ne h]
    exact isWeightedHomogeneous_X ℤ (rowW r r) _

theorem aeval_weighted_homog {σ τ Mo : Type*} [AddCommMonoid Mo] (w : τ → Mo) (φ : σ → MvPolynomial τ ℤ) (ω : σ → Mo)
    (hφ : ∀ v, IsWeightedHomogeneous w (φ v) (ω v)) (x : MvPolynomial σ ℤ) (κ : Mo)
    (hx : IsWeightedHomogeneous ω x κ) : IsWeightedHomogeneous w (aeval φ x) κ := by
  conv => enter [2, 2]; rw [x.as_sum]
  rw [map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial, ← hx (mem_support_iff.mp hd), Finsupp.weight_apply, MvPolynomial.algebraMap_eq]
  refine IsWeightedHomogeneous.C_mul ?_ _
  unfold Finsupp.prod Finsupp.sum
  exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _

def diagonalEntryIndicator (r : ℕ) : Fin r × Fin r → Fin r → ℕ := fun v c => if c = Fin.rev v.1 then 0 else 1

theorem weight_omega_add_degree {r : ℕ} (d : Fin r × Fin r →₀ ℕ) (c : Fin r) :
    Finsupp.weight (diagonalEntryIndicator r) d c + rowDeg d (Fin.rev c) = ∑ a, rowDeg d a := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  have h1 : ∀ a : Fin r, ∑ s : Fin r, (d (a, s) • diagonalEntryIndicator r (a, s)) c = if a = Fin.rev c then 0 else rowDeg d a := by
    intro a
    have e : (c = Fin.rev a) ↔ (a = Fin.rev c) := by
      constructor <;> (intro h; rw [h, Fin.rev_rev])
    unfold rowDeg
    split_ifs with h
    · refine Finset.sum_eq_zero fun s _ => ?_
      simp [diagonalEntryIndicator, e.2 h]
    · refine Finset.sum_congr rfl fun s _ => ?_
      have h' : ¬ c = Fin.rev a := fun h' => h (e.1 h')
      simp [diagonalEntryIndicator, h']
  rw [Finset.sum_congr rfl fun a _ => h1 a]
  have h2 : rowDeg d (Fin.rev c) = ∑ a, if a = Fin.rev c then rowDeg d a else 0 := by simp
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

theorem cofactor_weighted_homog {r : ℕ} (μ : Fin r → ℕ) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : IsWeightedHomogeneous (rowW r r) x μ) :
    IsWeightedHomogeneous (rowW r r) (cofMap r x) (fun c => ∑ a, μ a - μ (Fin.rev c)) := by
  unfold cofMap
  refine aeval_weighted_homog (rowW r r) _ (diagonalEntryIndicator r) (fun v => adjugate_entry_weighted_homog r _ _) x _ ?_
  intro d hd
  have hwt := hx hd
  funext c
  have h := weight_omega_add_degree d c
  simp only [← ldrow_weight_rowW, hwt] at h
  omega

theorem det_pow_weighted_homog (r N : ℕ) : IsWeightedHomogeneous (rowW r r) (genericDet ℤ r ^ N) (fun _ => N) := by
  have h := (det_weighted_homog_ones r).pow N
  have e : (N • fun _ : Fin r => 1) = fun _ => N := by
    funext a
    simp
  rwa [e] at h

theorem dualWeight : DualWeight := by
  intro r M μ x g hM hx hrel
  rw [gen_det_eq_det] at hrel
  refine weighted_homogeneous_cancel (rowW r r) (genericDet ℤ r ^ (∑ a, μ a)) g (fun _ => ∑ a, μ a) (dualWt M μ)
    (genericDet_pow_ne_zero r _) (det_pow_weighted_homog r _) ?_
  rw [hrel]
  have h := (det_pow_weighted_homog r M).mul (cofactor_weighted_homog μ x hx)
  have e : ((fun _ => M) + fun c => ∑ a, μ a - μ (Fin.rev c)) = (fun _ : Fin r => ∑ a, μ a) + dualWt M μ := by
    funext c
    have h1 := hM (Fin.rev c)
    have h2 : μ (Fin.rev c) ≤ ∑ a, μ a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    simp only [Pi.add_apply, dualWt]
    omega
  rwa [e] at h

theorem cofactor_map_generic_matrix (r : ℕ) : (cofMap r).mapMatrix (genericMatrix' ℤ r) =
    ((genericMatrix' ℤ r).adjugate.transpose).submatrix Fin.revPerm Fin.revPerm := by
  refine Matrix.ext fun a s => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
    Fin.revPerm_apply]
  exact cofactor_of_variable r a s

theorem cofactor_det_eq_pow (r : ℕ) : cofMap r (genericDet ℤ r) = genericDet ℤ r ^ (r - 1) := by
  unfold genericDet
  rw [AlgHom.map_det, cofactor_map_generic_matrix, Matrix.det_submatrix_equiv_self, Matrix.det_transpose, Matrix.det_adjugate,
    Fintype.card_fin]

theorem adjugate_adjugate_smul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    A.det • A.adjugate.adjugate = A.det ^ (Fintype.card n - 1) • A := by
  have h1 : A * (A.adjugate * A.adjugate.adjugate) = A.det ^ (Fintype.card n - 1) • A := by
    rw [Matrix.mul_adjugate, Matrix.det_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [← h1, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]

theorem cofactor_cofactor_variable (r : ℕ) (v : Fin r × Fin r) :
    genericDet ℤ r * cofMap r (cofMap r (X v)) = genericDet ℤ r ^ (r - 1) * X v := by
  obtain ⟨a, s⟩ := v
  have h1 : cofMap r (cofMap r (X (a, s))) = (genericMatrix' ℤ r).adjugate.adjugate a s := by
    rw [cofactor_of_variable]
    have h2 : cofMap r ((genericMatrix' ℤ r).adjugate (Fin.rev s) (Fin.rev a)) =
        (cofMap r).mapMatrix (genericMatrix' ℤ r).adjugate (Fin.rev s) (Fin.rev a) := rfl
    rw [h2, AlgHom.map_adjugate, cofactor_map_generic_matrix, Matrix.adjugate_submatrix_equiv_self, ← Matrix.adjugate_transpose]
    simp
  have h3 := congrFun (congrFun (adjugate_adjugate_smul (genericMatrix' ℤ r)) a) s
  rw [Fintype.card_fin] at h3
  rw [h1]
  exact h3

theorem pow_mul_eval_homogeneous_eq {σ S : Type*} [CommRing S] (φ ψ : MvPolynomial σ ℤ →ₐ[ℤ] S) (d e : S)
    (h : ∀ v, d * φ (X v) = e * ψ (X v)) (N : ℕ) (x : MvPolynomial σ ℤ) (hx : x.IsHomogeneous N) :
    d ^ N * φ x = e ^ N * ψ x := by
  conv_lhs => rw [x.as_sum]
  conv_rhs => rw [x.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hN : ∑ v ∈ m.support, m v = N := by
    have := hx (mem_support_iff.mp hm)
    rw [Finsupp.weight_apply] at this
    simpa [Finsupp.sum] using this
  rw [monomial_eq, map_mul, map_mul, Finsupp.prod, map_prod, map_prod, ← hN, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum, mul_left_comm, mul_left_comm _ (ψ _), ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, algHom_C, algHom_C]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_pow, map_pow, ← mul_pow, ← mul_pow, h]

theorem cofCof : CofCof := by
  intro r
  refine ⟨cofactor_det_eq_pow r, fun N x hx => ?_⟩
  have h := pow_mul_eval_homogeneous_eq ((cofMap r).comp (cofMap r)) (AlgHom.id ℤ _) (genericDet ℤ r) (genericDet ℤ r ^ (r - 1))
    (fun v => cofactor_cofactor_variable r v) N x hx
  rw [← pow_mul] at h
  exact h

theorem generator_diag_variable {r : ℕ} (a : Fin r) (v : Fin r × Fin r) :
    rowGen ℤ a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (lgraded_wa (n := r) a v) := by
  rw [rowGen, aeval_X]
  unfold lgraded_wa
  split_ifs with h
  · obtain ⟨b, s⟩ := v
    simp only at h
    subst h
    ring
  · simp

theorem generator_diag_constant {r : ℕ} (a : Fin r) (c : ℤ) :
    rowGen ℤ a a (C c : MvPolynomial (Fin r × Fin r) ℤ) = Polynomial.C (C c) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem generator_diag_monomial {r : ℕ} (a : Fin r) (m : Fin r × Fin r →₀ ℕ) (c : ℤ) :
    rowGen ℤ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, generator_diag_constant]
  simp_rw [map_pow, generator_diag_variable, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  rw [Finsupp.weight_apply, Finsupp.sum, map_mul, map_prod]
  simp_rw [map_pow, smul_eq_mul, mul_comm (lgraded_wa a _)]
  ring

theorem divided_power_diag_weight_vector {r : ℕ} (a : Fin r) (k : ℕ) (μ : Fin r → ℕ) (y : MvPolynomial (Fin r × Fin r) ℤ)
    (hy : IsWeightedHomogeneous (rowW r r) y μ) : rowDiv ℤ a a k y = ((μ a).choose k : ℤ) • y := by
  have h1 : rowDivL ℤ a a k y = ((μ a).choose k : ℤ) • y := by
    conv_lhs => rw [y.as_sum]
    conv_rhs => rw [y.as_sum]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [rowDivL_apply, rowDiv, generator_diag_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
      ← lgraded_weight_rowW, hy (mem_support_iff.mp hd), smul_eq_C_mul, mul_comm]
    simp
  exact h1

def columnWeight {r : ℕ} (c : Fin r) : Fin r × Fin r → ℤ := fun v => ((lgraded_wa (n := r) c v : ℕ) : ℤ)

theorem weight_wc_eq_degree {r : ℕ} (c : Fin r) (d : Fin r × Fin r →₀ ℕ) :
    Finsupp.weight (columnWeight c) d = ((Finsupp.weight (rowW r r) d c : ℕ) : ℤ) := by
  rw [lgraded_weight_rowW, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [columnWeight]

theorem divided_power_weight_vector {r : ℕ} (a b : Fin r) (k : ℕ) (μ : Fin r → ℕ) (y : MvPolynomial (Fin r × Fin r) ℤ)
    (hy : IsWeightedHomogeneous (rowW r r) y μ) :
    ∃ μ', IsWeightedHomogeneous (rowW r r) (rowDiv ℤ a b k y) μ' := by
  by_cases h0 : rowDiv ℤ a b k y = 0
  · exact ⟨0, by rw [h0]; exact isWeightedHomogeneous_zero _ _ _⟩
  · obtain ⟨d0, hd0⟩ := MvPolynomial.support_nonempty.mpr h0
    have key : ∀ c : Fin r, ∀ d, coeff d (rowDiv ℤ a b k y) ≠ 0 →
        ((Finsupp.weight (rowW r r) d c : ℕ) : ℤ) =
          (μ c : ℤ) + k * ((if a = c then 1 else 0) - (if b = c then 1 else 0)) := by
      intro c d hd
      have hyc : IsWeightedHomogeneous (columnWeight c) y (μ c : ℤ) := by
        intro d' hd'
        rw [weight_wc_eq_degree, hy hd']
      have hs := lehw_rowDiv_shift ℤ (columnWeight c) ((if a = c then 1 else 0) - (if b = c then 1 else 0)) a b
        (by
          intro s
          simp only [columnWeight, lgraded_wa]
          split_ifs <;> simp) (μ c : ℤ) k y hyc
      rw [← weight_wc_eq_degree]
      exact hs hd
    refine ⟨Finsupp.weight (rowW r r) d0, fun d hd => ?_⟩
    funext c
    have h1 := key c d hd
    have h2 := key c d0 (mem_support_iff.mp hd0)
    rw [← h2] at h1
    exact_mod_cast h1

theorem eq_sum_weighted_components {r : ℕ} (x : MvPolynomial (Fin r × Fin r) ℤ) :
    ∃ S : Finset (Fin r → ℕ), x = ∑ μ ∈ S, weightedHomogeneousComponent (rowW r r) μ x :=
  ⟨_, by rw [← finsum_eq_sum _ (weightedHomogeneousComponent_finsupp x), sum_weightedHomogeneousComponent]⟩

theorem weyl_le_of_stable_submodule {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (L : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ))
    (h0 : hw ℤ le_rfl ν ∈ L)
    (hs : ∀ a b : Fin r, a ≠ b → ∀ (k : ℕ) (f : MvPolynomial (Fin r × Fin r) ℤ), f ∈ L → rowDiv ℤ a b k f ∈ L) :
    weyl ℤ r r le_rfl ν ≤ L := by
  classical
  let L' : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ) :=
    ⨅ μ : Fin r → ℕ, L.comap (weightedHomogeneousComponent (rowW r r) μ)
  have hL' : ∀ x, x ∈ L' ↔ ∀ μ, weightedHomogeneousComponent (rowW r r) μ x ∈ L := by
    intro x
    simp [L', Submodule.mem_iInf]
  have hcomp : ∀ z ∈ L, (∃ μ', IsWeightedHomogeneous (rowW r r) z μ') →
      ∀ μ, weightedHomogeneousComponent (rowW r r) μ z ∈ L := by
    rintro z hz ⟨μ', hμ'⟩ μ
    by_cases h : μ = μ'
    · subst h
      rw [hμ'.weightedHomogeneousComponent_same]
      exact hz
    · rw [hμ'.weightedHomogeneousComponent_ne μ h]
      exact L.zero_mem
  have hle : L' ≤ L := by
    intro x hx
    obtain ⟨S, hS⟩ := eq_sum_weighted_components x
    rw [hS]
    exact L.sum_mem fun μ _ => (hL' x).1 hx μ
  refine (la_weyl_le_of_stable ℤ le_rfl ν L' ?_ ?_).trans hle
  · rw [hL']
    exact hcomp _ h0 ⟨_, hwRowWeight ℤ r r le_rfl ν hν⟩
  · intro a b k f hf
    rw [hL'] at hf ⊢
    intro μ
    obtain ⟨S, hS⟩ := eq_sum_weighted_components f
    have hT : weightedHomogeneousComponent (rowW r r) μ (rowDiv ℤ a b k f) =
        ∑ μ' ∈ S, weightedHomogeneousComponent (rowW r r) μ
          (rowDiv ℤ a b k (weightedHomogeneousComponent (rowW r r) μ' f)) := by
      conv_lhs => rw [hS]
      rw [← rowDivL_apply, map_sum, map_sum]
      rfl
    rw [hT]
    refine L.sum_mem fun μ' _ => ?_
    have hh := weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW r r) μ' f
    refine hcomp _ ?_ (divided_power_weight_vector a b k μ' _ hh) μ
    by_cases hab : a = b
    · subst hab
      rw [divided_power_diag_weight_vector a k μ' _ hh]
      exact L.smul_mem _ (hf μ')
    · exact hs a b hab k _ (hf μ')

theorem eval_neg_x_coeff {S : Type*} [CommRing S] (φ : S →+* S) (p : Polynomial S) (k : ℕ) :
    (Polynomial.eval₂ (Polynomial.C.comp φ) (-Polynomial.X) p).coeff k = (-1) ^ k * φ (p.coeff k) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, Polynomial.coeff_add, Polynomial.coeff_add, hp, hq, map_add, mul_add]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, RingHom.comp_apply, Polynomial.coeff_C_mul, neg_pow, Polynomial.coeff_monomial,
      ← Polynomial.C_1, ← Polynomial.C_neg, ← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : n = k
    · subst h
      simp
      ring
    · simp [h, Ne.symm h]

theorem adjugate_transvection' {S : Type*} [CommRing S] {n : Type*} [Fintype n] [DecidableEq n] (i j : n)
    (h : i ≠ j) (c : S) : (Matrix.transvection i j c).adjugate = Matrix.transvection i j (-c) := by
  have h1 : Matrix.transvection i j c * Matrix.transvection i j (-c) = 1 := by
    rw [Matrix.transvection_mul_transvection_same i j h, add_neg_cancel, Matrix.transvection_zero]
  calc (Matrix.transvection i j c).adjugate
      = (Matrix.transvection i j c).adjugate * (Matrix.transvection i j c * Matrix.transvection i j (-c)) := by
        rw [h1, Matrix.mul_one]
    _ = Matrix.transvection i j (-c) := by
        rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.det_transvection_of_ne i j h, one_smul, Matrix.one_mul]

theorem generator_map_generic_matrix {r : ℕ} (a b : Fin r) : (rowGen ℤ a b).mapMatrix (genericMatrix' ℤ r) =
    Matrix.transvection b a Polynomial.X * Polynomial.C.mapMatrix (genericMatrix' ℤ r) := by
  refine Matrix.ext fun p q => ?_
  by_cases hp : p = b
  · subst hp
    rw [Matrix.transvection_mul_apply_same]
    simp [rowGen_X, genericMatrix']
  · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hp]
    simp [rowGen_X, genericMatrix', hp]

theorem cofactor_intertwines_generator {r : ℕ} (a b : Fin r) (hab : a ≠ b) (x : MvPolynomial (Fin r × Fin r) ℤ) :
    rowGen ℤ a b (cofMap r x) =
      Polynomial.eval₂ (Polynomial.C.comp (cofMap r).toRingHom) (-Polynomial.X)
        (rowGen ℤ (Fin.rev b) (Fin.rev a) x) := by
  have key : (rowGen ℤ a b).toRingHom.comp (cofMap r).toRingHom =
      (Polynomial.eval₂RingHom (Polynomial.C.comp (cofMap r).toRingHom) (-Polynomial.X)).comp
        (rowGen ℤ (Fin.rev b) (Fin.rev a)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
    obtain ⟨c, s⟩ := v
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coe_eval₂RingHom]
    rw [cofactor_of_variable, rowGen_X]
    have h2 : rowGen ℤ a b ((genericMatrix' ℤ r).adjugate (Fin.rev s) (Fin.rev c)) =
        (rowGen ℤ a b).mapMatrix (genericMatrix' ℤ r).adjugate (Fin.rev s) (Fin.rev c) := rfl
    rw [h2, AlgHom.map_adjugate, generator_map_generic_matrix, Matrix.adjugate_mul_distrib,
      adjugate_transvection' b a hab.symm, ← RingHom.map_adjugate]
    by_cases hc : c = Fin.rev a
    · subst hc
      rw [Fin.rev_rev, Matrix.mul_transvection_apply_same]
      simp [cofactor_of_variable]
    · have hc' : Fin.rev c ≠ a := fun h => hc (by rw [← h, Fin.rev_rev])
      rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hc']
      simp [cofactor_of_variable, hc]
  exact congrArg (fun F => F x) key

theorem divided_power_cofactor {r : ℕ} (a b : Fin r) (hab : a ≠ b) (k : ℕ) (x : MvPolynomial (Fin r × Fin r) ℤ) :
    rowDiv ℤ a b k (cofMap r x) = (-1) ^ k * cofMap r (rowDiv ℤ (Fin.rev b) (Fin.rev a) k x) := by
  unfold rowDiv
  rw [cofactor_intertwines_generator a b hab, eval_neg_x_coeff]
  rfl

theorem divided_power_det_pow_mul {r : ℕ} (a b : Fin r) (hab : a ≠ b) (k n : ℕ) (f : MvPolynomial (Fin r × Fin r) ℤ) :
    rowDiv ℤ a b k (genericDet ℤ r ^ n * f) = genericDet ℤ r ^ n * rowDiv ℤ a b k f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, divided_power_det_mul_of_ne ℤ a b hab, ih, mul_assoc]

noncomputable def leadingMinorPolynomial (r s : ℕ) : MvPolynomial (Fin r × Fin r) ℤ := if h : s ≤ r then lpMinor ℤ s h h else 1

def partialSumOfExponents {r : ℕ} (ν : Fin r → ℕ) (s : ℕ) : ℕ := if h : s < r then ν ⟨s, h⟩ else 0

theorem partial_sequence_val {r : ℕ} (ν : Fin r → ℕ) (s : Fin r) : partialSumOfExponents ν s.val = ν s := dif_pos s.isLt

theorem partial_sequence_antitone {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (s : ℕ) : partialSumOfExponents ν (s + 1) ≤ partialSumOfExponents ν s := by
  unfold partialSumOfExponents
  by_cases h : s + 1 < r
  · rw [dif_pos h, dif_pos (by omega)]
    exact hν (Fin.le_def.mpr (by simp))
  · rw [dif_neg h]
    exact Nat.zero_le _

theorem partial_sequence_top_eq_zero {r : ℕ} (ν : Fin r → ℕ) : partialSumOfExponents ν r = 0 := dif_neg (lt_irrefl r)

theorem partial_sequence_sum {r : ℕ} (ν : Fin r → ℕ) : ∑ s ∈ Finset.range r, partialSumOfExponents ν s = ∑ a, ν a := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun s _ => partial_sequence_val ν s

theorem highest_weight_prod_leading_minors {r : ℕ} (ν : Fin r → ℕ) :
    hw ℤ le_rfl ν = ∏ s ∈ Finset.range r, leadingMinorPolynomial r (s + 1) ^ (partialSumOfExponents ν s - partialSumOfExponents ν (s + 1)) := by
  rw [← Fin.prod_univ_eq_prod_range (fun s => leadingMinorPolynomial r (s + 1) ^ (partialSumOfExponents ν s - partialSumOfExponents ν (s + 1)))]
  unfold hw
  refine Finset.prod_congr rfl fun s _ => ?_
  have h1 : leadingMinorPolynomial r (s.val + 1) = lpMinor ℤ (s.val + 1) (by omega) (by omega) := dif_pos (by omega)
  have h2 : nuNext ν s = partialSumOfExponents ν (s.val + 1) := rfl
  rw [h1, h2, partial_sequence_val]

theorem cofactor_leading_minor_pow {r s t : ℕ} (h : s + t = r) :
    genericDet ℤ r * cofMap r (leadingMinorPolynomial r s) = genericDet ℤ r ^ s * leadingMinorPolynomial r t := by
  unfold leadingMinorPolynomial
  rw [dif_pos (by omega), dif_pos (by omega)]
  exact cofactor_leading_minor h _ _

theorem telescoping_sum_eq_head (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) (n : ℕ) :
    ∑ s ∈ Finset.range n, (f s - f (s + 1)) + f n = f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := hf n
    omega

theorem telescoping_weighted_sum (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) (n : ℕ) :
    ∑ s ∈ Finset.range n, (s + 1) * (f s - f (s + 1)) + n * f n = ∑ s ∈ Finset.range n, f s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (hf n)
    rw [hc, Nat.add_sub_cancel_left]
    ring

noncomputable def ld3Q {r : ℕ} (ν : Fin r → ℕ) : MvPolynomial (Fin r × Fin r) ℤ :=
  ∏ s ∈ Finset.range r, leadingMinorPolynomial r (r - (s + 1)) ^ (partialSumOfExponents ν s - partialSumOfExponents ν (s + 1))

theorem cofactor_highest_weight {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) :
    genericDet ℤ r ^ (partialSumOfExponents ν 0) * cofMap r (hw ℤ le_rfl ν) = genericDet ℤ r ^ (∑ a, ν a) * ld3Q ν := by
  have h1 := telescoping_sum_eq_head (partialSumOfExponents ν) (partial_sequence_antitone ν hν) r
  have h2 := telescoping_weighted_sum (partialSumOfExponents ν) (partial_sequence_antitone ν hν) r
  rw [partial_sequence_top_eq_zero, add_zero] at h1
  rw [partial_sequence_top_eq_zero, mul_zero, add_zero, partial_sequence_sum] at h2
  rw [← h1, ← h2, highest_weight_prod_leading_minors, map_prod, ld3Q, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.mp hs
  rw [map_pow, ← mul_pow, cofactor_leading_minor_pow (show (s + 1) + (r - (s + 1)) = r by omega), mul_pow, ← pow_mul]

theorem leading_minor_zero_eq_one (r s : ℕ) (hs : s = 0) : leadingMinorPolynomial r s = 1 := by
  subst hs
  simp [leadingMinorPolynomial, lpMinor]

theorem partial_sequence_dual {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (t : ℕ) (ht : t < r) :
    partialSumOfExponents (dualWt M ν) t = M - partialSumOfExponents ν (r - (t + 1)) := by
  unfold partialSumOfExponents dualWt
  rw [dif_pos ht, dif_pos (by omega)]
  rfl

theorem highest_weight_dual_weight {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (hM : ∀ a, ν a ≤ M) :
    hw ℤ le_rfl (dualWt M ν) = genericDet ℤ r ^ (M - partialSumOfExponents ν 0) * ld3Q ν := by
  rcases r with _ | n
  · have h : genericDet ℤ 0 = 1 := by simp [genericDet]
    simp [hw, ld3Q, h]
  · have hle : ∀ s, partialSumOfExponents ν s ≤ M := by
      intro s
      unfold partialSumOfExponents
      split_ifs
      · exact hM _
      · exact Nat.zero_le _
    rw [highest_weight_prod_leading_minors, ld3Q, Finset.prod_range_succ, Finset.prod_range_succ]
    have e1 : leadingMinorPolynomial (n + 1) (n + 1) = genericDet ℤ (n + 1) := by
      unfold leadingMinorPolynomial
      rw [dif_pos le_rfl]
      exact leading_minor_full_eq_det ℤ _ rfl _ _
    have e2 : leadingMinorPolynomial (n + 1) (n + 1 - (n + 1)) = 1 := leading_minor_zero_eq_one _ _ (by omega)
    rw [e1, e2, one_pow, mul_one, partial_sequence_dual M ν n (by omega), partial_sequence_top_eq_zero, Nat.sub_zero,
      show n + 1 - (n + 1) = 0 by omega, mul_comm]
    congr 1
    rw [← Finset.prod_range_reflect
      (fun s => leadingMinorPolynomial (n + 1) (n + 1 - (s + 1)) ^ (partialSumOfExponents ν s - partialSumOfExponents ν (s + 1))) n]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    rw [partial_sequence_dual M ν t (by omega), partial_sequence_dual M ν (t + 1) (by omega),
      show n + 1 - (n - 1 - t + 1) = t + 1 by omega, show n + 1 - (t + 1) = n - 1 - t + 1 by omega,
      show n + 1 - (t + 1 + 1) = n - 1 - t by omega]
    have h3 := hle (n - 1 - t)
    have h4 := partial_sequence_antitone ν hν (n - 1 - t)
    congr 1
    omega

theorem highest_weight_dual_cofactor {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (hM : ∀ a, ν a ≤ M) :
    genericDet ℤ r ^ (∑ a, ν a) * hw ℤ le_rfl (dualWt M ν) = genericDet ℤ r ^ M * cofMap r (hw ℤ le_rfl ν) := by
  have h0 : partialSumOfExponents ν 0 ≤ M := by
    unfold partialSumOfExponents
    split_ifs
    · exact hM _
    · exact Nat.zero_le _
  rw [highest_weight_dual_weight M ν hν hM, mul_left_comm, ← cofactor_highest_weight ν hν, ← mul_assoc, ← pow_add, Nat.sub_add_cancel h0]

theorem weylDual : WeylDual := by
  intro r M ν hν hM
  rw [gen_det_eq_det]
  let L : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ) :=
    ((weyl ℤ r r le_rfl (dualWt M ν)).map (LinearMap.mulLeft ℤ (genericDet ℤ r ^ (∑ a, ν a)))).comap
      ((LinearMap.mulLeft ℤ (genericDet ℤ r ^ M)).comp (cofMap r).toLinearMap)
  have hL : ∀ x, x ∈ L ↔ ∃ g ∈ weyl ℤ r r le_rfl (dualWt M ν),
      genericDet ℤ r ^ (∑ a, ν a) * g = genericDet ℤ r ^ M * cofMap r x := fun x => Iff.rfl
  have hle : weyl ℤ r r le_rfl ν ≤ L := by
    refine weyl_le_of_stable_submodule ν hν L ((hL _).2 ⟨_, la_hw_mem ℤ le_rfl _, highest_weight_dual_cofactor M ν hν hM⟩)
      fun a b hab k f hf => ?_
    obtain ⟨g, hg, hrel⟩ := (hL f).1 hf
    have hab' : Fin.rev b ≠ Fin.rev a := fun h => hab (Fin.rev_injective h).symm
    refine (hL _).2 ⟨((-1 : ℤ) ^ k) • rowDiv ℤ (Fin.rev b) (Fin.rev a) k g,
      Submodule.smul_mem _ _ (weylRowDivStable ℤ r r le_rfl _ _ _ k g hg), ?_⟩
    have h1 := divided_power_cofactor (Fin.rev b) (Fin.rev a) hab' k f
    rw [Fin.rev_rev, Fin.rev_rev] at h1
    rw [mul_smul_comm, ← divided_power_det_pow_mul _ _ hab', hrel, divided_power_det_pow_mul _ _ hab', h1, smul_eq_C_mul]
    have hsq : ((-1 : MvPolynomial (Fin r × Fin r) ℤ)) ^ k * (-1) ^ k = 1 := by
      rw [← mul_pow]
      simp
    have hC : (C ((-1 : ℤ) ^ k) : MvPolynomial (Fin r × Fin r) ℤ) = (-1) ^ k := by simp
    rw [hC]
    linear_combination (genericDet ℤ r ^ M * cofMap r (rowDiv ℤ a b k f)) * hsq
  exact fun x hx => (hL x).1 (hle hx)

theorem weighted_homog_is_homogeneous {r : ℕ} (μ : Fin r → ℕ) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : IsWeightedHomogeneous (rowW r r) x μ) : x.IsHomogeneous (∑ a, μ a) := by
  intro d hd
  have hwt := hx hd
  have h1 : ∀ a, μ a = rowDeg d a := fun a => by rw [← ldrow_weight_rowW, hwt]
  simp only [h1, rowDeg]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  simp

theorem dual_weight_total {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (hM : ∀ a, ν a ≤ M) :
    ∑ a, dualWt M ν a + ∑ a, ν a = r * M := by
  have h0 : ∑ a, dualWt M ν a = ∑ a, (M - ν a) := Equiv.sum_comp Fin.revPerm fun a => M - ν a
  rw [h0]
  exact sum_complement_add_sum M ν hM

theorem exp_le_of_dual_exp_le (hN : NablaDual) (hW : WeylDual) (hT : DualWeight) (hC : CofCof) (l r M : ℕ) (ν μ : Fin r → ℕ)
    (e : ℕ) (hl : l.Prime) (hν : Antitone ν) (hνM : ∀ a, ν a ≤ M) (hμM : ∀ a, μ a ≤ M)
    (h : ExpLe l r (dualWt M ν) (dualWt M μ) e) : ExpLe l r ν μ e := by
  intro x hx
  by_cases h0 : x = 0
  · refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
    rw [h0, smul_zero]
    exact Submodule.zero_mem _
  obtain ⟨-, htot⟩ := dominance_of_nabla_weight r ν μ hν x hx h0
  obtain ⟨g, hg, hrel⟩ := hN r M ν hν hνM x hx.1
  have hgw := hT r M μ x g hμM hx.2 (by rw [htot]; exact hrel)
  obtain ⟨m, hm, hmem⟩ := h g ⟨hg, hgw⟩
  refine ⟨m, hm, ?_⟩
  obtain ⟨y, hy, hrel'⟩ := hW r M (dualWt M ν) ((dualWtSpec r M ν).2.2 hν) (dualWtSpec r M ν).2.1 _ hmem
  rw [(dualWtSpec r M ν).1 hνM] at hy
  have H2 := congrArg (cofMap r) hrel
  rw [map_mul, map_mul, map_pow, map_pow, (hC r).1] at H2
  have H3 := (hC r).2 (∑ a, ν a) x (htot ▸ weighted_homog_is_homogeneous μ x hx.2)
  rw [map_smul, smul_eq_C_mul] at hrel'
  have hNs := dual_weight_total M ν hνM
  have hE : genDet r ^ (∑ a, dualWt M ν a) * (genDet r ^ (r - 1)) ^ (∑ a, ν a) * genDet r ^ (∑ a, ν a) =
      genDet r ^ M * (genDet r ^ (r - 1)) ^ M * genDet r ^ ((r - 1) * ∑ a, ν a) := by
    rcases r with _ | n
    · have h1 : genDet 0 = 1 := by simp [genDet]
      simp [h1]
    · rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      simp only [Nat.add_sub_cancel]
      rw [add_mul, one_mul] at hNs
      linarith
  have hfin : (genDet r ^ (∑ a, dualWt M ν a) * (genDet r ^ (r - 1)) ^ (∑ a, ν a) * genDet r ^ (∑ a, ν a)) * y =
      (genDet r ^ (∑ a, dualWt M ν a) * (genDet r ^ (r - 1)) ^ (∑ a, ν a) * genDet r ^ (∑ a, ν a)) *
        ((m * (l : ℤ) ^ e) • x) := by
    conv_rhs => rw [hE]
    rw [smul_eq_C_mul]
    linear_combination ((genDet r ^ (r - 1)) ^ (∑ a, ν a) * genDet r ^ (∑ a, ν a)) * hrel' +
      (genDet r ^ (∑ a, ν a) * genDet r ^ M * C (m * (l : ℤ) ^ e)) * H2 +
      (genDet r ^ M * C (m * (l : ℤ) ^ e) * (genDet r ^ (r - 1)) ^ M) * H3
  have hne : genDet r ^ (∑ a, dualWt M ν a) * (genDet r ^ (r - 1)) ^ (∑ a, ν a) * genDet r ^ (∑ a, ν a) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (genericDet_pow_ne_zero r _) (pow_ne_zero _ (genericDet_pow_ne_zero r _))) (genericDet_pow_ne_zero r _)
  rw [← mul_left_cancel₀ hne hfin]
  exact hy

theorem expDualOfLattices : ExpDualOfLattices := by
  intro hN hW hT hC l r M ν μ e hl hν hνM hμM
  constructor
  · intro h
    refine exp_le_of_dual_exp_le hN hW hT hC l r M (dualWt M ν) (dualWt M μ) e hl ((dualWtSpec r M ν).2.2 hν)
      (dualWtSpec r M ν).2.1 (dualWtSpec r M μ).2.1 ?_
    rw [(dualWtSpec r M ν).1 hνM, (dualWtSpec r M μ).1 hμM]
    exact h
  · exact exp_le_of_dual_exp_le hN hW hT hC l r M ν μ e hl hν hνM hμM

theorem expDual : ExpDual := expDualOfLattices nablaDual weylDual dualWeight cofCof

theorem lastGradedOfGradedAlone : LastGradedOfGradedAlone := lastGradedOfGraded expDual

theorem dual_weight_spec : DualWtSpec := dualWtSpec
theorem block_duality : BlockDual := blockDual
theorem depth_duality : DepthDual := depthDual
theorem weight_bound' : WtBound := wtBound
theorem exponent_twist : ExpTwist := expTwist
theorem last_graded_of_graded : LastGradedOfGraded := lastGradedOfGraded
theorem nabla_duality : NablaDual := nablaDual
theorem weyl_duality : WeylDual := weylDual
theorem dual_weight' : DualWeight := dualWeight
theorem cofactor_involution : CofCof := cofCof
theorem exp_dual_of_lattices : ExpDualOfLattices := expDualOfLattices
theorem exponent_duality : ExpDual := expDual
theorem last_graded_of_graded_alone : LastGradedOfGradedAlone := lastGradedOfGradedAlone

end Formalism.CohomologicalDescent.LD
