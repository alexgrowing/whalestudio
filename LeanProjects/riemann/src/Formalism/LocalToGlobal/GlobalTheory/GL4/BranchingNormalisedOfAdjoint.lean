import Formalism.LocalToGlobal.GlobalTheory.GL4.FockSelfImEqZero

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

def dpow (n c : ℕ) : MvPolynomial (Fin n × Fin n) ℂ := lpMinor ℂ (r := n) (n := n) n le_rfl le_rfl ^ c

def lamNat {n : ℕ} (lt : DomWeight (n + 1)) : Fin n → ℕ := fun s => lt.natW s.castSucc

def sgNat {n : ℕ} (sg : DomWeight n) : Fin n → ℕ := fun i => (sg.w i).toNat

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j h
  have := lam.anti h
  unfold DomWeight.natW
  omega

theorem detShift_last {n : ℕ} (lt : DomWeight (n + 1)) (h0 : lt.w (Fin.last n) = 0) : lt.detShift = 0 := by
  unfold DomWeight.detShift
  rw [dif_pos (Nat.succ_pos n)]
  have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [this, h0]

theorem lt_nonneg {n : ℕ} (lt : DomWeight (n + 1)) (h0 : lt.w (Fin.last n) = 0) (i : Fin (n + 1)) : 0 ≤ lt.w i := by
  have := lt.anti (Fin.le_last i)
  omega

theorem lamZ_lamNat {n : ℕ} (lt : DomWeight (n + 1)) (h0 : lt.w (Fin.last n) = 0) :
    Formalism.BranchingDeterminantCap.lamZ (lamNat lt) = lt.w := by
  funext a
  unfold Formalism.BranchingDeterminantCap.lamZ lamNat DomWeight.natW
  rw [detShift_last lt h0]
  split_ifs with h
  · have hc : (Fin.castSucc ⟨a.val, h⟩ : Fin (n + 1)) = a := Fin.ext rfl
    rw [hc]
    have := lt_nonneg lt h0 a
    omega
  · have ha : a = Fin.last n := Fin.ext (by have := a.isLt; simp; omega)
    rw [ha, h0]

theorem sg_nonneg {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) (i : Fin n) : 0 ≤ sg.w i := by
  have h1 := (hI i).1
  have h2 := lt_nonneg lt h0 i.succ
  omega

theorem sgNat_cast {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) : (fun i => (sgNat sg i : ℤ)) = sg.w := by
  funext i
  unfold sgNat
  have := sg_nonneg lt sg h0 hI i
  omega

theorem interlace_nat {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) : Formalism.BranchingDeterminantCap.Interlace (Formalism.BranchingDeterminantCap.lamZ (lamNat lt)) (fun i => (sgNat sg i : ℤ)) := by
  rw [lamZ_lamNat lt h0, sgNat_cast lt sg h0 hI]
  exact fun i => ⟨(hI i).2, (hI i).1⟩

theorem detShift_nonneg {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) : 0 ≤ sg.detShift := by
  unfold DomWeight.detShift
  split_ifs with h
  · exact sg_nonneg lt sg h0 hI _
  · exact le_rfl

theorem sgNat_eq {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) : sgNat sg = fun i => sg.natW i + sg.detShift.toNat := by
  funext i
  have h1 := sg_nonneg lt sg h0 hI i
  have h2 := detShift_nonneg lt sg h0 hI
  have h3 : sg.detShift ≤ sg.w i := by
    unfold DomWeight.detShift
    rw [dif_pos (Fin.pos i)]
    exact sg.anti (by rw [Fin.le_def]; simp; omega)
  unfold sgNat DomWeight.natW
  omega

theorem twist_facts {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) :
    (∀ v ∈ weyl ℂ n n le_rfl sg.natW, dpow n sg.detShift.toNat * v ∈ weyl ℂ n n le_rfl (sgNat sg)) ∧
    dpow n sg.detShift.toNat * hw ℂ le_rfl sg.natW = hw ℂ le_rfl (sgNat sg) ∧
    (∀ v ∈ weyl ℂ n n le_rfl sg.natW,
      fockF (dpow n sg.detShift.toNat * v) (dpow n sg.detShift.toNat * v) /
          fockF (hw ℂ le_rfl (sgNat sg)) (hw ℂ le_rfl (sgNat sg)) =
        fockF v v / fockF (hw ℂ le_rfl sg.natW) (hw ℂ le_rfl sg.natW)) := by
  rw [sgNat_eq lt sg h0 hI]
  cases n with
  | zero =>
    have hc : sg.detShift.toNat = 0 := by unfold DomWeight.detShift; simp
    have hf : (fun i : Fin 0 => sg.natW i + 0) = sg.natW := funext fun i => i.elim0
    simp only [hc, hf]
    simp [dpow]
  | succ m =>
    refine ⟨fun v hv => det_mul_mem_weyl ℂ sg.natW _ v hv, ?_, fun v hv => ?_⟩
    · rw [hw_add_const, dpow, mul_comm]
    · exact fock_ratio_det_pow sg.natW (natW_anti sg) _ v hv

theorem rowAct_lpMinor_full (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    rowAct ℂ A (lpMinor ℂ (r := n) (n := n) n le_rfl le_rfl) =
      C A.det * lpMinor ℂ (r := n) (n := n) n le_rfl le_rfl := by
  unfold lpMinor
  rw [AlgHom.map_det]
  have h : (rowAct ℂ (n := n) A).mapMatrix
      (Matrix.of fun p q : Fin n => (X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) : MvPolynomial (Fin n × Fin n) ℂ)) =
      (A.map C) * Matrix.of fun p q : Fin n => (X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) : MvPolynomial (Fin n × Fin n) ℂ) := by
    ext p q
    simp [rowAct, Matrix.mul_apply]
  rw [h, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem rowAct_dpow (n c : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    rowAct ℂ A (dpow n c) = C (A.det ^ c) * dpow n c := by
  unfold dpow
  rw [map_pow, rowAct_lpMinor_full, mul_pow, C_pow]

theorem weyl_eq_dual (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    weyl ℂ r n hn ν = dualWeyl ℂ r n ν :=
  le_antisymm (Formalism.GradedWeylDivisibility.weylLeDual ℂ r n hn ν hν) (Formalism.BranchingDeterminantCap.bs_dual_le_weyl hn ν hν)

theorem dualWeyl_fd (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℂ (dualWeyl ℂ r n ν) := by
  have hle : dualWeyl ℂ r n ν ≤ homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s) := by
    intro f hf
    have h1 : f ∈ weightedHomogeneousSubmodule ℂ (colW r n) ν := (Submodule.mem_inf.mp hf).1
    rw [mem_weightedHomogeneousSubmodule] at h1
    rw [mem_homogeneousSubmodule]
    intro m hm
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_weight_sum, h1 hm]
  have : FiniteDimensional ℂ (homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s)) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  exact Submodule.finiteDimensional_of_le hle

theorem fockF_sub_left {κ : Type} (f g h : MvPolynomial κ ℂ) : fockF (f - g) h = fockF f h - fockF g h := by
  have e := fockF_add_left_g_l4 (f - g) g h
  rw [sub_add_cancel] at e
  rw [e]
  ring

theorem eq_of_fock {κ : Type} (V : Submodule ℂ (MvPolynomial κ ℂ)) (a b : MvPolynomial κ ℂ) (ha : a ∈ V) (hb : b ∈ V)
    (h : ∀ v ∈ V, fockF a v = fockF b v) : a = b := by
  by_contra hne
  have hpos := (Formalism.GradedWeylDivisibility.fockPos κ (a - b) (sub_ne_zero.mpr hne)).1
  have e : fockF (a - b) (a - b) = 0 := by
    rw [fockF_sub_left, h (a - b) (V.sub_mem ha hb), sub_self]
  rw [e, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

theorem initMinor_ne_zero {r n s : ℕ} (I : Fin s → Fin r) (hI : Function.Injective I) (hs : s ≤ n) :
    initMinor ℂ (n := n) I hs ≠ 0 := by
  classical
  intro h
  let e : Fin r × Fin n → ℂ := fun v => if h : v.2.val < s then (if I ⟨v.2.val, h⟩ = v.1 then 1 else 0) else 0
  have h1 := congrArg (eval e) h
  unfold initMinor at h1
  rw [RingHom.map_det, map_zero] at h1
  have hM : (eval e).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin r × Fin n) ℂ)) = 1 := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X, e, Fin.coe_castLE,
      Matrix.one_apply]
    rw [dif_pos q.isLt]
    by_cases hpq : p = q
    · subst hpq
      simp
    · rw [if_neg hpq, if_neg]
      intro h'
      apply hpq
      have : (⟨q.val, q.isLt⟩ : Fin s) = p := hI h'
      rw [← this]
  rw [hM, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem xiB_ne_zero {n : ℕ} (lam sg : Fin n → ℕ) : Formalism.BranchingDeterminantCap.xiB ℂ lam sg ≠ 0 := by
  unfold Formalism.BranchingDeterminantCap.xiB
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have hA : Function.Injective (Formalism.BranchingDeterminantCap.rowsA i) := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    simpa [Formalism.BranchingDeterminantCap.rowsA] using this
  have hB : Function.Injective (Formalism.BranchingDeterminantCap.rowsB i) := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    have ha := a.isLt
    have hb := b.isLt
    have hi := i.isLt
    unfold Formalism.BranchingDeterminantCap.rowsB at this
    split_ifs at this with h1 h2 h2 <;> simp only [Fin.val_last, Fin.val_mk] at this <;> omega
  exact mul_ne_zero (pow_ne_zero _ (initMinor_ne_zero _ hA _)) (pow_ne_zero _ (initMinor_ne_zero _ hB _))

theorem weylProd_eq_dimV {N : ℕ} (nu : Fin (N + 1) → ℤ) : Formalism.BranchingDeterminantCap.weylProd nu = dimV nu := by
  unfold Formalism.BranchingDeterminantCap.weylProd dimV
  rw [Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · push_cast
    ring
  · rfl

theorem extM_map_star {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.BranchingDeterminantCap.extM ℂ g).map star = Formalism.BranchingDeterminantCap.extM ℂ (g.map star) := by
  ext a b
  simp only [Matrix.map_apply, Formalism.BranchingDeterminantCap.extM, Matrix.of_apply]
  split_ifs <;> simp

theorem det_map_star {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : (g.map star).det = star g.det := by
  have h := RingHom.map_det (starRingEnd ℂ) g
  rw [starRingEnd_apply] at h
  rw [h]
  rfl

theorem detPow_eq {n : ℕ} (g : GL (Fin n) ℂ) (c : ℤ) (hc : 0 ≤ c) :
    detPow ℂ n g c = (g : Matrix (Fin n) (Fin n) ℂ).det ^ c.toNat := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hc
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, zpow_natCast, Int.toNat_natCast]

theorem sqAct_smul {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (a : ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g (a • f) = a • sqAct ℂ N lam g f := by
  unfold sqAct
  rw [map_smul, smul_comm]

theorem delSq_rowAct {n : ℕ} (sg : DomWeight n) (A : Matrix (Fin n) (Fin n) ℂ) (v : MvPolynomial (Fin n × Fin n) ℂ)
    (hv : v ∈ delSq ℂ n sg) : rowAct ℂ A v ∈ delSq ℂ n sg := by
  unfold delSq at hv ⊢
  rw [weyl_eq_dual n n le_rfl _ (natW_anti sg)] at hv ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ A v hv

theorem delSq_fd {n : ℕ} (sg : DomWeight n) : FiniteDimensional ℂ (delSq ℂ n sg) := by
  unfold delSq
  rw [weyl_eq_dual n n le_rfl _ (natW_anti sg)]
  exact dualWeyl_fd n n _

theorem adj_equiv {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg)
    (io : ↥(dualWeyl ℂ n n (sgNat sg)) →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin n) ℂ)
    (hio2 : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : ↥(dualWeyl ℂ n n (sgNat sg))),
        (f' : MvPolynomial (Fin n × Fin n) ℂ) = rowAct ℂ g (f : MvPolynomial (Fin n × Fin n) ℂ) →
          io f' = rowAct ℂ (Formalism.BranchingDeterminantCap.extM ℂ g) (io f))
    (P0 : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (hP0V : ∀ F, P0 F ∈ delSq ℂ n sg)
    (hP0 : ∀ F v (hv : v ∈ delSq ℂ n sg) (hy : dpow n sg.detShift.toNat * v ∈ dualWeyl ℂ n n (sgNat sg)),
      fockF (P0 F) v = fockF F (rename (colEmb (n + 1) n) (io ⟨_, hy⟩)))
    (g : GL (Fin n) ℂ) (H : GL (Fin (n + 1)) ℂ)
    (hH : (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = blockMat (g : Matrix (Fin n) (Fin n) ℂ))
    (F : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) :
    P0 (sqAct ℂ (n + 1) lt H F) = sqAct ℂ n sg g (P0 F) := by
  set c0 := sg.detShift.toNat with hc0
  have tw1 := (twist_facts lt sg h0 hI).1
  have hmem : ∀ v ∈ delSq ℂ n sg, dpow n c0 * v ∈ dualWeyl ℂ n n (sgNat sg) := fun v hv =>
    Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl _ (fun a b h => by
      rw [sgNat_eq lt sg h0 hI]; exact Nat.add_le_add_right (natW_anti sg h) _) (tw1 v hv)
  have hsq : sqAct ℂ n sg g (P0 F) ∈ delSq ℂ n sg := by
    unfold sqAct
    exact Submodule.smul_mem _ _ (delSq_rowAct sg _ _ (hP0V F))
  refine eq_of_fock _ _ _ (hP0V _) hsq fun v hv => ?_
  set gb : Matrix (Fin n) (Fin n) ℂ := (g : Matrix (Fin n) (Fin n) ℂ).map star with hgb
  have hv' : rowAct ℂ gb v ∈ delSq ℂ n sg := delSq_rowAct sg gb v hv

  rw [hP0 _ v hv (hmem v hv), sqAct_of_last_zero ℂ lt h0 H F, Formalism.GradedWeylDivisibility.fockRowAdj]
  have hHc : (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).transpose.conjTranspose = Formalism.BranchingDeterminantCap.extM ℂ gb := by
    rw [Matrix.conjTranspose, Matrix.transpose_transpose, hH, blockMat_eq_extM, extM_map_star]
  rw [hHc, rowAct_rename]
  have hy' : rowAct ℂ gb (dpow n c0 * v) = (gb.det ^ c0) • (dpow n c0 * rowAct ℂ gb v) := by
    rw [map_mul, rowAct_dpow, smul_eq_C_mul, mul_assoc]
  have hmem' : rowAct ℂ gb (dpow n c0 * v) ∈ dualWeyl ℂ n n (sgNat sg) :=
    Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ gb _ (hmem v hv)
  rw [← hio2 gb ⟨_, hmem v hv⟩ ⟨_, hmem'⟩ rfl]
  have hsub : (⟨_, hmem'⟩ : ↥(dualWeyl ℂ n n (sgNat sg))) = (gb.det ^ c0) • ⟨_, hmem _ hv'⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_smul]
    exact hy'
  rw [hsub, map_smul, map_smul, fockF_smul_right_eq_star_mul, ← hP0 F _ hv' (hmem _ hv')]

  unfold sqAct
  rw [fockF_smul_left', Formalism.GradedWeylDivisibility.fockRowAdj]
  have hgc : ((g : Matrix (Fin n) (Fin n) ℂ).transpose).conjTranspose = gb := by
    rw [Matrix.conjTranspose, Matrix.transpose_transpose]
  rw [hgc, detPow_eq g _ (detShift_nonneg lt sg h0 hI), ← hc0, hgb, det_map_star, star_pow, star_star]

theorem scaleMat_conjTranspose (n : ℕ) (T : ℝ) : (scaleMat n T).conjTranspose = scaleMat n T := by
  unfold scaleMat
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem scale_cancel (n d T : ℕ) (hT : 0 < T) (x : MvPolynomial (Fin (n + 1) × Fin n) ℂ)
    (hx : ∀ m ∈ x.support, rowDeg m (Fin.last n) = d) :
    rowAct ℂ (scaleMat n T) (rowAct ℂ (Formalism.BranchingDeterminantCap.zScale n (1 / Real.sqrt T)) x) = x := by
  rw [(Formalism.BranchingDeterminantCap.branch_scale_formula n n d (1 / Real.sqrt T) x hx).1, map_smul, scaleMat_eq_zScale,
    (Formalism.BranchingDeterminantCap.branch_scale_formula n n d (Real.sqrt T) x hx).1, smul_smul, ← mul_pow]
  have hs : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have : ((1 / Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ hs.ne', Complex.ofReal_one]
  rw [this, one_pow, one_smul]

theorem fock_hw_pos {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : 0 < (fockF (hw ℂ hn ν) (hw ℂ hn ν)).re :=
  (Formalism.GradedWeylDivisibility.fockPos _ _ (Formalism.GradedWeylDivisibility.hwNe ℂ r n hn ν)).1

theorem adj_norm {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) (T : ℕ) (hT : 0 < T) (G : GL (Fin (n + 1)) ℂ)
    (hG : (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T)
    (io : ↥(dualWeyl ℂ n n (sgNat sg)) →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin n) ℂ)
    (hio2 : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : ↥(dualWeyl ℂ n n (sgNat sg))),
        (f' : MvPolynomial (Fin n × Fin n) ℂ) = rowAct ℂ g (f : MvPolynomial (Fin n × Fin n) ℂ) →
          io f' = rowAct ℂ (Formalism.BranchingDeterminantCap.extM ℂ g) (io f))
    (hio3 : ∀ h : ↥(dualWeyl ℂ n n (sgNat sg)), (h : MvPolynomial (Fin n × Fin n) ℂ) = hw ℂ le_rfl (sgNat sg) →
        io h = ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ (lamNat lt)) (fun i => (sgNat sg i : ℤ)) : ℤ) : ℂ) •
          Formalism.BranchingDeterminantCap.xiB ℂ (lamNat lt) (sgNat sg))
    (hio4 : ∀ f, ∀ m ∈ (io f).support, rowDeg m (Fin.last n) = ∑ i, (lamNat lt i - sgNat sg i))
    (P0 : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (hP0V : ∀ F, P0 F ∈ delSq ℂ n sg)
    (hP0 : ∀ F v (hv : v ∈ delSq ℂ n sg) (hy : dpow n sg.detShift.toNat * v ∈ dualWeyl ℂ n n (sgNat sg)),
      fockF (P0 F) v = fockF F (rename (colEmb (n + 1) n) (io ⟨_, hy⟩)))
    (F : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) :
    (fockF (P0 F) (P0 F)).re ≤
      ((1 / Real.sqrt T) ^ (2 * ∑ i, (lamNat lt i - sgNat sg i)) *
        ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ (lamNat lt)) (fun i => (sgNat sg i : ℤ)) : ℤ) : ℝ) ^ 2 *
        (fockF (Formalism.BranchingDeterminantCap.xiB ℂ (lamNat lt) (sgNat sg)) (Formalism.BranchingDeterminantCap.xiB ℂ (lamNat lt) (sgNat sg))).re /
        (fockF (hw ℂ le_rfl sg.natW) (hw ℂ le_rfl sg.natW)).re) *
      (fockF (sqAct ℂ (n + 1) lt G F) (sqAct ℂ (n + 1) lt G F)).re := by
  set d := ∑ i, (lamNat lt i - sgNat sg i) with hd
  set t : ℝ := 1 / Real.sqrt T with ht
  set c := Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ (lamNat lt)) (fun i => (sgNat sg i : ℤ)) with hc
  set ξ := Formalism.BranchingDeterminantCap.xiB ℂ (lamNat lt) (sgNat sg) with hξ
  obtain ⟨tw1, -, tw3⟩ := twist_facts lt sg h0 hI
  have hmem : dpow n sg.detShift.toNat * P0 F ∈ dualWeyl ℂ n n (sgNat sg) :=
    Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl _ (fun a b h => by
      rw [sgNat_eq lt sg h0 hI]; exact Nat.add_le_add_right (natW_anti sg h) _) (tw1 _ (hP0V F))
  set y : ↥(dualWeyl ℂ n n (sgNat sg)) := ⟨_, hmem⟩ with hy
  have hNT := (Formalism.BranchingDeterminantCap.branch_norm_trace n (lamNat lt) (sgNat sg) t (interlace_nat lt sg h0 hI) io hio2 hio3 hio4).2 y
  have hrat := tw3 (P0 F) (hP0V F)
  set Z := rowAct ℂ (Formalism.BranchingDeterminantCap.zScale n t) (io y) with hZ
  set J := rename (colEmb (n + 1) n) Z with hJ

  have hr : ∀ {σ : Type} (f : MvPolynomial σ ℂ), fockF f f = (((fockF f f).re : ℝ) : ℂ) :=
    fun f => fock_self_eq_re f
  set a := (fockF Z Z).re
  set hn := (fockF (hw ℂ le_rfl (sgNat sg)) (hw ℂ le_rfl (sgNat sg))).re
  set x := (fockF ξ ξ).re
  set yy := (fockF (y : MvPolynomial (Fin n × Fin n) ℂ) y).re
  set p := (fockF (P0 F) (P0 F)).re
  set hs := (fockF (hw ℂ le_rfl sg.natW) (hw ℂ le_rfl sg.natW)).re
  have hn0 : 0 < hn := fock_hw_pos le_rfl _
  have hs0 : 0 < hs := fock_hw_pos le_rfl _
  have e1 : a * hn = t ^ (2 * d) * (c : ℝ) ^ 2 * x * yy := by
    rw [hr Z, hr (hw ℂ le_rfl (sgNat sg)), hr ξ, hr (y : MvPolynomial (Fin n × Fin n) ℂ)] at hNT
    exact_mod_cast hNT
  have e2 : yy * hs = p * hn := by
    rw [hr (dpow n sg.detShift.toNat * P0 F), hr (hw ℂ le_rfl (sgNat sg)), hr (P0 F),
      hr (hw ℂ le_rfl sg.natW)] at hrat
    have h' : yy / hn = p / hs := by exact_mod_cast hrat
    rw [div_eq_div_iff hn0.ne' hs0.ne'] at h'
    exact h'
  have hx0 : 0 ≤ x := fock_self_re_nonneg ξ
  have hK : 0 ≤ t ^ (2 * d) * (c : ℝ) ^ 2 * x / hs := by
    have : 0 ≤ t := by rw [ht]; positivity
    positivity
  apply fock_adjoint_bound (P0 F) (sqAct ℂ (n + 1) lt G F) J _ hK
  · rw [hP0 F (P0 F) (hP0V F) hmem, sqAct_of_last_zero ℂ lt h0 G F, hG, scaleMat_transpose, Formalism.GradedWeylDivisibility.fockRowAdj,
      scaleMat_conjTranspose, hJ, rowAct_rename, hZ, scale_cancel n d T hT _ (hio4 y)]
  · rw [hJ, fockF_rename _ (colEmb_inj _ _)]
    apply le_of_eq
    have e3 : (a * hs) * hn = (t ^ (2 * d) * (c : ℝ) ^ 2 * x * p) * hn := by
      linear_combination hs * e1 + (t ^ (2 * d) * (c : ℝ) ^ 2 * x) * e2
    have e4 := mul_right_cancel₀ hn0.ne' e3
    field_simp
    linarith

theorem adj_ne {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg)
    (io : ↥(dualWeyl ℂ n n (sgNat sg)) →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin n) ℂ)
    (hio1 : ∀ f, io f ∈ dualWeyl ℂ (n + 1) n (lamNat lt))
    (hio3 : ∀ h : ↥(dualWeyl ℂ n n (sgNat sg)), (h : MvPolynomial (Fin n × Fin n) ℂ) = hw ℂ le_rfl (sgNat sg) →
        io h = ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ (lamNat lt)) (fun i => (sgNat sg i : ℤ)) : ℤ) : ℂ) •
          Formalism.BranchingDeterminantCap.xiB ℂ (lamNat lt) (sgNat sg))
    (P0 : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (hP0 : ∀ F v (hv : v ∈ delSq ℂ n sg) (hy : dpow n sg.detShift.toNat * v ∈ dualWeyl ℂ n n (sgNat sg)),
      fockF (P0 F) v = fockF F (rename (colEmb (n + 1) n) (io ⟨_, hy⟩))) :
    ∃ F ∈ delSq ℂ (n + 1) lt, P0 F ≠ 0 := by
  set c := Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ (lamNat lt)) (fun i => (sgNat sg i : ℤ)) with hc
  set ξ := Formalism.BranchingDeterminantCap.xiB ℂ (lamNat lt) (sgNat sg) with hξ
  obtain ⟨-, tw2, -⟩ := twist_facts lt sg h0 hI
  have hc0 : (c : ℂ) ≠ 0 := by
    have := (Formalism.BranchingDeterminantCap.capacity_constant_bound n _ _ (interlace_nat lt sg h0 hI)).1
    exact_mod_cast this
  have hsgN : Antitone (sgNat sg) := by
    rw [sgNat_eq lt sg h0 hI]
    exact fun a b h => Nat.add_le_add_right (natW_anti sg h) _
  have hhw : hw ℂ le_rfl (sgNat sg) ∈ dualWeyl ℂ n n (sgNat sg) :=
    Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl _ hsgN (Submodule.subset_span ⟨[], rfl⟩)
  have hio_hw := hio3 ⟨_, hhw⟩ rfl
  have hξmem : ξ ∈ dualWeyl ℂ (n + 1) n (lamNat lt) := by
    have h1 := hio1 ⟨_, hhw⟩
    rw [hio_hw] at h1
    have h2 := (dualWeyl ℂ (n + 1) n (lamNat lt)).smul_mem (c : ℂ)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h2
  have hlam : Antitone (lamNat lt) := fun a b h => natW_anti lt (Fin.castSucc_le_castSucc_iff.mpr h)
  have hξw : ξ ∈ weyl ℂ (n + 1) n (Nat.le_succ n) (lamNat lt) := Formalism.BranchingDeterminantCap.bs_dual_le_weyl _ _ hlam hξmem
  refine ⟨rename (colEmb (n + 1) n) ξ, ?_, fun hP => ?_⟩
  · rw [delSq_eq_map]
    exact Submodule.mem_map_of_mem hξw
  · have hv : hw ℂ le_rfl sg.natW ∈ delSq ℂ n sg := Submodule.subset_span ⟨[], rfl⟩
    have hy : dpow n sg.detShift.toNat * hw ℂ le_rfl sg.natW ∈ dualWeyl ℂ n n (sgNat sg) := by
      rw [tw2]; exact hhw
    have h1 := hP0 (rename (colEmb (n + 1) n) ξ) _ hv hy
    have hsub : (⟨_, hy⟩ : ↥(dualWeyl ℂ n n (sgNat sg))) = ⟨_, hhw⟩ := Subtype.ext tw2
    rw [hP, hsub, hio_hw, map_smul, fockF_smul_right_eq_star_mul, fockF_rename _ (colEmb_inj _ _)] at h1
    have h2 : fockF (0 : MvPolynomial (Fin n × Fin n) ℂ) (hw ℂ le_rfl sg.natW) = 0 := by
      rw [← fockLin_apply, map_zero]
    rw [h2] at h1
    have hpos := (Formalism.GradedWeylDivisibility.fockPos _ ξ (xiB_ne_zero _ _)).1
    have h3 : fockF ξ ξ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hpos; exact lt_irrefl _ hpos
    exact mul_ne_zero (star_ne_zero.mpr hc0) h3 h1.symm

def AdjointIntegrality : Prop :=
  ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n), lt.w (Fin.last n) = 0 → Interlace lt sg →
  ∀ io : ↥(dualWeyl ℂ n n (sgNat sg)) →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin n) ℂ,
    (∀ f, io f ∈ dualWeyl ℂ (n + 1) n (lamNat lt)) →
    (∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : ↥(dualWeyl ℂ n n (sgNat sg))),
        (f' : MvPolynomial (Fin n × Fin n) ℂ) = rowAct ℂ g (f : MvPolynomial (Fin n × Fin n) ℂ) →
          io f' = rowAct ℂ (Formalism.BranchingDeterminantCap.extM ℂ g) (io f)) →
    (∀ h : ↥(dualWeyl ℂ n n (sgNat sg)), (h : MvPolynomial (Fin n × Fin n) ℂ) = hw ℂ le_rfl (sgNat sg) →
        io h = ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ (lamNat lt)) (fun i => (sgNat sg i : ℤ)) : ℤ) : ℂ) •
          Formalism.BranchingDeterminantCap.xiB ℂ (lamNat lt) (sgNat sg)) →
    (∀ f, ∀ m ∈ (io f).support, rowDeg m (Fin.last n) = ∑ i, (lamNat lt i - sgNat sg i)) →
    ∀ P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ,
      (∀ F, P F ∈ delSq ℂ n sg) →
      (∀ F v (hv : v ∈ delSq ℂ n sg) (hy : dpow n sg.detShift.toNat * v ∈ dualWeyl ℂ n n (sgNat sg)),
        normFock sg (P F) v = normFock lt F (rename (colEmb (n + 1) n) (io ⟨_, hy⟩))) →
      ∀ F ∈ delSq ℤ (n + 1) lt, ∃ g ∈ delSq ℤ n sg,
        P (MvPolynomial.map (Int.castRingHom ℂ) F) = MvPolynomial.map (Int.castRingHom ℂ) g

theorem branchingDegree_eq_sum {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) : degP lt sg = ((∑ i, (lamNat lt i - sgNat sg i) : ℕ) : ℤ) := by
  unfold degP
  rw [Fin.sum_univ_castSucc (f := lt.w), h0, add_zero, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := (hI i).2
  have h2 := sg_nonneg lt sg h0 hI i
  have h3 := lt_nonneg lt h0 i.castSucc
  unfold lamNat sgNat DomWeight.natW
  rw [detShift_last lt h0]
  omega

theorem exp_eq_pow (T d : ℕ) (hT : 0 < T) :
    Real.exp (-((d : ℤ) : ℝ) * Real.log T) = (1 / Real.sqrt T) ^ (2 * d) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  rw [pow_mul, div_pow, one_pow, Real.sq_sqrt hT'.le, neg_mul, Real.exp_neg, Int.cast_natCast,
    Real.exp_nat_mul, Real.exp_log hT', one_div_pow, one_div]

theorem branching_normalised_of_adjoint (hInt : AdjointIntegrality) : BranchingIntegralNormalised := by
  intro n lt sg h0 hI T hT G hG
  have hInter := interlace_nat lt sg h0 hI
  obtain ⟨io, hio1, hio2, hio3, hio4⟩ := Formalism.BranchingDeterminantCap.branch_map_formula ℂ n (lamNat lt) (sgNat sg) hInter
  set V := delSq ℂ n sg with hV
  obtain ⟨tw1, -, -⟩ := twist_facts lt sg h0 hI
  have hmem : ∀ v ∈ V, dpow n sg.detShift.toNat * v ∈ dualWeyl ℂ n n (sgNat sg) := fun v hv =>
    Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl _ (fun a b h => by
      rw [sgNat_eq lt sg h0 hI]; exact Nat.add_le_add_right (natW_anti sg h) _) (tw1 v hv)
  haveI : FiniteDimensional ℂ V := delSq_fd sg
  let tw : V →ₗ[ℂ] ↥(dualWeyl ℂ n n (sgNat sg)) :=
    LinearMap.codRestrict _ ((LinearMap.mulLeft ℂ (dpow n sg.detShift.toNat)).comp V.subtype) (fun v => hmem v v.2)
  let jl : V →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ :=
    (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) ℂ →ₐ[ℂ] _).toLinearMap ∘ₗ io ∘ₗ tw
  obtain ⟨P0, hP0V, hP0'⟩ := fock_adjoint_exists V jl
  have hP0 : ∀ F v (hv : v ∈ delSq ℂ n sg) (hy : dpow n sg.detShift.toNat * v ∈ dualWeyl ℂ n n (sgNat sg)),
      fockF (P0 F) v = fockF F (rename (colEmb (n + 1) n) (io ⟨_, hy⟩)) := fun F v hv hy => hP0' F ⟨v, hv⟩

  have hr : ∀ {σ : Type} (f : MvPolynomial σ ℂ), fockF f f = (((fockF f f).re : ℝ) : ℂ) :=
    fun f => fock_self_eq_re f
  set hsr := (fockF (extremal ℂ n sg) (extremal ℂ n sg)).re with hhsr
  set hlr := (fockF (extremal ℂ (n + 1) lt) (extremal ℂ (n + 1) lt)).re with hhlr
  have hs0 : 0 < hsr := fock_hw_pos le_rfl _
  have hl0 : 0 < hlr := fock_hw_pos le_rfl _
  have hlr_eq : hlr = (fockF (hw ℂ (Nat.le_succ n) (lamNat lt)) (hw ℂ (Nat.le_succ n) (lamNat lt))).re := by
    rw [hhlr]
    unfold extremal
    rw [hw_rename ℂ lt.natW (natW_last lt), fockF_rename _ (colEmb_inj _ _)]
    rfl
  set α : ℂ := ((hsr / hlr : ℝ) : ℂ) with hα
  have hsC : fockF (extremal ℂ n sg) (extremal ℂ n sg) = (hsr : ℂ) := hr _
  have hlC : fockF (extremal ℂ (n + 1) lt) (extremal ℂ (n + 1) lt) = (hlr : ℂ) := hr _
  have hsne : (hsr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have hlne : (hlr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl0.ne'
  have hadjN : ∀ F v (hv : v ∈ delSq ℂ n sg) (hy : dpow n sg.detShift.toNat * v ∈ dualWeyl ℂ n n (sgNat sg)),
      normFock sg ((α • P0) F) v = normFock lt F (rename (colEmb (n + 1) n) (io ⟨_, hy⟩)) := by
    intro F v hv hy
    unfold normFock
    rw [LinearMap.smul_apply, fockF_smul_left', hP0 F v hv hy, hsC, hlC, hα, Complex.ofReal_div]
    field_simp
  refine ⟨α • P0, fun f _ => Submodule.smul_mem _ _ (hP0V f), ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨F, hF, hne⟩ := adj_ne lt sg h0 hI io hio1 hio3 P0 hP0
    refine ⟨F, hF, ?_⟩
    rw [LinearMap.smul_apply]
    exact smul_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hs0 hl0).ne') hne
  ·
    exact hInt n lt sg h0 hI io hio1 hio2 hio3 hio4 (α • P0) (fun f => Submodule.smul_mem _ _ (hP0V f)) hadjN
  ·
    intro g H hH f _
    rw [LinearMap.smul_apply, LinearMap.smul_apply, adj_equiv lt sg h0 hI io hio2 P0 hP0V hP0 g H hH f,
      sqAct_smul]
  ·
    intro f _
    have hb := adj_norm lt sg h0 hI T hT G hG io hio2 hio3 hio4 P0 hP0V hP0 f
    have hxi := Formalism.BranchingDeterminantCap.xi_norm_bound n (lamNat lt) (sgNat sg) hInter
    rw [weylProd_eq_dimV, lamZ_lamNat lt h0, ← hlr_eq] at hxi
    set p := (fockF (P0 f) (P0 f)).re
    set s := (fockF (sqAct ℂ (n + 1) lt G f) (sqAct ℂ (n + 1) lt G f)).re
    set x := (fockF (Formalism.BranchingDeterminantCap.xiB ℂ (lamNat lt) (sgNat sg)) (Formalism.BranchingDeterminantCap.xiB ℂ (lamNat lt) (sgNat sg))).re
    set t2 := (1 / Real.sqrt T) ^ (2 * ∑ i, (lamNat lt i - sgNat sg i))
    have hcc : Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ (lamNat lt)) (fun i => (sgNat sg i : ℤ)) = Formalism.BranchingDeterminantCap.cCap lt.w sg.w := by
      rw [lamZ_lamNat lt h0, sgNat_cast lt sg h0 hI]
    rw [hcc] at hb
    set cc := (((Formalism.BranchingDeterminantCap.cCap lt.w sg.w : ℤ) : ℝ)) ^ 2
    have hs_eq : (fockF (hw ℂ le_rfl sg.natW) (hw ℂ le_rfl sg.natW)).re = hsr := rfl
    rw [hs_eq] at hb

    have hL : (normFock sg ((α • P0) f) ((α • P0) f)).re = (hsr / hlr) ^ 2 * p / hsr := by
      unfold normFock
      rw [LinearMap.smul_apply, fockF_smul_left', fockF_smul_right_eq_star_mul, hr (P0 f), hsC, hα, Complex.star_def,
        Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
      ring

    have hR : normTil lt G f = s / hlr := by
      unfold normTil normFock
      rw [hr (sqAct ℂ (n + 1) lt G f), hlC, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hL, hR, branchingDegree_eq_sum lt sg h0 hI, exp_eq_pow T _ hT]
    have hx0 : 0 ≤ x := fock_self_re_nonneg _
    have hs0' : 0 ≤ s := fock_self_re_nonneg _
    have ht0 : 0 ≤ t2 := by positivity
    have hcc0 : 0 ≤ cc := by positivity
    have hdim := dimV_pos lt

    have h1 : (hsr / hlr) ^ 2 * p / hsr ≤ t2 * cc * x * s / hlr ^ 2 := by
      rw [div_le_div_iff₀ hs0 (by positivity)]
      have := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ (hsr / hlr) ^ 2 * hlr ^ 2)
      calc (hsr / hlr) ^ 2 * p * hlr ^ 2 = hsr ^ 2 * p := by field_simp
        _ ≤ hsr ^ 2 * (t2 * cc * x / hsr * s) := by
            apply mul_le_mul_of_nonneg_left hb (by positivity)
        _ = t2 * cc * x * s * hsr := by field_simp
    have h2 : t2 * cc * x * s / hlr ^ 2 ≤ t2 * (cc * dimV lt.w) * (s / hlr) := by
      rw [div_le_iff₀ (by positivity)]
      have : t2 * cc * x * s ≤ t2 * cc * (dimV lt.w * hlr) * s := by
        apply mul_le_mul_of_nonneg_right _ hs0'
        exact mul_le_mul_of_nonneg_left hxi (by positivity)
      calc t2 * cc * x * s ≤ t2 * cc * (dimV lt.w * hlr) * s := this
        _ = t2 * (cc * dimV lt.w) * (s / hlr) * hlr ^ 2 := by field_simp
    exact h1.trans h2

theorem branching_link_of_adjoint (h : AdjointIntegrality) : Link3 := branching_link_of_normalised (branching_normalised_of_adjoint h)

theorem branching_family_of_adjoint (h : AdjointIntegrality) : Link3F := branching_link_family_normalised (branching_normalised_of_adjoint h)

theorem adjInt_hyps_inhabited (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) :
    ∃ io : ↥(dualWeyl ℂ n n (sgNat sg)) →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin n) ℂ,
    (∀ f, io f ∈ dualWeyl ℂ (n + 1) n (lamNat lt)) ∧
    (∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : ↥(dualWeyl ℂ n n (sgNat sg))),
        (f' : MvPolynomial (Fin n × Fin n) ℂ) = rowAct ℂ g (f : MvPolynomial (Fin n × Fin n) ℂ) →
          io f' = rowAct ℂ (Formalism.BranchingDeterminantCap.extM ℂ g) (io f)) ∧
    (∀ h : ↥(dualWeyl ℂ n n (sgNat sg)), (h : MvPolynomial (Fin n × Fin n) ℂ) = hw ℂ le_rfl (sgNat sg) →
        io h = ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ (lamNat lt)) (fun i => (sgNat sg i : ℤ)) : ℤ) : ℂ) •
          Formalism.BranchingDeterminantCap.xiB ℂ (lamNat lt) (sgNat sg)) ∧
    (∀ f, ∀ m ∈ (io f).support, rowDeg m (Fin.last n) = ∑ i, (lamNat lt i - sgNat sg i)) ∧
    ∃ P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ,
      (∀ F, P F ∈ delSq ℂ n sg) ∧
      (∀ F v (hv : v ∈ delSq ℂ n sg) (hy : dpow n sg.detShift.toNat * v ∈ dualWeyl ℂ n n (sgNat sg)),
        normFock sg (P F) v = normFock lt F (rename (colEmb (n + 1) n) (io ⟨_, hy⟩))) ∧
      (∃ F ∈ delSq ℂ (n + 1) lt, P F ≠ 0) := by
  have hInter := interlace_nat lt sg h0 hI
  obtain ⟨io, hio1, hio2, hio3, hio4⟩ := Formalism.BranchingDeterminantCap.branch_map_formula ℂ n (lamNat lt) (sgNat sg) hInter
  set V := delSq ℂ n sg with hV
  obtain ⟨tw1, -, -⟩ := twist_facts lt sg h0 hI
  have hmem : ∀ v ∈ V, dpow n sg.detShift.toNat * v ∈ dualWeyl ℂ n n (sgNat sg) := fun v hv =>
    Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl _ (fun a b h => by
      rw [sgNat_eq lt sg h0 hI]; exact Nat.add_le_add_right (natW_anti sg h) _) (tw1 v hv)
  haveI : FiniteDimensional ℂ V := delSq_fd sg
  let tw : V →ₗ[ℂ] ↥(dualWeyl ℂ n n (sgNat sg)) :=
    LinearMap.codRestrict _ ((LinearMap.mulLeft ℂ (dpow n sg.detShift.toNat)).comp V.subtype) (fun v => hmem v v.2)
  let jl : V →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ :=
    (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) ℂ →ₐ[ℂ] _).toLinearMap ∘ₗ io ∘ₗ tw
  obtain ⟨P0, hP0V, hP0'⟩ := fock_adjoint_exists V jl
  have hP0 : ∀ F v (hv : v ∈ delSq ℂ n sg) (hy : dpow n sg.detShift.toNat * v ∈ dualWeyl ℂ n n (sgNat sg)),
      fockF (P0 F) v = fockF F (rename (colEmb (n + 1) n) (io ⟨_, hy⟩)) := fun F v hv hy => hP0' F ⟨v, hv⟩
  have hr : ∀ {σ : Type} (f : MvPolynomial σ ℂ), fockF f f = (((fockF f f).re : ℝ) : ℂ) :=
    fun f => fock_self_eq_re f
  set hsr := (fockF (extremal ℂ n sg) (extremal ℂ n sg)).re with hhsr
  set hlr := (fockF (extremal ℂ (n + 1) lt) (extremal ℂ (n + 1) lt)).re with hhlr
  have hs0 : 0 < hsr := fock_hw_pos le_rfl _
  have hl0 : 0 < hlr := fock_hw_pos le_rfl _
  set α : ℂ := ((hsr / hlr : ℝ) : ℂ) with hα
  have hsC : fockF (extremal ℂ n sg) (extremal ℂ n sg) = (hsr : ℂ) := hr _
  have hlC : fockF (extremal ℂ (n + 1) lt) (extremal ℂ (n + 1) lt) = (hlr : ℂ) := hr _
  have hsne : (hsr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have hlne : (hlr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl0.ne'
  refine ⟨io, hio1, hio2, hio3, hio4, α • P0, fun f => Submodule.smul_mem _ _ (hP0V f), ?_, ?_⟩
  · intro F v hv hy
    unfold normFock
    rw [LinearMap.smul_apply, fockF_smul_left', hP0 F v hv hy, hsC, hlC, hα, Complex.ofReal_div]
    field_simp
  · obtain ⟨F, hF, hne⟩ := adj_ne lt sg h0 hI io hio1 hio3 P0 hP0
    refine ⟨F, hF, ?_⟩
    rw [LinearMap.smul_apply]
    exact smul_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hs0 hl0).ne') hne

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
