import Formalism.LocalToGlobal.GlobalTheory.GL4.ApplyWordMemDual
import Formalism.LocalToGlobal.GlobalTheory.GL4.PNabla

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

def elemMat (R : Type) [CommRing R] {r : ℕ} (a b : Fin r) (t : R) : Matrix (Fin r) (Fin r) R :=
  fun c d => (if c = d then 1 else 0) + (if c = b ∧ d = a then t else 0)

theorem eval_rowGen_gen (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (t : R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    Polynomial.eval (C t) (rowGen R a b f) = rowAct R (elemMat R a b t) f := by
  have : (Polynomial.evalRingHom (C t)).comp (rowGen R (n := n) a b).toRingHom =
      (rowAct R (n := n) (elemMat R a b t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, rowAct]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowGen, rowAct,
        aeval_X, Polynomial.coe_evalRingHom, elemMat, map_add, add_mul, Finset.sum_add_distrib]
      congr 1
      · simp
      · by_cases hb : v.1 = b
        · simp only [hb, true_and, if_true, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
          rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp), if_pos rfl, mul_comm]
        · simp [hb]
  exact congrArg (fun φ => φ f) this

theorem eval_C_gen (R : Type) [CommRing R] {σ : Type} (P : Polynomial (MvPolynomial σ R)) (N : ℕ)
    (hN : P.natDegree < N) (t : R) :
    Polynomial.eval (C t) P = ∑ i ∈ Finset.range N, C (t ^ i) * P.coeff i := by
  rw [Polynomial.eval_eq_sum_range' hN]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, mul_comm]

theorem extM_elemMat (R : Type) [CommRing R] {n : ℕ} (a b : Fin n) (t : R) :
    Formalism.BranchingDeterminantCap.extM R (elemMat R a b t) = elemMat R a.castSucc b.castSucc t := by
  ext c d
  unfold Formalism.BranchingDeterminantCap.extM elemMat
  simp only [Matrix.of_apply]
  by_cases h : c.val < n ∧ d.val < n
  · rw [dif_pos h]
    congr 1
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
  · rw [dif_neg h]
    have : ¬ (c = b.castSucc ∧ d = a.castSucc) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨b.isLt, a.isLt⟩
    rw [if_neg this, add_zero]

def RowNat (R : Type) [CommRing R] {n : ℕ} (σ : Fin n → ℕ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) : Prop :=
  ∀ (g : Matrix (Fin n) (Fin n) R) (f f' : ↥(dualWeyl R n n σ)),
    (f' : MvPolynomial (Fin n × Fin n) R) = rowAct R g (f : MvPolynomial (Fin n × Fin n) R) →
      io f' = rowAct R (Formalism.BranchingDeterminantCap.extM R g) (io f)

theorem io_rowDiv_gen (R : Type) [CommRing R] [IsDomain R] [Infinite R] {n : ℕ} (σ : Fin n → ℕ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) (hio2 : RowNat R σ io)
    (a b : Fin n) (k : ℕ) (f : ↥(dualWeyl R n n σ))
    (hk : rowDiv R a b k (f : MvPolynomial (Fin n × Fin n) R) ∈ dualWeyl R n n σ) :
    io ⟨_, hk⟩ = rowDiv R a.castSucc b.castSucc k (io f) := by
  have hmem : ∀ i, rowDiv R a b i (f : MvPolynomial (Fin n × Fin n) R) ∈ dualWeyl R n n σ :=
    fun i => Formalism.GradedWeylDivisibility.dualWeylModuleRowDividedPowerStable R n n σ a b i _ f.2
  set N := (rowGen R a b (f : MvPolynomial (Fin n × Fin n) R)).natDegree +
    (rowGen R a.castSucc b.castSucc (io f)).natDegree + k + 1 with hN
  have h1 : (rowGen R a b (f : MvPolynomial (Fin n × Fin n) R)).natDegree < N := by omega
  have h2 : (rowGen R a.castSucc b.castSucc (io f)).natDegree < N := by omega
  have hk' : k ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have key : ∀ t : R, ∑ i ∈ Finset.range N, t ^ i • io ⟨_, hmem i⟩ =
      ∑ i ∈ Finset.range N, t ^ i • rowDiv R a.castSucc b.castSucc i (io f) := by
    intro t
    have hrow : rowAct R (elemMat R a b t) (f : MvPolynomial (Fin n × Fin n) R) ∈ dualWeyl R n n σ :=
      Formalism.GradedWeylDivisibility.dualWeylRowStable R n n σ _ _ f.2
    have e := hio2 (elemMat R a b t) f ⟨_, hrow⟩ rfl
    have e2 : rowAct R (elemMat R a.castSucc b.castSucc t) (io f) =
        ∑ i ∈ Finset.range N, C (t ^ i) * (rowGen R a.castSucc b.castSucc (io f)).coeff i := by
      rw [← eval_rowGen_gen, eval_C_gen R _ N h2]
    rw [extM_elemMat, e2] at e
    have hsub : (⟨_, hrow⟩ : ↥(dualWeyl R n n σ)) = ∑ i ∈ Finset.range N, t ^ i • ⟨_, hmem i⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← eval_rowGen_gen, eval_C_gen R _ N h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_C_mul]
      rfl
    rw [hsub, map_sum] at e
    simp only [map_smul] at e
    rw [e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul]
    rfl
  ext m
  set P : Polynomial R := ∑ i ∈ Finset.range N, Polynomial.monomial i (coeff m (io ⟨_, hmem i⟩)) with hP
  set Q : Polynomial R := ∑ i ∈ Finset.range N,
    Polynomial.monomial i (coeff m (rowDiv R a.castSucc b.castSucc i (io f))) with hQ
  have hPQ : P = Q := by
    apply Polynomial.funext
    intro t
    simp only [hP, hQ, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    have := congrArg (coeff m) (key t)
    simp only [coeff_sum, coeff_smul, smul_eq_mul] at this
    simpa [mul_comm] using this
  have := congrArg (fun p => Polynomial.coeff p k) hPQ
  simp only [hP, hQ, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', if_pos hk'] at this
  exact this

theorem applyWord_mem_dual_gen (R : Type) [CommRing R] {n : ℕ} (σ : Fin n → ℕ) (w : List (Fin n × Fin n × ℕ))
    (f : MvPolynomial (Fin n × Fin n) R) (hf : f ∈ dualWeyl R n n σ) : applyWord R w f ∈ dualWeyl R n n σ := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact Formalism.GradedWeylDivisibility.dualWeylModuleRowDividedPowerStable R n n σ _ _ _ _ ih

theorem io_applyWord_gen (R : Type) [CommRing R] [IsDomain R] [Infinite R] {n : ℕ} (σ : Fin n → ℕ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) (hio2 : RowNat R σ io)
    (w : List (Fin n × Fin n × ℕ)) (f : ↥(dualWeyl R n n σ))
    (hw : applyWord R w (f : MvPolynomial (Fin n × Fin n) R) ∈ dualWeyl R n n σ) :
    io ⟨_, hw⟩ = applyWord R (liftWord w) (io f) := by
  revert hw
  induction w with
  | nil => intro hw; rfl
  | cons x w ih =>
    intro hw
    have hw' := applyWord_mem_dual_gen R σ w _ f.2
    change io ⟨rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (f : MvPolynomial (Fin n × Fin n) R)), hw⟩ =
      rowDiv R x.1.castSucc x.2.1.castSucc x.2.2 (applyWord R (liftWord w) (io f))
    rw [io_rowDiv_gen R σ io hio2 x.1 x.2.1 x.2.2 ⟨_, hw'⟩ hw, ih hw']

theorem applyWord_smul_gen (R : Type) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ)) (c : R)
    (f : MvPolynomial (Fin r × Fin n) R) : applyWord R w (c • f) = c • applyWord R w f := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    change rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (c • f)) = c • rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f)
    rw [ih, Formalism.GradedWeylDivisibility.rowDiv_smul]

def HwVal (R : Type) [CommRing R] {n : ℕ} (lam σ : Fin n → ℕ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) : Prop :=
  ∀ h : ↥(dualWeyl R n n σ), (h : MvPolynomial (Fin n × Fin n) R) = hw R le_rfl σ →
    io h = ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ lam) (fun i => (σ i : ℤ)) : ℤ) : R) • Formalism.BranchingDeterminantCap.xiB R lam σ

theorem io_weyl_gen (R : Type) [CommRing R] [IsDomain R] [Infinite R] {n : ℕ} (lam σ : Fin n → ℕ) (hσ : Antitone σ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) (hio2 : RowNat R σ io)
    (hio3 : HwVal R lam σ io)
    (w : List (Fin n × Fin n × ℕ)) (hwd : applyWord R w (hw R le_rfl σ) ∈ dualWeyl R n n σ) :
    io ⟨_, hwd⟩ = ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ lam) (fun i => (σ i : ℤ)) : ℤ) : R) •
      applyWord R (liftWord w) (Formalism.BranchingDeterminantCap.xiB R lam σ) := by
  have hhw : hw R le_rfl σ ∈ dualWeyl R n n σ :=
    Formalism.GradedWeylDivisibility.weylLeDual R n n le_rfl _ hσ (Submodule.subset_span ⟨[], rfl⟩)
  rw [io_applyWord_gen R σ io hio2 w ⟨_, hhw⟩ hwd, hio3 ⟨_, hhw⟩ rfl, applyWord_smul_gen]

theorem map_initMinor_gen {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n s : ℕ} (I : Fin s → Fin r)
    (hs : s ≤ n) : map φ (initMinor R I hs) = initMinor S I hs := by
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

theorem map_xiB {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (lam σ : Fin n → ℕ) :
    map φ (Formalism.BranchingDeterminantCap.xiB R lam σ) = Formalism.BranchingDeterminantCap.xiB S lam σ := by
  unfold Formalism.BranchingDeterminantCap.xiB
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_pow, map_initMinor_gen, map_initMinor_gen]

theorem map_smul_gen {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {κ : Type} (c : R) (f : MvPolynomial κ R) :
    map φ (c • f) = φ c • map φ f := by
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]

theorem io_bc_weyl {R S : Type} [CommRing R] [IsDomain R] [Infinite R] [CommRing S] [IsDomain S] [Infinite S]
    (φ : R →+* S) {n : ℕ} (lam σ : Fin n → ℕ) (hσ : Antitone σ)
    (ioR : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) (hR2 : RowNat R σ ioR)
    (hR3 : HwVal R lam σ ioR)
    (ioS : ↥(dualWeyl S n n σ) →ₗ[S] MvPolynomial (Fin (n + 1) × Fin n) S) (hS2 : RowNat S σ ioS)
    (hS3 : HwVal S lam σ ioS)
    (y : MvPolynomial (Fin n × Fin n) R) (hy : y ∈ weyl R n n le_rfl σ) :
    ∀ (h1 : y ∈ dualWeyl R n n σ) (h2 : map φ y ∈ dualWeyl S n n σ), ioS ⟨_, h2⟩ = map φ (ioR ⟨y, h1⟩) := by
  have hle := Formalism.GradedWeylDivisibility.weylLeDual R n n le_rfl σ hσ
  have hmp : ∀ x, x ∈ dualWeyl R n n σ → map φ x ∈ dualWeyl S n n σ :=
    fun x hx => Formalism.GradedWeylDivisibility.dualWeylMap R S φ n n σ x hx
  unfold weyl at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    intro h1 h2
    have h2' : applyWord S w (hw S le_rfl σ) ∈ dualWeyl S n n σ := by
      rw [← lclosedeq_hw_map φ, lclosedeq_applyWord_map]
      exact h2
    have e : (⟨_, h2⟩ : ↥(dualWeyl S n n σ)) = ⟨_, h2'⟩ := by
      apply Subtype.ext
      show map φ (applyWord R w (hw R le_rfl σ)) = applyWord S w (hw S le_rfl σ)
      rw [← lclosedeq_hw_map φ, lclosedeq_applyWord_map]
    rw [e, io_weyl_gen S lam σ hσ ioS hS2 hS3 w h2']
    have e1 := io_weyl_gen R lam σ hσ ioR hR2 hR3 w h1
    rw [e1, map_smul_gen, ← lclosedeq_applyWord_map, map_xiB, map_intCast]
  | zero =>
    intro h1 h2
    have e1 : (⟨_, h1⟩ : ↥(dualWeyl R n n σ)) = 0 := rfl
    have e2 : (⟨_, h2⟩ : ↥(dualWeyl S n n σ)) = 0 := Subtype.ext (map_zero _)
    rw [e1, e2, map_zero, map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    intro h1 h2
    have hx1 := hle hx
    have hy1 := hle hy
    have e1 : (⟨_, h1⟩ : ↥(dualWeyl R n n σ)) = ⟨x, hx1⟩ + ⟨y, hy1⟩ := rfl
    have e2 : (⟨_, h2⟩ : ↥(dualWeyl S n n σ)) = ⟨_, hmp x hx1⟩ + ⟨_, hmp y hy1⟩ := Subtype.ext (map_add _ _ _)
    rw [e1, e2, map_add, map_add, map_add, ihx hx1 (hmp x hx1), ihy hy1 (hmp y hy1)]
  | smul c x hx ihx =>
    intro h1 h2
    have hx1 := hle hx
    have e1 : (⟨_, h1⟩ : ↥(dualWeyl R n n σ)) = c • ⟨x, hx1⟩ := rfl
    have e2 : (⟨_, h2⟩ : ↥(dualWeyl S n n σ)) = φ c • ⟨_, hmp x hx1⟩ := Subtype.ext (map_smul_gen φ c x)
    rw [e1, e2, map_smul, map_smul, map_smul_gen, ihx hx1 (hmp x hx1)]

theorem io_bc {R S : Type} [CommRing R] [IsDomain R] [Infinite R] [CommRing S] [IsDomain S] [Infinite S]
    (φ : R →+* S) (hφ : Function.Injective φ) {n : ℕ} (lam σ : Fin n → ℕ) (hσ : Antitone σ)
    (ioR : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) (hR2 : RowNat R σ ioR)
    (hR3 : HwVal R lam σ ioR)
    (ioS : ↥(dualWeyl S n n σ) →ₗ[S] MvPolynomial (Fin (n + 1) × Fin n) S) (hS2 : RowNat S σ ioS)
    (hS3 : HwVal S lam σ ioS)
    (q : MvPolynomial (Fin n × Fin n) R) (N : R) (hN : N ≠ 0) (hq : N • q ∈ weyl R n n le_rfl σ)
    (h1 : q ∈ dualWeyl R n n σ) (h2 : map φ q ∈ dualWeyl S n n σ) : ioS ⟨_, h2⟩ = map φ (ioR ⟨q, h1⟩) := by
  have h1' : N • q ∈ dualWeyl R n n σ := Submodule.smul_mem _ _ h1
  have h2' : map φ (N • q) ∈ dualWeyl S n n σ := Formalism.GradedWeylDivisibility.dualWeylMap R S φ n n σ _ h1'
  have key := io_bc_weyl φ lam σ hσ ioR hR2 hR3 ioS hS2 hS3 (N • q) hq h1' h2'
  have e1 : (⟨_, h1'⟩ : ↥(dualWeyl R n n σ)) = N • ⟨q, h1⟩ := rfl
  have e2 : (⟨_, h2'⟩ : ↥(dualWeyl S n n σ)) = φ N • ⟨_, h2⟩ := Subtype.ext (map_smul_gen φ N q)
  rw [e1, e2, map_smul, map_smul, map_smul_gen, smul_eq_C_mul, smul_eq_C_mul] at key
  have hC : (C (φ N) : MvPolynomial (Fin (n + 1) × Fin n) S) ≠ 0 := by
    rw [Ne, C_eq_zero]
    exact fun h => hN (hφ (by rw [h, map_zero]))
  exact mul_left_cancel₀ hC key

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
