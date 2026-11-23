import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

noncomputable section
namespace GlobalTheory.FockEmbExp
open Formalism.BasicNotions.TH Matrix
open scoped Kronecker

section general
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem exp_kron_left (Y : Matrix m m ℂ) :
    NormedSpace.exp (Y ⊗ₖ (1 : Matrix n n ℂ)) = NormedSpace.exp Y ⊗ₖ (1 : Matrix n n ℂ) := by
  let f : Matrix m m ℂ →+* Matrix (m × n) (m × n) ℂ :=
    { toFun Y := Y ⊗ₖ (1 : Matrix n n ℂ)
      map_one' := Matrix.one_kronecker_one
      map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      map_zero' := Matrix.zero_kronecker _
      map_add' A B := Matrix.add_kronecker _ _ _ }
  have hf : Continuous f := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    show Continuous fun Y : Matrix m m ℂ => Y a.1 b.1 * (1 : Matrix n n ℂ) a.2 b.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

theorem exp_kron_right (Z : Matrix n n ℂ) :
    NormedSpace.exp ((1 : Matrix m m ℂ) ⊗ₖ Z) = (1 : Matrix m m ℂ) ⊗ₖ NormedSpace.exp Z := by
  let f : Matrix n n ℂ →+* Matrix (m × n) (m × n) ℂ :=
    { toFun Z := (1 : Matrix m m ℂ) ⊗ₖ Z
      map_one' := Matrix.one_kronecker_one
      map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      map_zero' := Matrix.kronecker_zero _
      map_add' A B := Matrix.kronecker_add _ _ _ }
  have hf : Continuous f := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    show Continuous fun Y : Matrix n n ℂ => (1 : Matrix m m ℂ) a.1 b.1 * Y a.2 b.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Z).symm

theorem exp_reindex' (e : m ≃ n) (X : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.reindex e e X) = Matrix.reindex e e (NormedSpace.exp X) := by
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X).symm

end general

variable {p q r s : ℕ}

theorem smul_mem {X : Mat p q} (hX : X ∈ upq p q) (t : ℝ) : t • X ∈ upq p q := by
  have h : Xᴴ * Jm p q + Jm p q * X = 0 := hX
  show (t • X)ᴴ * Jm p q + Jm p q * (t • X) = 0
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h,
    smul_zero]

theorem continuous_expt (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) :
    Continuous fun t : ℝ => T.expt (t • X) :=
  T.expt_cont.comp_continuous (by fun_prop) fun t => smul_mem hX t

theorem lift_unique (T : GrpData p q) {γ δ : ℝ → T.G} (hγ : Continuous γ) (hδ : Continuous δ)
    (hc : ∀ t, T.cov (γ t) = T.cov (δ t)) (h0 : γ 0 = δ 0) (t : ℝ) : γ t = δ t := by
  have hsq : Continuous T.sq := continuous_snd.comp T.emb.continuous
  have h := isPreconnected_univ.eq_of_sq_eq (α := ℝ)
    (f := fun t : ℝ => ((T.sq (γ t) : ℂˣ) : ℂ)) (g := fun t : ℝ => ((T.sq (δ t) : ℂˣ) : ℂ))
    (Units.continuous_val.comp (hsq.comp hγ)).continuousOn
    (Units.continuous_val.comp (hsq.comp hδ)).continuousOn (fun t _ => by
      simp only [Pi.pow_apply]
      rw [T.sq_sq, T.sq_sq, hc]) (fun _ => Units.ne_zero _) (Set.mem_univ 0) (by simp only [h0])
  exact T.emb.injective (Prod.ext (hc t) (Units.ext (h (Set.mem_univ t))))

theorem Jm_diag (p q : ℕ) :
    Jm p q = Matrix.diagonal fun a => if a.isLeft then (1 : ℂ) else -1 := by
  ext (a | a) (b | b) <;> simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem Jm_eq (p q r s : ℕ) : Jm (p * r + q * s) (p * s + q * r) =
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Jm p q ⊗ₖ Jm r s) := by
  rw [Jm_diag, Jm_diag, Jm_diag, Matrix.diagonal_kronecker_diagonal, Matrix.reindex_apply,
    Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  obtain ⟨l, rfl⟩ := (lineEquiv p q r s).surjective x
  rw [lineEquiv_isLeft, Function.comp, Equiv.symm_apply_apply]
  rcases l with ⟨a | a, c | c⟩ <;> simp [linePos]

theorem left_mem {Y : Mat p q} (hY : Y ∈ upq p q) (r s : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Y ⊗ₖ (1 : Mat r s)) ∈
      upq (p * r + q * s) (p * s + q * r) := by
  have h : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
  show _ᴴ * _ + _ * _ = 0
  rw [Jm_eq, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have := congrArg (fun A : Mat p q => (A ⊗ₖ Jm r s).submatrix (lineEquiv p q r s).symm (lineEquiv p q r s).symm) h
  simpa [Matrix.add_kronecker, Matrix.submatrix_add] using this

theorem right_mem {Y : Mat r s} (hY : Y ∈ upq r s) (p q : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) ((1 : Mat p q) ⊗ₖ Y) ∈
      upq (p * r + q * s) (p * s + q * r) := by
  have h : Yᴴ * Jm r s + Jm r s * Y = 0 := hY
  show _ᴴ * _ + _ * _ = 0
  rw [Jm_eq, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have := congrArg (fun A : Mat r s => (Jm p q ⊗ₖ A).submatrix (lineEquiv p q r s).symm (lineEquiv p q r s).symm) h
  simpa [Matrix.kronecker_add, Matrix.submatrix_add] using this

variable {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q} {T2 : GrpData r s}

theorem continuous_emb (F : FockData T0 T1 T2) : Continuous F.emb := by
  have h1 : Continuous T1.cov := continuous_fst.comp T1.emb.continuous
  have h2 : Continuous T2.cov := continuous_fst.comp T2.emb.continuous
  have s1 : Continuous T1.sq := continuous_snd.comp T1.emb.continuous
  have s2 : Continuous T2.sq := continuous_snd.comp T2.emb.continuous
  have hv : Continuous fun x : T1.G × T2.G =>
      ((T0.cov (F.emb x) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) := by
    have c1 := (Units.continuous_val.comp h1).comp (continuous_fst (X := T1.G) (Y := T2.G))
    have c2 := (Units.continuous_val.comp h2).comp (continuous_snd (X := T1.G) (Y := T2.G))
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have := (c1.matrix_elem ((lineEquiv p q r s).symm a).1 ((lineEquiv p q r s).symm b).1).mul
      (c2.matrix_elem ((lineEquiv p q r s).symm a).2 ((lineEquiv p q r s).symm b).2)
    refine this.congr fun x => ?_
    rw [show x = (x.1, x.2) from rfl, F.emb_cov]
    rfl
  rw [T0.emb.isInducing.continuous_iff]
  refine Continuous.prodMk (Units.continuous_iff.2 ⟨hv, ?_⟩) ?_
  · refine (hv.comp continuous_inv).congr fun x => ?_
    simp only [Function.comp, map_inv]
  · refine (((s1.comp continuous_fst).pow (r + s)).mul ((s2.comp continuous_snd).pow (p + q))).congr
      fun x => ?_
    exact (F.emb_sq x.1 x.2).symm

theorem emb_expt_left (F : FockData T0 T1 T2) {Y : Mat p q} (hY : Y ∈ upq p q) (t : ℝ) :
    F.emb (T1.expt (t • Y), 1) = T0.expt (t • Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Y ⊗ₖ (1 : Mat r s))) := by
  refine lift_unique T0 (γ := fun t : ℝ => F.emb (T1.expt (t • Y), 1))
    ((continuous_emb F).comp ((continuous_expt T1 hY).prodMk continuous_const))
    (continuous_expt T0 (left_mem hY r s)) (fun t => Units.ext ?_) ?_ t
  · rw [F.emb_cov, T0.expt_cov _ (smul_mem (left_mem hY r s) t), T1.expt_cov _ (smul_mem hY t),
      map_one, Units.val_one, ← exp_kron_left, ← exp_reindex']
    congr 1
    ext a b
    simp
    ring
  · simp only [zero_smul, T1.expt_zero, T0.expt_zero]
    exact map_one F.emb

theorem emb_expt_right (F : FockData T0 T1 T2) {Y : Mat r s} (hY : Y ∈ upq r s) (t : ℝ) :
    F.emb (1, T2.expt (t • Y)) = T0.expt (t • Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      ((1 : Mat p q) ⊗ₖ Y)) := by
  refine lift_unique T0 (γ := fun t : ℝ => F.emb (1, T2.expt (t • Y)))
    ((continuous_emb F).comp (continuous_const.prodMk (continuous_expt T2 hY)))
    (continuous_expt T0 (right_mem hY p q)) (fun t => Units.ext ?_) ?_ t
  · rw [F.emb_cov, T0.expt_cov _ (smul_mem (right_mem hY p q) t), T2.expt_cov _ (smul_mem hY t),
      map_one, Units.val_one, ← exp_kron_right, ← exp_reindex']
    congr 1
    ext a b
    simp
    ring
  · simp only [zero_smul, T2.expt_zero, T0.expt_zero]
    exact map_one F.emb

theorem fock_derived : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), Continuous F.emb ∧ (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => F.π (T1.expt (t • Y), 1) (F.ι P)) (F.ι (fockAct1 p q r s Y P)) 0) ∧ (∀ Y ∈ upq r s, ∀ P, HasDerivAt (fun t : ℝ => F.π (1, T2.expt (t • Y)) (F.ι P)) (F.ι (fockAct2 p q r s Y P)) 0) := by
  intro p q r s T0 T1 T2 F
  refine ⟨continuous_emb F, fun Y hY P => ?_, fun Y hY P => ?_⟩
  · have h := F.der _ (left_mem hY r s) P
    rw [← Matrix.reindex_symm, Equiv.symm_apply_apply] at h
    simp only [FockData.π, MonoidHom.comp_apply, emb_expt_left F hY]
    exact h
  · have h := F.der _ (right_mem hY p q) P
    rw [← Matrix.reindex_symm, Equiv.symm_apply_apply] at h
    simp only [FockData.π, MonoidHom.comp_apply, emb_expt_right F hY]
    exact h

end GlobalTheory.FockEmbExp
