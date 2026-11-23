import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.AtTraceT

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxd2

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  show IsOpen {g : Mat n | g.det ≠ 0}
  exact isOpen_ne_fun continuous_id.matrix_det continuous_const

theorem rm_diff (lam : Fin n → ℤ) {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ (Rm lam) x :=
  ((Cxc.rm_smooth lam).contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)

theorem hasDerivAt_line {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Mat n → W} {x : Mat n}
    (hf : DifferentiableAt ℝ f x) (X : Mat n) :
    HasDerivAt (fun t : ℝ => f (x * (1 + t • X))) (fderiv ℝ f x (x * X)) 0 := by
  have hg : HasDerivAt (fun t : ℝ => x * (1 + t • X)) (x * X) 0 := by
    have e : (fun t : ℝ => x * (1 + t • X)) = fun t => x + t • (x * X) := by
      funext t
      rw [mul_add, mul_one, Matrix.mul_smul]
    rw [e]
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (x * X)).const_add x
    rw [one_smul] at this
    exact this
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hg (by simp)

def entL {J : Type} [Fintype J] [DecidableEq J] (P N : Matrix J J ℂ) (i j : J) : Matrix J J ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (P * M * N) i j
      map_add' := fun M M' => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r M => by simp [Matrix.mul_smul, Matrix.smul_mul] }

theorem entL_apply {J : Type} [Fintype J] [DecidableEq J] (P N M : Matrix J J ℂ) (i j : J) :
    entL P N i j M = (P * M * N) i j := rfl

theorem eventually_det (X : Mat n) : ∀ᶠ t : ℝ in nhds 0, IsUnit (1 + t • X).det := by
  have hc : Continuous (fun t : ℝ => (1 + t • X).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have h0 : (1 + (0 : ℝ) • X).det ≠ 0 := by simp
  exact (hc.continuousAt.eventually_ne h0).mono fun t ht => isUnit_iff_ne_zero.mpr ht

theorem hasDerivAt_rm_one (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (X : Mat n) :
    HasDerivAt (fun t : ℝ => Rm lam (1 + t • X)) (∑ a, ∑ b, X a b • At lam a b) 0 := by
  have h := hasDerivAt_line (rm_diff lam (x := 1) (by show (1 : Mat n).det ≠ 0; simp)) X
  simp only [one_mul] at h
  convert h using 1
  all_goals first
    | rfl
    | exact (hD n lam hlam X).symm
    | (congr 1; exact (hD n lam hlam X).symm)

theorem rd_hol (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (X : Mat n) :
    Rd X (fun y => (Rm lam y * N) i j) x = (Rm lam x * (∑ a, ∑ b, X a b • At lam a b) * N) i j := by
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have hf : DifferentiableAt ℝ (fun y => (Rm lam y * N) i j) x := by
    have := ((entL 1 N i j).differentiableAt).comp x (rm_diff lam hx)
    simp only [Function.comp_def, entL_apply, one_mul] at this
    exact this
  have h1 := hasDerivAt_line hf X
  have h2 : HasDerivAt (fun t : ℝ => (Rm lam x * Rm lam (1 + t • X) * N) i j)
      ((Rm lam x * (∑ a, ∑ b, X a b • At lam a b) * N) i j) 0 := by
    have := (entL (Rm lam x) N i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rm_one lam hD hlam X)
    simp only [Function.comp_def, entL_apply] at this
    exact this
  have h3 : (fun t : ℝ => (Rm lam (x * (1 + t • X)) * N) i j) =ᶠ[nhds 0]
      fun t => (Rm lam x * Rm lam (1 + t • X) * N) i j := by
    filter_upwards [eventually_det X] with t ht
    rw [Cxc.rm_mul lam x _ hxu ht]
  show fderiv ℝ (fun y => (Rm lam y * N) i j) x (x * X) = _
  exact h1.unique (h3.hasDerivAt_iff.mpr h2)

theorem sum_single {lam : Fin n → ℤ} (X : Mat n) (a b : Fin n) (z : ℂ) (A : Fin n → Fin n → Matrix (Jd n lam) (Jd n lam) ℂ) :
    ∑ c, ∑ d, (Matrix.single a b z : Mat n) c d • A c d = z • A a b := by
  simp [Matrix.single_apply, ite_and, ite_smul]

theorem eu_hol (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (s : Bool) (a b : Fin n) :
    Eu s a b (fun y => (Rm lam y * N) i j) x = if s then (Rm lam x * At lam a b * N) i j else 0 := by
  have e1 := rd_hol lam hD hlam N i j hx (Matrix.single a b 1)
  have e2 := rd_hol lam hD hlam N i j hx (Matrix.single a b Complex.I)
  rw [sum_single (0 : Mat n) a b (1 : ℂ) (At lam)] at e1
  rw [sum_single (0 : Mat n) a b Complex.I (At lam)] at e2
  simp only [Eu, Pi.smul_apply, Pi.add_apply, e1, e2]
  cases s <;> simp [Matrix.mul_smul, Matrix.smul_mul] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem eu_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f g : Mat n → V} {x : Mat n}
    (h : f =ᶠ[nhds x] g) (s : Bool) (a b : Fin n) : Eu s a b f x = Eu s a b g x := by
  have e : ∀ Y : Mat n, Rd Y f x = Rd Y g x := fun Y => by
    simp only [Rd, h.fderiv_eq]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, e]

theorem epow_hol (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (M : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow true m a b (fun y => (Rm lam y * M) i j))
      (fun y => (Rm lam y * (At lam ^ m) a b * M) i j) (GLs n) := by
  induction m with
  | zero =>
    intro a b y hy
    rw [Epow.eq_1]
    by_cases h : a = b <;> simp [h, Matrix.one_apply]
  | succ m ih =>
    intro a b y hy
    rw [show m + 1 = m.succ from rfl, Epow.eq_2]
    simp only [Finset.sum_apply]
    have key : ∀ c, Eu true a c (Epow true m c b (fun y => (Rm lam y * M) i j)) y
        = (Rm lam y * At lam a c * ((At lam ^ m) c b * M)) i j := fun c => by
      rw [eu_congr (g := fun z => (Rm lam z * ((At lam ^ m) c b * M)) i j) ?_ true a c]
      · rw [eu_hol lam hD hlam ((At lam ^ m) c b * M) i j hy true a c]
        exact if_pos rfl
      · filter_upwards [isOpen_GLs.mem_nhds hy] with z hz
        exact (ih c b hz).trans (congrFun (congrFun (Matrix.mul_assoc _ _ _) i) j)
    simp only [key]
    rw [pow_succ', Matrix.mul_apply (M := At lam) (N := At lam ^ m), Finset.mul_sum, Finset.sum_mul,
      Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_assoc]

theorem rmHol_of (hT : AtTrace) (hD : AtDer) : RmHol := by
  intro n lam hlam M i j g hg
  refine ⟨fun m => ?_, fun a b => by rw [eu_hol lam hD hlam M i j hg false a b]; rfl⟩
  simp only [gel, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => epow_hol lam hD hlam M i j m a a hg]
  have e : ∑ a, (Rm lam g * (At lam ^ m) a a * M) i j = (Rm lam g * (At lam ^ m).trace * M) i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  rw [e, hT n lam hlam m]
  simp [Matrix.mul_smul, Matrix.smul_mul]

end PositivityTheory.RgBcC.Cxd2
