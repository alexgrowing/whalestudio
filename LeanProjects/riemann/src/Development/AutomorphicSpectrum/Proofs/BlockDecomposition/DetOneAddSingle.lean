import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.DeterminantPowerSmoothness.DetPowSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowIrreducibleKStable

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.FFin

variable {n : ℕ}

def evP (p : MvPolynomial (Fin n × Fin n) ℂ) (g : Mat n) : ℂ := MvPolynomial.eval (fun ij => g ij.1 ij.2) p

def Tp (a b : Fin n) : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ c, LinearMap.mulLeft ℂ (MvPolynomial.X (c, a)) ∘ₗ (MvPolynomial.pderiv (c, b)).toLinearMap

def Qf (e : Fin n → ℤ) (g : Mat n) : ℂ := ∏ j, GlobalTheory.CompanionTheory.ModelS.gm j g ^ e j

def wf (e : Fin n → ℤ) (m : ℤ) (p : MvPolynomial (Fin n × Fin n) ℂ) : Mat n → ℂ :=
  (GLs n).indicator fun g => Qf e g * g.det ^ m * evP p g

open scoped ComplexOrder in

theorem gm_ne_zero (j : Fin n) {g : Mat n} (hg : g ∈ GLs n) : GlobalTheory.CompanionTheory.ModelS.gm j g ≠ 0 := by
  unfold GlobalTheory.CompanionTheory.ModelS.gm
  have hli : LinearIndependent ℂ g.row := by
    have : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg)
    exact Matrix.linearIndependent_rows_of_isUnit this
  have hinj : Function.Injective (g.submatrix (GlobalTheory.CompanionTheory.ModelS.ini j) id).vecMul := by
    rw [Matrix.vecMul_injective_iff]
    exact hli.comp _ (Fin.castLE_injective _)
  have hp := Matrix.PosDef.mul_conjTranspose_self _ hinj
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit).ne_zero

theorem gm_smooth (j : Fin n) : ContDiff ℝ ∞ (GlobalTheory.CompanionTheory.ModelS.gm j : Mat n → ℂ) := by
  have hent : ∀ a b : Fin n, ContDiff ℝ ∞ (fun x : Mat n => x a b) := fun a b =>
    (contDiff_apply_apply ℝ ℂ a b).restrict_scalars ℝ
  unfold GlobalTheory.CompanionTheory.ModelS.gm
  refine Cxc.det_smooth.comp ?_
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
  refine ContDiff.sum fun c _ => ContDiff.mul (hent _ _) ?_
  exact (Complex.conjCLE.contDiff).comp (hent _ _)

theorem Qf_smooth (e : Fin n → ℤ) : ContDiffOn ℝ ∞ (Qf e) (GLs n) := by
  unfold Qf
  refine contDiffOn_prod fun j _ => ?_
  intro g hg
  refine ContDiffAt.contDiffWithinAt ?_
  have hG : ContDiffAt ℝ ∞ (GlobalTheory.CompanionTheory.ModelS.gm j : Mat n → ℂ) g := (gm_smooth j).contDiffAt
  generalize e j = c
  cases c with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact hG.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hG.pow (k + 1)).inv (pow_ne_zero _ (gm_ne_zero j hg))

def entryL (a b : Fin n) : Mat n →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)

theorem entryL_apply (a b : Fin n) (x : Mat n) : entryL a b x = x a b := rfl

theorem evP_C (c : ℂ) (g : Mat n) : evP (MvPolynomial.C c) g = c := by simp [evP]

theorem evP_X (i : Fin n × Fin n) (g : Mat n) : evP (MvPolynomial.X i) g = g i.1 i.2 := by simp [evP]

theorem evalPoints_add (p q : MvPolynomial (Fin n × Fin n) ℂ) (g : Mat n) : evP (p + q) g = evP p g + evP q g := by
  simp [evP]

theorem evP_mul (p q : MvPolynomial (Fin n × Fin n) ℂ) (g : Mat n) : evP (p * q) g = evP p g * evP q g := by
  simp [evP]

theorem evalEmbedding_smul (c : ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) (g : Mat n) : evP (c • p) g = c * evP p g := by
  simp [evP]

theorem contDiff_evalMatrix (p : MvPolynomial (Fin n × Fin n) ℂ) : ContDiff ℂ ∞ (evP p : Mat n → ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have e : (evP (MvPolynomial.C c) : Mat n → ℂ) = fun _ => c := funext (evP_C c)
    rw [e]
    exact contDiff_const
  | add p q hp hq =>
    have e : (evP (p + q) : Mat n → ℂ) = fun g => evP p g + evP q g := funext (evalPoints_add p q)
    rw [e]
    exact hp.add hq
  | mul_X p i hp =>
    have e : (evP (p * MvPolynomial.X i) : Mat n → ℂ) = fun g => evP p g * entryL i.1 i.2 g := by
      funext g
      rw [evP_mul, evP_X, entryL_apply]
    rw [e]
    exact hp.mul (entryL i.1 i.2).contDiff

theorem differentiable_evalMatrix (p : MvPolynomial (Fin n × Fin n) ℂ) : Differentiable ℂ (evP p : Mat n → ℂ) :=
  (contDiff_evalMatrix p).differentiable (by simp)

theorem fderiv_evalMatrix (p : MvPolynomial (Fin n × Fin n) ℂ) (g v : Mat n) :
    fderiv ℂ (evP p) g v = ∑ c, ∑ d, evP (MvPolynomial.pderiv (c, d) p) g * v c d := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have e : (evP (MvPolynomial.C c) : Mat n → ℂ) = fun _ => c := funext (evP_C c)
    rw [e]
    simp [evP]
  | add p q hp hq =>
    have e : (evP (p + q) : Mat n → ℂ) = evP p + evP q := funext (evalPoints_add p q)
    have h : HasFDerivAt (evP (p + q)) (fderiv ℂ (evP p) g + fderiv ℂ (evP q) g) g := by
      rw [e]
      exact (differentiable_evalMatrix p g).hasFDerivAt.add (differentiable_evalMatrix q g).hasFDerivAt
    rw [h.fderiv]
    simp only [ContinuousLinearMap.add_apply, hp, hq, map_add, evalPoints_add, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have e : (evP (p * MvPolynomial.X i) : Mat n → ℂ) = evP p * ⇑(entryL i.1 i.2) := by
      funext g
      rw [Pi.mul_apply, evP_mul, evP_X, entryL_apply]
    have h : HasFDerivAt (evP (p * MvPolynomial.X i))
        (evP p g • entryL i.1 i.2 + entryL i.1 i.2 g • fderiv ℂ (evP p) g) g := by
      rw [e]
      exact (differentiable_evalMatrix p g).hasFDerivAt.mul (entryL i.1 i.2).hasFDerivAt
    have key : ∀ c d, evP (MvPolynomial.pderiv (c, d) (p * MvPolynomial.X i)) g =
        g i.1 i.2 * evP (MvPolynomial.pderiv (c, d) p) g + evP p g * (if (c, d) = i then 1 else 0) := by
      intro c d
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, evalPoints_add, evP_mul, evP_mul, evP_X,
        add_comm]
      congr 2
      by_cases hi : (c, d) = i
      · subst hi
        simp [evP]
      · have : i ≠ (c, d) := fun h => hi h.symm
        simp [evP, hi, Pi.single_apply, this]
    rw [h.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hp, smul_eq_mul, entryL_apply, key,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    obtain ⟨i₁, i₂⟩ := i
    rw [add_comm]
    congr 1
    simp [Prod.mk.injEq, ite_and, Finset.sum_ite_eq]

theorem evP_Tp (a b : Fin n) (p : MvPolynomial (Fin n × Fin n) ℂ) (g : Mat n) :
    evP (Tp a b p) g = ∑ c, g c a * evP (MvPolynomial.pderiv (c, b) p) g := by
  simp [Tp, LinearMap.sum_apply, evP]

theorem mul_single_entry (g : Mat n) (a b c d : Fin n) :
    (g * Matrix.single a b (1 : ℂ)) c d = if d = b then g c a else 0 := by
  by_cases h : d = b
  · subst h
    simp [Matrix.mul_apply, Matrix.single_apply]
  · simp [Matrix.mul_apply, Matrix.single_apply, h, Ne.symm h]

theorem fderiv_evalMatrix_mul_single (p : MvPolynomial (Fin n × Fin n) ℂ) (g : Mat n) (a b : Fin n) :
    fderiv ℂ (evP p) g (g * Matrix.single a b (1 : ℂ)) = evP (Tp a b p) g := by
  rw [fderiv_evalMatrix, evP_Tp]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_single_entry, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

def detP : MvPolynomial (Fin n × Fin n) ℂ := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det

def minP {k : ℕ} (r : Fin k → Fin n) : MvPolynomial (Fin n × Fin n) ℂ :=
  ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).submatrix r r).det

theorem evalMatrix_minor {k : ℕ} (r : Fin k → Fin n) (g : Mat n) : evP (minP r) g = (g.submatrix r r).det := by
  unfold evP minP
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [Matrix.mvPolynomialX_apply]

theorem evalMatrix_det (g : Mat n) : evP detP g = g.det := by
  unfold evP detP
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [Matrix.mvPolynomialX_apply]

theorem det_diff : Differentiable ℂ (fun x : Mat n => x.det) := by
  have e : (fun x : Mat n => x.det) = evP detP := funext fun x => (evalMatrix_det x).symm
  rw [e]
  exact differentiable_evalMatrix _

theorem det_one_add_single (a b : Fin n) (t : ℂ) :
    (1 + t • Matrix.single a b (1 : ℂ) : Mat n).det = 1 + if a = b then t else 0 := by
  by_cases h : a = b
  · subst h
    have e : (1 + t • Matrix.single a a (1 : ℂ) : Mat n) = Matrix.diagonal (fun i => if i = a then 1 + t else 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hi : i = a
        · subst hi
          simp
        · simp [hi, Ne.symm hi, Matrix.single_apply]
      · simp [Matrix.one_apply, Matrix.single_apply, hij, Matrix.diagonal_apply]
        intro h1 h2
        exact absurd (h1.symm.trans h2) hij
    rw [e, Matrix.det_diagonal]
    simp
  · have e : (1 + t • Matrix.single a b (1 : ℂ) : Mat n) = Matrix.transvection a b t := by
      simp [Matrix.transvection]
    rw [e, Matrix.det_transvection_of_ne a b h t]
    simp [h]

theorem detz_diff (m : ℤ) {g : Mat n} (hg : g ∈ GLs n) : DifferentiableAt ℂ (fun x : Mat n => x.det ^ m) g :=
  (det_diff g).zpow (Or.inl hg)

theorem detz_fderiv (m : ℤ) {g : Mat n} (hg : g ∈ GLs n) (a b : Fin n) :
    fderiv ℂ (fun x : Mat n => x.det ^ m) g (g * Matrix.single a b (1 : ℂ)) =
      (if a = b then (m : ℂ) else 0) * g.det ^ m := by
  have h1 : HasDerivAt (fun t : ℂ => (g + t • (g * Matrix.single a b (1 : ℂ))).det ^ m)
      (fderiv ℂ (fun x : Mat n => x.det ^ m) g (g * Matrix.single a b (1 : ℂ))) 0 :=
    (detz_diff m hg).hasFDerivAt.hasLineDerivAt _
  have h2 : ∀ t : ℂ, (g + t • (g * Matrix.single a b (1 : ℂ))).det ^ m =
      g.det ^ m * (1 + if a = b then t else 0) ^ m := by
    intro t
    have e : g + t • (g * Matrix.single a b (1 : ℂ)) = g * (1 + t • Matrix.single a b (1 : ℂ)) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [e, Matrix.det_mul, det_one_add_single, mul_zpow]
  have h3 : HasDerivAt (fun t : ℂ => g.det ^ m * (1 + if a = b then t else 0) ^ m)
      ((if a = b then (m : ℂ) else 0) * g.det ^ m) 0 := by
    by_cases h : a = b
    · simp only [h, if_true]
      have h4 : HasDerivAt (fun z : ℂ => z ^ m) ((m : ℂ) * (1 + 0 : ℂ) ^ (m - 1)) (1 + 0) :=
        hasDerivAt_zpow m _ (Or.inl (by simp))
      have h5 := (h4.comp_const_add 1 0).const_mul (g.det ^ m)
      simpa [mul_comm] using h5
    · simp only [h, if_false]
      simpa using hasDerivAt_const (0 : ℂ) (g.det ^ m * (1 + 0 : ℂ) ^ m)
  rw [funext h2] at h1
  exact h1.unique h3

theorem gm_path (j : Fin n) (X : Mat n) (hX : Xᴴ = -X) (g : Mat n) (t : ℝ) :
    GlobalTheory.CompanionTheory.ModelS.gm j (g + t • (g * X)) =
      ((g.submatrix (GlobalTheory.CompanionTheory.ModelS.ini j) id) * (g.submatrix (GlobalTheory.CompanionTheory.ModelS.ini j) id)ᴴ -
        ((t ^ 2 : ℝ) : ℂ) • ((g.submatrix (GlobalTheory.CompanionTheory.ModelS.ini j) id) * (X * X) *
          (g.submatrix (GlobalTheory.CompanionTheory.ModelS.ini j) id)ᴴ)).det := by
  unfold GlobalTheory.CompanionTheory.ModelS.gm
  set A := g.submatrix (GlobalTheory.CompanionTheory.ModelS.ini j) id with hA
  have e1' : g + t • (g * X) = g * (1 + (t : ℂ) • X) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rfl
  have e2' : (g + t • (g * X)).submatrix (GlobalTheory.CompanionTheory.ModelS.ini j) id = A * (1 + (t : ℂ) • X) := by
    rw [e1', hA]
    exact Matrix.submatrix_mul _ _ _ id _ Function.bijective_id
  have e3 : (1 + (t : ℂ) • X)ᴴ = 1 - (t : ℂ) • X := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hX, sub_eq_add_neg]
  have e4 : (1 + (t : ℂ) • X) * (1 - (t : ℂ) • X) = 1 - ((t ^ 2 : ℝ) : ℂ) • (X * X) := by
    have h : ∀ Y : Mat n, (1 + Y) * (1 - Y) = 1 - Y * Y := fun Y => by noncomm_ring
    rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    push_cast
    rw [pow_two]
  rw [e2', Matrix.conjTranspose_mul, e3]
  congr 1
  calc A * (1 + (t : ℂ) • X) * ((1 - (t : ℂ) • X) * Aᴴ)
      = A * ((1 + (t : ℂ) • X) * (1 - (t : ℂ) • X)) * Aᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [e4, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]

theorem Qf_kill (e : Fin n → ℤ) (X : Mat n) (hX : Xᴴ = -X) {g : Mat n} (hg : g ∈ GLs n)
    (hd : DifferentiableAt ℝ (Qf e) g) : fderiv ℝ (Qf e) g (g * X) = 0 := by
  classical
  set A : ∀ j : Fin n, Matrix (Fin (j + 1)) (Fin n) ℂ := fun j => g.submatrix (GlobalTheory.CompanionTheory.ModelS.ini j) id with hA
  let M : Fin n → ℝ → ℂ := fun j s => ((A j) * (A j)ᴴ - (s : ℂ) • ((A j) * (X * X) * (A j)ᴴ)).det
  let Ψ : ℝ → ℂ := fun s => ∏ j, M j s ^ e j
  have hM0 : ∀ j, M j 0 = GlobalTheory.CompanionTheory.ModelS.gm j g := fun j => by
    simp [M, GlobalTheory.CompanionTheory.ModelS.gm, hA]
  have hMd : ∀ j, DifferentiableAt ℝ (M j) 0 := fun j => by
    have h1 : ContDiff ℝ ∞ (fun s : ℝ => (A j) * (A j)ᴴ - (s : ℂ) • ((A j) * (X * X) * (A j)ᴴ)) := by
      refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      exact contDiff_const.sub (Complex.ofRealCLM.contDiff.mul contDiff_const)
    exact (Cxc.det_smooth.comp h1).differentiable (by simp) 0
  have hΨ : DifferentiableAt ℝ Ψ 0 := by
    have : Ψ = ∏ j, fun s => M j s ^ e j := by
      funext s
      simp [Ψ, Finset.prod_apply]
    rw [this]
    refine DifferentiableAt.finset_prod fun j _ => ?_
    have hne : M j 0 ≠ 0 := by rw [hM0]; exact gm_ne_zero j hg
    have hD := hMd j
    generalize e j = c
    cases c with
    | ofNat k =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast]
      exact hD.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hD.pow (k + 1)).inv (pow_ne_zero _ hne)
  have h1 : HasDerivAt (fun t : ℝ => Qf e (g + t • (g * X))) (fderiv ℝ (Qf e) g (g * X)) 0 :=
    hd.hasFDerivAt.hasLineDerivAt _
  have h2 : (fun t : ℝ => Qf e (g + t • (g * X))) = fun t => Ψ (t ^ 2) := by
    funext t
    simp only [Qf, Ψ, M]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [gm_path j X hX g t]
  have h3 : HasDerivAt (fun t : ℝ => Ψ (t ^ 2)) ((2 * (0:ℝ)) • deriv Ψ 0) 0 := by
    have hs : HasDerivAt (fun t : ℝ => t ^ 2) (2 * (0:ℝ)) 0 := by simpa using hasDerivAt_pow 2 (0:ℝ)
    have hΨ' : HasDerivAt Ψ (deriv Ψ 0) ((fun t : ℝ => t ^ 2) 0) := by simpa using hΨ.hasDerivAt
    exact HasDerivAt.scomp (h := fun t : ℝ => t ^ 2) 0 hΨ' hs
  rw [h2] at h1
  simpa using h1.unique h3

theorem wf_mem (e : Fin n → ℤ) (m : ℤ) (p : MvPolynomial (Fin n × Fin n) ℂ) : wf e m p ∈ GlobalTheory.CompanionTheory.ModelS.SmF n := by
  refine ⟨?_, fun g hg => Set.indicator_of_notMem hg _⟩
  have h : ContDiffOn ℝ ∞ (fun g : Mat n => Qf e g * g.det ^ m * evP p g) (GLs n) :=
    ((Qf_smooth e).mul (Cxc.detPow_smooth m)).mul ((contDiff_evalMatrix p).restrict_scalars ℝ).contDiffOn
  exact h.congr fun g hg => Set.indicator_of_mem hg _

theorem Kf_val (a b : Fin n) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (GlobalTheory.CompanionTheory.ModelS.Kf a b w).1 g = Eu true a b w.1 g - Eu false b a w.1 g := by
  simp only [GlobalTheory.CompanionTheory.ModelS.Kf, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
    GlobalTheory.CompanionTheory.ModelS.orderedCechToCatCochainsOne_apply_valueAtSubset _ _ _ hg, e2, LinearMap.neg_apply, Submodule.coe_neg, Pi.neg_apply,
    GlobalTheory.CompanionTheory.ModelS.liftOneFormsToCompatible_apply _ _ _ hg]
  ring

theorem Eu_val (s : Bool) (a b : Fin n) (f : Mat n → ℂ) (g : Mat n) :
    Eu s a b f g = (1 / 2 : ℂ) * (fderiv ℝ f g (g * Matrix.single a b 1) +
      (if s then -Complex.I else Complex.I) * fderiv ℝ f g (g * Matrix.single a b Complex.I)) := by
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem Kf_wf (e : Fin n → ℤ) (m : ℤ) (p : MvPolynomial (Fin n × Fin n) ℂ) (w : GlobalTheory.CompanionTheory.ModelS.SmF n)
    (hw : w.1 = wf e m p) (a b : Fin n) {g : Mat n} (hg : g ∈ GLs n) :
    (GlobalTheory.CompanionTheory.ModelS.Kf a b w).1 g =
      Qf e g * g.det ^ m * ((if a = b then (m : ℂ) else 0) * evP p g + evP (Tp a b p) g) := by
  set h : Mat n → ℂ := fun x => x.det ^ m * evP p x with hh
  set f : Mat n → ℂ := fun x => Qf e x * h x with hf
  have hEq : w.1 =ᶠ[nhds g] f := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with x hx
    rw [hw, wf, Set.indicator_of_mem hx]
    simp only [hf, hh, mul_assoc]
  have hfd : fderiv ℝ w.1 g = fderiv ℝ f g := hEq.fderiv_eq
  have hQd : DifferentiableAt ℝ (Qf e) g := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth (Qf_smooth e) hg
  have hhF : HasFDerivAt h (g.det ^ m • fderiv ℂ (evP p) g + evP p g • fderiv ℂ (fun x : Mat n => x.det ^ m) g) g :=
    (detz_diff m hg).hasFDerivAt.mul (differentiable_evalMatrix p g).hasFDerivAt
  have hhC : DifferentiableAt ℂ h g := hhF.differentiableAt
  have hhR : DifferentiableAt ℝ h g := hhC.restrictScalars ℝ
  have hL : fderiv ℝ f g = Qf e g • fderiv ℝ h g + h g • fderiv ℝ (Qf e) g :=
    (hQd.hasFDerivAt.mul hhR.hasFDerivAt).fderiv
  have hres : ∀ v, fderiv ℝ h g v = fderiv ℂ h g v := fun v =>
    DFunLike.congr_fun (hhC.hasFDerivAt.restrictScalars ℝ).fderiv v
  have hc1 : fderiv ℂ h g (g * Matrix.single a b 1) =
      g.det ^ m * evP (Tp a b p) g + evP p g * ((if a = b then (m : ℂ) else 0) * g.det ^ m) := by
    rw [hhF.fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, fderiv_evalMatrix_mul_single, detz_fderiv m hg]
  have hI : ∀ a b : Fin n, g * Matrix.single a b Complex.I = Complex.I • (g * Matrix.single a b 1) := fun a b => by
    rw [← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hIr : ∀ (ℓ : Mat n →L[ℂ] ℂ) (v : Mat n), ℓ (Complex.I • v) = Complex.I * ℓ v := fun ℓ v => by
    rw [map_smul, smul_eq_mul]
  have k1 : fderiv ℝ (Qf e) g (g * Matrix.single a b 1) - fderiv ℝ (Qf e) g (g * Matrix.single b a 1) = 0 := by
    have hX : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1 : Mat n)ᴴ = -(Matrix.single a b 1 - Matrix.single b a 1) := by
      simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
    have := Qf_kill e _ hX hg hQd
    rwa [Matrix.mul_sub, map_sub] at this
  have k2 : fderiv ℝ (Qf e) g (g * Matrix.single a b Complex.I) + fderiv ℝ (Qf e) g (g * Matrix.single b a Complex.I) = 0 := by
    have hX : (Matrix.single a b Complex.I + Matrix.single b a Complex.I : Mat n)ᴴ = -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
      have hn : ∀ a b : Fin n, (Matrix.single a b (-Complex.I) : Mat n) = -Matrix.single a b Complex.I := fun a b => by
        ext i j
        by_cases h1 : a = i ∧ b = j
        · obtain ⟨rfl, rfl⟩ := h1
          simp
        · simp [Matrix.single_apply, h1]
      simp [Matrix.conjTranspose_add, Matrix.conjTranspose_single, hn, add_comm]
    have := Qf_kill e _ hX hg hQd
    rwa [Matrix.mul_add, map_add] at this
  rw [Kf_val a b w hg, Eu_val, Eu_val, hfd, hL]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Complex.real_smul, hres, if_true, Bool.false_eq_true,
    if_false]
  rw [hI a b, hI b a, hIr, hIr]
  rw [← hI a b, ← hI b a]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [hc1]
  linear_combination (h g / 2) * k1 - (Complex.I * h g / 2) * k2 -
    (1 / 2) * Qf e g * (g.det ^ m * evP (Tp a b p) g + evP p g * ((if a = b then (m : ℂ) else 0) * g.det ^ m) + fderiv ℂ h g (g * Matrix.single b a 1)) * hI2

theorem muZ_antitone (lam : Fin n → ℤ) (hl : Antitone lam) (lev : Fin n → ℕ) (hm : Monotone lev) :
    Antitone (GlobalTheory.CompanionTheory.ModelS.muZ lam lev) := by
  intro a b hab
  unfold GlobalTheory.CompanionTheory.ModelS.muZ
  have h1 := hl hab
  have h2 : (univ.filter fun c => lev b < lev c).card ≤ (univ.filter fun c => lev a < lev c).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_of_le_of_lt (hm hab) hc
  have h3 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_of_lt_of_le hc (hm hab)
  omega

theorem dif_nonneg {v : Fin n → ℤ} (hv : Antitone v) (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    0 ≤ GlobalTheory.CompanionTheory.ModelS.dif v j := by
  unfold GlobalTheory.CompanionTheory.ModelS.dif
  rw [dif_pos hj]
  have : j ≤ ⟨j + 1, hj⟩ := Fin.mk_le_mk.2 (Nat.le_succ _)
  have := hv this
  omega

theorem lm_eq_det (j : Fin n) (hj : (j : ℕ) + 1 = n) (g : Mat n) : GlobalTheory.CompanionTheory.ModelS.lm j g = g.det := by
  have hb : Function.Bijective (GlobalTheory.CompanionTheory.ModelS.ini j) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨Fin.castLE_injective _, by simp [hj]⟩
  exact Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hb) g

theorem fRaw_factor (lam : Fin n → ℤ) (hl : Antitone lam) (lev : Fin n → ℕ) (hlev : IsLev lam lev) :
    ∃ (m : ℤ) (p : MvPolynomial (Fin n × Fin n) ℂ), ∀ g ∈ GLs n,
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev g =
        Qf (GlobalTheory.CompanionTheory.ModelS.dif (GlobalTheory.CompanionTheory.ModelS.yZ lam lev)) g * g.det ^ m * evP p g := by
  have hμ := muZ_antitone lam hl lev hlev.1
  rcases n with _ | k
  · refine ⟨0, 1, fun g hg => ?_⟩
    simp [GlobalTheory.CompanionTheory.ModelS.fRaw, Set.indicator_of_mem hg, Qf, evP]
  set μ := GlobalTheory.CompanionTheory.ModelS.muZ lam lev with hμd
  set x : Fin (k + 1) → ℕ := fun j => if j = Fin.last k then 0 else (GlobalTheory.CompanionTheory.ModelS.dif μ j).toNat with hx
  refine ⟨GlobalTheory.CompanionTheory.ModelS.dif μ (Fin.last k), ∏ j, minP (GlobalTheory.CompanionTheory.ModelS.ini j) ^ x j, fun g hg => ?_⟩
  have hev : evP (∏ j, minP (GlobalTheory.CompanionTheory.ModelS.ini j) ^ x j) g = ∏ j, GlobalTheory.CompanionTheory.ModelS.lm j g ^ x j := by
    have e : ∀ j, evP (minP (GlobalTheory.CompanionTheory.ModelS.ini j)) g = GlobalTheory.CompanionTheory.ModelS.lm j g := fun j => evalMatrix_minor _ g
    simp only [← e]
    simp only [evP, map_prod, map_pow]
  have hj : ∀ j, GlobalTheory.CompanionTheory.ModelS.lm j g ^ GlobalTheory.CompanionTheory.ModelS.dif μ j =
      (if j = Fin.last k then g.det ^ GlobalTheory.CompanionTheory.ModelS.dif μ (Fin.last k) else 1) * GlobalTheory.CompanionTheory.ModelS.lm j g ^ x j := by
    intro j
    by_cases h : j = Fin.last k
    · subst h
      simp [hx, lm_eq_det (Fin.last k) (by simp) g]
    · have hlt : (j : ℕ) + 1 < k + 1 := by
        have := Fin.val_lt_last h
        omega
      have h0 := dif_nonneg hμ j hlt
      simp only [h, if_false, one_mul, hx]
      rw [← zpow_natCast, Int.toNat_of_nonneg h0]
  have key : ∏ j, GlobalTheory.CompanionTheory.ModelS.lm j g ^ GlobalTheory.CompanionTheory.ModelS.dif μ j =
      g.det ^ GlobalTheory.CompanionTheory.ModelS.dif μ (Fin.last k) * ∏ j, GlobalTheory.CompanionTheory.ModelS.lm j g ^ x j := by
    rw [Finset.prod_congr rfl fun j _ => hj j, Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  rw [GlobalTheory.CompanionTheory.ModelS.fRaw, Set.indicator_of_mem hg, hev, Finset.prod_mul_distrib, key, Qf]
  ring

def wfL (e : Fin n → ℤ) (m : ℤ) : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] GlobalTheory.CompanionTheory.ModelS.SmF n where
  toFun q := ⟨wf e m q, wf_mem e m q⟩
  map_add' p q := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · simp [wf, Set.indicator_of_mem hg, evalPoints_add, mul_add]
    · simp [wf, Set.indicator_of_notMem hg]
  map_smul' c q := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · simp only [Submodule.coe_smul, Pi.smul_apply, wf, Set.indicator_of_mem hg, evalEmbedding_smul, RingHom.id_apply,
        smul_eq_mul]
      ring
    · simp [wf, Set.indicator_of_notMem hg]

theorem Tp_mem (a b : Fin n) (d : ℕ) {q : MvPolynomial (Fin n × Fin n) ℂ}
    (hq : q ∈ MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ d) :
    Tp a b q ∈ MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ d := by
  have hN := (MvPolynomial.mem_restrictTotalDegree _ _ _).1 hq
  simp only [Tp, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ((GlobalTheory.LowStable.X_mul_pderiv_totalDegree_le _ _ q).trans hN)

end GlobalTheory.CompanionTheory.ModelS.FFin
