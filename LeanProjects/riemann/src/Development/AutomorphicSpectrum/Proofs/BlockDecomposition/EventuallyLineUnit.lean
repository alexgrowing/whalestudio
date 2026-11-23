import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import Formalism.GelfandTransference.HadamardGelfand.Highest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot

noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def XA (lam : Fin n → ℤ) (B : Mat n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  fun i j => fderiv ℂ (fun x : Mat n => Rm lam x i j) 1 B

def Xu (lam : Fin n → ℤ) (a b : Fin n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  XA lam (Matrix.single a b 1)

def HolRm (lam : Fin n → ℤ) : Prop :=
  ∀ (i j : Jd n lam), ∀ g ∈ GLs n, DifferentiableAt ℂ (fun x : Mat n => Rm lam x i j) g

theorem XA_add (lam : Fin n → ℤ) (B B' : Mat n) : XA lam (B + B') = XA lam B + XA lam B' := by
  ext i j; simp [XA]

theorem XA_smul (lam : Fin n → ℤ) (c : ℂ) (B : Mat n) : XA lam (c • B) = c • XA lam B := by
  ext i j; simp [XA]

theorem XA_sum (lam : Fin n → ℤ) {ι : Type} (s : Finset ι) (B : ι → Mat n) :
    XA lam (∑ r ∈ s, B r) = ∑ r ∈ s, XA lam (B r) := by
  ext i j; simp [XA, Matrix.sum_apply]

theorem Rm_of_unit (lam : Fin n → ℤ) {x : Mat n} (h : IsUnit x.det) :
    Rm lam x = LinearMap.toMatrix (wb lam) (wb lam) (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h)) := by
  rw [Rm, dif_pos h]

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : Mat n) = 1 := by
  have h : IsUnit (1 : Mat n).det := by simp
  rw [Rm_of_unit lam h]
  have e : Matrix.nonsingInvUnit (1 : Mat n) h = 1 := Units.ext rfl
  rw [e, map_one]
  exact LinearMap.toMatrix_one _

theorem Rm_mul (lam : Fin n → ℤ) {x y : Mat n} (hx : IsUnit x.det) (hy : IsUnit y.det) :
    Rm lam (x * y) = Rm lam x * Rm lam y := by
  have h : IsUnit (x * y).det := by rw [Matrix.det_mul]; exact hx.mul hy
  rw [Rm_of_unit lam h, Rm_of_unit lam hx, Rm_of_unit lam hy]
  have e : Matrix.nonsingInvUnit (x * y) h = Matrix.nonsingInvUnit x hx * Matrix.nonsingInvUnit y hy := Units.ext rfl
  rw [e, map_mul]
  exact LinearMap.toMatrix_mul _ _ _

theorem isUnit_det_of_mem {g : Mat n} (hg : g ∈ GLs n) : IsUnit g.det := isUnit_iff_ne_zero.2 hg

theorem mem_GLs_of_isUnit {g : Mat n} (hg : IsUnit g.det) : g ∈ GLs n := hg.ne_zero

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by simp [GLs]

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne_fun this continuous_const

theorem hasDerivAt_line {lam : Fin n → ℤ} (hD : HolRm lam) (B : Mat n) (i j : Jd n lam) :
    HasDerivAt (fun t : ℂ => Rm lam (1 + t • B) i j) (XA lam B i j) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => (1 : Mat n) + t • B) B 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const B).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have h2 := (hD i j 1 one_mem_GLs).hasFDerivAt
  exact h2.comp_hasDerivAt_of_eq (0 : ℂ) h1 (by simp)

theorem eventually_line_unit (B : Mat n) : ∀ᶠ t : ℂ in 𝓝 0, IsUnit ((1 : Mat n) + t • B).det := by
  have hc : Continuous fun t : ℂ => (1 : Mat n) + t • B := continuous_const.add (continuous_id.smul continuous_const)
  have : ∀ᶠ t : ℂ in 𝓝 0, (1 : Mat n) + t • B ∈ GLs n :=
    hc.continuousAt.eventually_mem (isOpen_GLs.mem_nhds (by simpa using one_mem_GLs))
  exact this.mono fun t ht => isUnit_det_of_mem ht

theorem conj_XA {lam : Fin n → ℤ} (hD : HolRm lam) {x B B' : Mat n} (hx : IsUnit x.det) (h : x * B = B' * x) :
    Rm lam x * XA lam B = XA lam B' * Rm lam x := by
  ext i j
  have hev : ∀ᶠ t : ℂ in 𝓝 0, ∑ k, Rm lam x i k * Rm lam (1 + t • B) k j = ∑ k, Rm lam (1 + t • B') i k * Rm lam x k j := by
    filter_upwards [eventually_line_unit B, eventually_line_unit B'] with t h1 h2
    have e : x * (1 + t • B) = (1 + t • B') * x := by
      simp only [mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, h]
    have := Rm_mul lam hx h1
    rw [e, Rm_mul lam h2 hx] at this
    have := congrFun (congrFun this i) j
    simpa [Matrix.mul_apply] using this.symm
  have hL : HasDerivAt (fun t : ℂ => ∑ k, Rm lam x i k * Rm lam (1 + t • B) k j)
      (∑ k, Rm lam x i k * XA lam B k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B k j).const_mul _
  have hR : HasDerivAt (fun t : ℂ => ∑ k, Rm lam (1 + t • B') i k * Rm lam x k j)
      (∑ k, XA lam B' i k * Rm lam x k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B' i k).mul_const _
  simpa [Matrix.mul_apply] using (hL.congr_of_eventuallyEq (hev.mono fun t ht => ht.symm)).unique hR |>.symm ▸ rfl

theorem fderiv_Rm {lam : Fin n → ℤ} (hD : HolRm lam) {g : Mat n} (hg : g ∈ GLs n) (B : Mat n) (i j : Jd n lam) :
    fderiv ℂ (fun x : Mat n => Rm lam x i j) g (g * B) = (Rm lam g * XA lam B) i j := by
  have hu := isUnit_det_of_mem hg
  have hline : HasDerivAt (fun t : ℂ => g + t • (g * B)) (g * B) 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const (g * B)).const_add g
    rw [one_smul] at h
    exact h
  have h1 : HasDerivAt (fun t : ℂ => Rm lam (g + t • (g * B)) i j)
      (fderiv ℂ (fun x : Mat n => Rm lam x i j) g (g * B)) 0 :=
    (hD i j g hg).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  have h2 : HasDerivAt (fun t : ℂ => ∑ k, Rm lam g i k * Rm lam (1 + t • B) k j)
      (∑ k, Rm lam g i k * XA lam B k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B k j).const_mul _
  have hev : ∀ᶠ t : ℂ in 𝓝 0, Rm lam (g + t • (g * B)) i j = ∑ k, Rm lam g i k * Rm lam (1 + t • B) k j := by
    filter_upwards [eventually_line_unit B] with t ht
    have e : g + t • (g * B) = g * (1 + t • B) := by
      simp only [mul_add, mul_one, Matrix.mul_smul]
    rw [e, Rm_mul lam hu ht, Matrix.mul_apply]
  simpa [Matrix.mul_apply] using h1.unique (h2.congr_of_eventuallyEq hev)

end GlobalTheory.CompanionTheory.RmHol
