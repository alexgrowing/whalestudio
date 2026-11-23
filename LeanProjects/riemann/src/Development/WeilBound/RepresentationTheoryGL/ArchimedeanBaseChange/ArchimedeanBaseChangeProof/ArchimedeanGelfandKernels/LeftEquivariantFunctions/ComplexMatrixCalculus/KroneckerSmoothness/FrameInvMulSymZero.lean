import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnChartInv

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.Cxh

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

theorem frame_inv_mul_sym_zero (hu : IsUnit (sqQ lam)) (hG : GamMul) (x : Mat n) :
    lefFr n lam x⁻¹ * lefS n lam 0 =
      cjL lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ rhoW lam x⁻¹) := by
  have hmul : ∀ A B : Matrix (Ix n lam) (Ix n lam) ℂ, cjL lam A * cjL lam B = cjL lam (A * B) := by
    intro A B
    have hc : clm lam (A * B) = clm lam A * clm lam B := map_mul Matrix.toEuclideanCLM A B
    have hi : Ring.inverse (sqQ lam) * sqQ lam = 1 := Ring.inverse_mul_cancel _ hu
    change sqQ lam * (clm lam A * Ring.inverse (sqQ lam)) * (sqQ lam * (clm lam B * Ring.inverse (sqQ lam))) =
      sqQ lam * (clm lam (A * B) * Ring.inverse (sqQ lam))
    rw [hc]
    simp only [mul_assoc]
    rw [← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), hi, one_mul]
  have h0 : lefS n lam 0 = cjL lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := by
    simp only [lefS, Complex.ofReal_zero, zero_smul]
  rw [h0, lefFr, fr0, hmul, ← Matrix.mul_kronecker_mul, ← (hG n).2, mul_zero, Matrix.mul_one]

theorem clm_entry (M : Matrix (Ix n lam) (Ix n lam) ℂ) (u : EV n lam) (r : Ix n lam) :
    (clm lam M u) r = ∑ c, M r c * u c := by
  have h : (clm lam M u).ofLp = M *ᵥ u.ofLp := by
    rw [clm, ← ContinuousLinearMap.coe_coe, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    rfl
  change (clm lam M u).ofLp r = _
  rw [h]
  rfl

theorem clm_apply' (M : Matrix (Ix n lam) (Ix n lam) ℂ) (u : EV n lam) :
    clm lam M u = ∑ i : Ix n lam × Ix n lam, (M i.1 i.2 * u i.2) • EuclideanSpace.single i.1 (1 : ℂ) := by
  rw [Fintype.sum_prod_type (f := fun i : Ix n lam × Ix n lam => (M i.1 i.2 * u i.2) • EuclideanSpace.single i.1 (1 : ℂ))]
  ext r
  rw [clm_entry]
  simp [Finset.sum_apply, EuclideanSpace.single_apply, Pi.single_apply]

theorem mem_GLs_inv' {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq] at hx ⊢
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hx

theorem mem_GLs_conjInv {x : Mat n} (hx : x ∈ GLs n) : (x⁻¹)ᴴ ∈ GLs n := by
  have h := mem_GLs_inv' hx
  simp only [GLs, Set.mem_setOf_eq] at h ⊢
  rw [Matrix.det_conjTranspose]
  exact star_ne_zero.2 h

theorem contDiff_conjT : ContDiff ℝ ∞ (fun y : Mat n => yᴴ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  exact Complex.conjCLE.contDiff.comp ((contDiff_apply ℝ ℂ i).comp (contDiff_apply ℝ (Fin n → ℂ) j))

theorem contDiffOn_theta : ContDiffOn ℝ ∞ (fun y : Mat n => (y⁻¹)ᴴ) (GLs n) :=
  contDiff_conjT.comp_contDiffOn GlobalTheory.CompanionTheory.MatInv.contDiffOn_inv

theorem contDiffOn_entry {J : Type} [Fintype J] [DecidableEq J] {f : Mat n → Matrix J J ℂ} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (a b : J) : ContDiffOn ℝ ∞ (fun x => (f x * (1 : Matrix J J ℂ) : Matrix J J ℂ) a b) (GLs n) := by
  simp only [Matrix.mul_one]
  exact ((contDiff_apply ℝ ℂ b).comp (contDiff_apply ℝ (J → ℂ) a)).comp_contDiffOn hf

end PositivityTheory.RgBcC.Cxh

namespace PositivityTheory.RgBcC

open Cxh
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option maxHeartbeats 800000 in
theorem eigOf : EigOf := by
  intro hAvg hG hRm hHol hAnti hProd hLoc n lam hlam w
  obtain ⟨hu, -, -, -, -⟩ := hAvg n lam
  obtain ⟨hR1, hRmul, hRc⟩ := hRm n lam
  let G0 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ := gamM (0 : Matrix (Md n) (Md n) ℂ)
  let hh : Ix n lam × Ix n lam → Mat n → ℂ := fun i x =>
    (Rm lam x * 1 : Matrix (Jd n lam) (Jd n lam) ℂ) i.2.2.1 i.1.2.1
  let aa : Ix n lam × Ix n lam → Mat n → ℂ := fun i x =>
    (Rm lam x⁻¹ᴴ * 1 : Matrix (Jd n lam) (Jd n lam) ℂ) i.2.2.2 i.1.2.2
  let vv : Ix n lam × Ix n lam → EV n lam := fun i =>
    (G0 i.1.1 i.2.1 * (Ring.inverse (sqQ lam) w) i.2) • sqQ lam (EuclideanSpace.single i.1 (1 : ℂ))
  have hE := hProd n (infOf lam) (Ix n lam × Ix n lam) (EV n lam) hh aa vv
    (fun i => contDiffOn_entry (f := Rm lam) hRc _ _)
    (fun i => contDiffOn_entry (f := fun x => Rm lam x⁻¹ᴴ)
      (hRc.comp contDiffOn_theta (fun x hx => mem_GLs_conjInv hx)) _ _)
    (fun i g hg => hHol n lam hlam 1 _ _ g hg)
    (fun i g hg => hAnti n lam hlam 1 _ _ g hg)
  refine hLoc n (infOf lam) (EV n lam) _ _ ?_ hE
  intro x hx
  have hdx : IsUnit (det x) := isUnit_iff_ne_zero.2 hx
  have hdx' : IsUnit (det x⁻¹) := isUnit_iff_ne_zero.2 (mem_GLs_inv' hx)
  have hinv : (Rm lam x⁻¹)⁻¹ = Rm lam x := by
    apply Matrix.inv_eq_left_inv
    rw [← hRmul x x⁻¹ hdx hdx', Matrix.mul_nonsing_inv x hdx, hR1]
  symm
  rw [← ContinuousLinearMap.mul_apply, frame_inv_mul_sym_zero hu hG]
  change (sqQ lam * (clm lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ rhoW lam x⁻¹) * Ring.inverse (sqQ lam))) w = _
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, clm_apply', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  simp only [vv, smul_smul]
  congr 1
  simp only [hh, aa, G0, rhoW, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_one, hinv]
  ring
