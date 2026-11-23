import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivDeterminantPowerCornerInt

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

theorem analyticAt_determinant_power_zero_int (N : ℕ) (t : ℤ) : AnalyticAt ℂ (H N t) 0 := analyticAt_H N t 0 (by simp)

theorem analyticAt_fderiv_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (G : F → ℂ) (x v : F) (hG : AnalyticAt ℂ G x) : AnalyticAt ℂ (fun y => fderiv ℂ G y v) x := by
  have h2 : AnalyticAt ℂ (fun L : F →L[ℂ] ℂ => L v) (fderiv ℂ G x) :=
    (ContinuousLinearMap.apply ℂ ℂ v).analyticAt _
  exact h2.comp hG.fderiv

theorem ev_piF (N : ℕ) : ∀ᶠ X in 𝓝 (0 : Matrix (Fin N) (Fin (N + 1)) ℂ), (1 + piF X).det ≠ 0 := by
  have hc : Continuous fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => (1 + piF X).det := by
    unfold piF
    fun_prop
  have hz : piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ) = 0 := by
    ext k l
    simp [piF]
  have h0 : (1 + piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)).det ≠ 0 := by
    simp [hz]
  exact hc.continuousAt.eventually_ne h0

theorem iconst_mul {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (G : F → ℂ) (x : F) (a : ℂ)
    (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin n → F) :
    iteratedFDeriv ℂ n (fun y => a * G y) x u = a * iteratedFDeriv ℂ n G x u := by
  have h := iteratedFDeriv_const_smul_apply' (a := a) (i := n) (hG.contDiffAt (n := n))
  simp only [smul_eq_mul] at h
  rw [h, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

theorem icompL {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (G : F → ℂ) (φ : E → F) (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hsmul : ∀ (c : ℂ) a, φ (c • a) = c • φ a)
    (x : E) (y : F) (hxy : φ x = y) (hG : AnalyticAt ℂ G y) (n : ℕ) (u : Fin n → E)
    (v : Fin n → F) (huv : ∀ i, φ (u i) = v i) :
    iteratedFDeriv ℂ n (G ∘ φ) x u = iteratedFDeriv ℂ n G y v := by
  let Lℓ : E →ₗ[ℂ] F := { toFun := φ, map_add' := hadd, map_smul' := hsmul }
  let L : E →L[ℂ] F := LinearMap.toContinuousLinearMap Lℓ
  have hL : ∀ z, L z = φ z := fun z => rfl
  obtain ⟨U, hUP, hUo, hyU⟩ := eventually_nhds_iff.1 hG.eventually_analyticAt
  have hU : ContDiffOn ℂ n G U := fun z hz => (hUP z hz).contDiffAt.contDiffWithinAt
  have hxU : L x ∈ U := by rw [hL, hxy]; exact hyU
  have hpre : IsOpen (L ⁻¹' U) := hUo.preimage L.continuous
  have key := L.iteratedFDerivWithin_comp_right hU hUo.uniqueDiffOn hpre.uniqueDiffOn hxU
    (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpre (show x ∈ L ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hUo hxU] at key
  have hcomp : G ∘ φ = G ∘ L := rfl
  rw [hcomp, key, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  show iteratedFDeriv ℂ n G (φ x) (fun i => φ (u i)) = _
  rw [hxy]
  congr 1
  funext i
  exact huv i

theorem phiF_add (a b : Matrix (Fin N) (Fin (N + 1)) ℂ) : phiF (a + b) = phiF a + phiF b := by
  ext i j
  cases i using Fin.cases <;> simp [phiF_zero_row, phiF_succ_row]

theorem phiF_smul (c : ℂ) (a : Matrix (Fin N) (Fin (N + 1)) ℂ) : phiF (c • a) = c • phiF a := by
  ext i j
  cases i using Fin.cases <;> simp [phiF_zero_row, phiF_succ_row]

theorem piF_add (a b : Matrix (Fin N) (Fin (N + 1)) ℂ) : piF (a + b) = piF a + piF b := by
  ext i j; rfl

theorem piF_smul (c : ℂ) (a : Matrix (Fin N) (Fin (N + 1)) ℂ) : piF (c • a) = c • piF a := by
  ext i j; rfl

theorem phiF_zero : phiF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ) = 0 := by
  ext i j
  cases i using Fin.cases <;> simp [phiF_zero_row, phiF_succ_row]

theorem piF_zero : piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ) = 0 := by
  ext i j; rfl

theorem iterated_derivative_corner_case_int (t : ℤ) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) 0
        (fun k => Matrix.single k.succ (e k).succ 1) =
      (t : ℂ) * iteratedFDeriv ℂ N (H N t) 0 (fun k => Matrix.single k (e k) 1) := by
  have hA : AnalyticAt ℂ (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int (N + 1) t)
  have h1 := icompL (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) phiF phiF_add
    phiF_smul 0 0 phiF_zero hA N (fun k => Matrix.single k (e k).succ 1)
    (fun k => Matrix.single k.succ (e k).succ 1) (fun k => phiF_single k (e k).succ)
  rw [← h1]
  have hpi : piF = ⇑(piL N) := funext fun X => (piL_apply X).symm
  have hB : AnalyticAt ℂ (H N t ∘ piF) 0 := by
    rw [hpi]
    refine (analyticAt_H N t (piL N 0) ?_).comp ((piL N).analyticAt 0)
    rw [piL_apply, piF_zero, add_zero, det_one]
    exact one_ne_zero
  have hev : (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) ∘ phiF =ᶠ[𝓝 0]
      fun X => (t : ℂ) * (H N t ∘ piF) X := by
    filter_upwards [ev_piF N] with X hX
    exact fderiv_determinant_power_corner_int t X hX
  rw [(Filter.EventuallyEq.iteratedFDeriv ℂ hev N).eq_of_nhds, iconst_mul _ 0 _ hB]
  congr 1
  exact icompL (H N t) piF piF_add piF_smul 0 0 piF_zero (analyticAt_determinant_power_zero_int N t) N _ _
    (fun k => piF_single_succ k (e k))

end PositivityTheory.Rg.Sw.LVs.CK
