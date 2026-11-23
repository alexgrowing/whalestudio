import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.RowS

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows.CornerBlockIndex

variable {ι : Type} {a m : ℕ}

variable [Fintype ι]

def betL (l : (ι → ℂ) →L[ℝ] ℝ) (x : V ι a m) : V ι a m →ₗ[ℝ] ℝ where
  toFun y := l (∑ t, x t * y t)
  map_add' y y' := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.mul_sum]

def bet (l : (ι → ℂ) →L[ℝ] ℝ) : V ι a m →L[ℝ] V ι a m →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => LinearMap.toContinuousLinearMap (betL l x)
      map_add' := fun x x' => by ext y; simp [betL, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by ext y; simp [betL, Finset.mul_sum] }

theorem bet_apply (l : (ι → ℂ) →L[ℝ] ℝ) (x y : V ι a m) : bet l x y = l (∑ t, x t * y t) := by
  rfl

theorem bet_nondeg (hm : m + 1 < a) {χ : AddChar (ι → ℂ) ℂ} (hχ : ∀ z, (∀ w, χ (z * w) = 1) → z = 0)
    {l : (ι → ℂ) →L[ℝ] ℝ} (hl : ∀ z, χ z = Complex.exp ((l z : ℝ) * Complex.I)) :
    ∀ y : V ι a m, (∀ x, bet l x y = 0) → y = 0 := by
  intro y hy
  funext t
  show y t = 0
  apply hχ
  intro w
  have h1 := hy (Pi.single t w)
  rw [bet_apply] at h1
  have hs : ∑ s, (Pi.single t w : V ι a m) s * y s = y t * w := by
    rw [Finset.sum_eq_single t]
    · simp [mul_comm]
    · intro s _ hs
      simp [Pi.single_apply, hs]
    · simp
  rw [hs] at h1
  rw [hl, h1]
  simp

def Lb (_hm : m + 1 < a) : V ι a m →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Matrix.of.symm (posM Subtype.val y)
      map_add' := fun y y' => by rw [posM_add]; rfl
      map_smul' := fun c y => by
        ext i j k
        simp only [posM, Matrix.sum_apply, Matrix.single_apply, Pi.smul_apply, Matrix.of_symm_apply]
        rw [Finset.sum_apply, Finset.sum_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs <;> simp }

theorem blkU_val (hm : m + 1 < a) (y : V ι a m) : (blkU y : GL (Fin a) (ι → ℂ)).val = 1 + Matrix.of (Lb hm y) := by
  rfl

theorem blkU_inv_val (hm : m + 1 < a) (y : V ι a m) :
    (blkU y : GL (Fin a) (ι → ℂ))⁻¹.val = 1 - Matrix.of (Lb hm y) := by
  rfl

theorem lastE_eq {R : Type} [CommRing R] (hm : m + 1 < a) (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → R) :
    lastE (m + 1) y = y (t0 hm) := by
  unfold lastE
  rw [Finset.sum_eq_single (t0 hm)]
  · simp [t0, ix, mm]
  · intro t _ ht
    rw [if_neg]
    intro h1
    apply ht
    obtain ⟨⟨i, k⟩, h1', h2', h3'⟩ := t
    simp only at h1 h1' h2' h3'
    apply Subtype.ext
    simp only [t0, ix, mm]
    ext <;> simp <;> omega
  · simp

end PositivityTheory.jumpWindows.CornerBlockIndex

end
