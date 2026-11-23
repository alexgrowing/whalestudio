import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

def fsProj (f : ℕ) : (Fin f → ℝ) → UnitAddTorus (Fin f) := fun t i => (t i : UnitAddCircle)

theorem fsProj_isOpenQuotientMap (f : ℕ) : IsOpenQuotientMap (fsProj f) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

theorem fsProj_eq {f : ℕ} (s t : Fin f → ℝ) (h : fsProj f s = fsProj f t) :
    ∃ n : Fin f → ℤ, t = s + fun i => (n i : ℝ) := by
  have hi : ∀ i, ∃ k : ℤ, t i = s i + k := by
    intro i
    have h1 : ((s i : ℝ) : UnitAddCircle) = (t i : UnitAddCircle) := congrFun h i
    have h2 : (((t i - s i : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h2
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose n hn using hi
  exact ⟨n, funext fun i => by simp [hn i]⟩

def fsFun {f : ℕ} (g : (Fin f → ℝ) → ℂ) : UnitAddTorus (Fin f) → ℂ :=
  fun θ => g (Function.surjInv (fsProj_isOpenQuotientMap f).surjective θ)

theorem fsFun_proj {f : ℕ} (g : (Fin f → ℝ) → ℂ)
    (hper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x) (t : Fin f → ℝ) :
    fsFun g (fsProj f t) = g t := by
  unfold fsFun
  set s := Function.surjInv (fsProj_isOpenQuotientMap f).surjective (fsProj f t)
  have hs : fsProj f s = fsProj f t := Function.surjInv_eq _ _
  obtain ⟨n, hn⟩ := fsProj_eq s t hs
  rw [hn, hper]

theorem fsFun_continuous {f : ℕ} (g : (Fin f → ℝ) → ℂ) (hg : Continuous g)
    (hper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x) :
    Continuous (fsFun g) := by
  rw [(fsProj_isOpenQuotientMap f).isQuotientMap.continuous_iff]
  have : fsFun g ∘ fsProj f = g := funext fun t => fsFun_proj g hper t
  rw [this]; exact hg

theorem fs_mFourier_proj {f : ℕ} (m : Fin f → ℤ) (t : Fin f → ℝ) :
    UnitAddTorus.mFourier m (fsProj f t) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ k, (m k : ℂ) * (t k : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fsProj, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem four_sum (f : ℕ) : FOURSumStatement f := by
  intro Ω h hΩ hh hper h0 hsum x
  set g : (Fin f → ℝ) → ℂ := fun x => h (fun k => (x k : ℂ)) with hgdef
  have hreal : ∀ y : Fin f → ℝ, (fun k => ((y k : ℝ) : ℂ)) ∈ tube f Ω := by
    intro y
    show (fun k => ((y k : ℝ) : ℂ).im) ∈ Ω
    have e : (fun k => (((y k : ℝ) : ℂ)).im) = 0 := by funext k; simp
    rw [e]; exact h0
  have hg : Continuous g := by
    have hc : Continuous (fun y : Fin f → ℝ => (fun k => ((y k : ℝ) : ℂ))) := by fun_prop
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hopen : IsOpen (tube f Ω) := hΩ.preimage (by fun_prop)
    exact ((hh _ (hreal y)).differentiableAt (hopen.mem_nhds (hreal y))).continuousAt.comp
      hc.continuousAt
  have hgper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x := by
    intro y n
    have := hper _ (hreal y) n
    simp only [hgdef]
    convert this using 2
    funext k
    simp
  let F : C(UnitAddTorus (Fin f), ℂ) := ⟨fsFun g, fsFun_continuous g hg hgper⟩
  have hcoef : ∀ ν, UnitAddTorus.mFourierCoeff F ν = fourCoeff h 0 ν := by
    intro ν
    rw [UnitAddTorus.mFourierCoeff_eq_integral _ ν 0, fourCoeff]
    have hset : ({x : Fin f → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin f → ℝ) i) ((0 : Fin f → ℝ) i + 1)}
        : Set (Fin f → ℝ)) = Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1) := by
      ext x; simp
    rw [hset]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have h1 : (fun i => ((t i : ℝ) : UnitAddCircle)) = fsProj f t := rfl
    have h2 : F (fsProj f t) = g t := fsFun_proj g hgper t
    beta_reduce
    rw [h1, h2, smul_eq_mul, fs_mFourier_proj]
    simp only [hgdef, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero, Pi.neg_apply, Int.cast_neg]
    rw [mul_comm]
    congr 2
    simp [Finset.sum_neg_distrib]
  have hs : Summable (UnitAddTorus.mFourierCoeff F) := by
    refine Summable.of_norm ?_
    simpa [hcoef] using hsum
  have := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (fsProj f x)
  simp only [hcoef, smul_eq_mul, fs_mFourier_proj] at this
  rw [show F (fsProj f x) = g x from fsFun_proj g hgper x] at this
  exact this

end

end ReciprocityTheory.L2DbarEstimates.Y
