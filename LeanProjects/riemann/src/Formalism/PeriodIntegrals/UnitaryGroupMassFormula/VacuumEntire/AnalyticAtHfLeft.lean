import Mathlib
import Formalism.PeriodIntegrals.VacEntire

noncomputable section

namespace PI.VacEntire.UnitaryGroupMassFormula

open PI.VacEntire

def coordL (ι : Type) [Fintype ι] (N N' : ℕ) (τ : ι) (i : Fin N') (j : Fin N) :
    (ι → Fin N' → Fin N → ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) j).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => Fin N' → Fin N → ℂ) τ))

theorem analyticAt_coord {ι : Type} [Fintype ι] {N N' : ℕ} (τ : ι) (i : Fin N') (j : Fin N)
    (c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (fun z : ι → Fin N' → Fin N → ℂ => z τ i j) c :=
  (coordL ι N N' τ i j).analyticAt c

theorem analyticAt_Hf_left {ι : Type} [Fintype ι] {N N' : ℕ} (A : ℝ)
    (x c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (fun z => Hf A z x) c := by
  unfold Hf
  refine AnalyticAt.div_const ?_
  refine Finset.analyticAt_fun_sum _ (fun τ _ => ?_)
  refine Finset.analyticAt_fun_sum _ (fun i _ => ?_)
  refine Finset.analyticAt_fun_sum _ (fun j _ => ?_)
  exact (analyticAt_coord τ i j c).mul analyticAt_const

theorem analyticAt_U {ι : Type} [Fintype ι] {N N' : ℕ} (A : ℝ)
    (x : ι → Fin N' → Fin N → ℂ) (G : (ι → Fin N' → Fin N → ℂ) → ℂ)
    (hG : AnalyticOnNhd ℂ G Set.univ) (c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (U A x G) c := by
  unfold U
  refine AnalyticAt.mul ?_ ?_
  · have hshift : AnalyticAt ℂ (fun z : ι → Fin N' → Fin N → ℂ => z + x) c :=
      analyticAt_id.add analyticAt_const
    exact (hG (c + x) (Set.mem_univ _)).comp (f := fun z => z + x) hshift
  · refine AnalyticAt.cexp' ?_
    exact (analyticAt_const.mul (analyticAt_Hf_left A x c)).sub analyticAt_const

theorem iopEntire : IopEntire := by
  intro ι _ N N' d A La₁ La₂ G hG c _
  by_cases h0 : (La₁.addSubgroupOf La₂).index = 0
  · have hfun : Iop d A La₁ La₂ G = fun _ => (0 : ℂ) := by
      funext z
      simp [Iop, h0]
    rw [hfun]
    exact analyticAt_const
  · have : Finite (La₂ ⧸ La₁.addSubgroupOf La₂) :=
      (AddSubgroup.index_ne_zero_iff_finite).1 h0
    let _ : Fintype (La₂ ⧸ La₁.addSubgroupOf La₂) := Fintype.ofFinite _
    have hfun : Iop d A La₁ La₂ G = fun z =>
        ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
          ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂,
            al d A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) *
              U A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) G z := by
      funext z
      simp only [Iop]
      rw [finsum_eq_sum_of_fintype]
    rw [hfun]
    refine analyticAt_const.mul ?_
    refine Finset.analyticAt_fun_sum _ (fun q _ => ?_)
    exact analyticAt_const.mul (analyticAt_U A _ G hG c)

def blockL (n : Type) [Fintype n] (N N' : ℕ) (i : Fin N') (j : Fin N) :
    (n → Fin N' → Fin N → ℂ) →L[ℂ] (n → ℂ) :=
  ContinuousLinearMap.pi fun τ => coordL n N N' τ i j

theorem tensEntire : TensEntire := by
  intro n _ θ N N' hθ c _
  unfold tensPow
  refine Finset.analyticAt_fun_prod _ (fun i _ => ?_)
  refine Finset.analyticAt_fun_prod _ (fun j _ => ?_)
  have he : (fun z : n → Fin N' → Fin N → ℂ => fun τ => z τ i j) = ⇑(blockL n N N' i j) := by
    funext z τ
    rfl
  have hb : AnalyticAt ℂ (fun z : n → Fin N' → Fin N → ℂ => fun τ => z τ i j) c := by
    rw [he]
    exact (blockL n N N' i j).analyticAt c
  exact (hθ _ (Set.mem_univ _)).comp hb

end PI.VacEntire.UnitaryGroupMassFormula
