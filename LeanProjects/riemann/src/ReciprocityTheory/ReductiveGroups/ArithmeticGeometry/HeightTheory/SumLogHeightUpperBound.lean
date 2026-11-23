import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UpSiegel

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem upB_nonneg (hd : d.AxH 𝒜) : 0 ≤ d.upB := by
  have h1 := hd.P_ge.2.2.2.1
  have h2 := hd.size_L
  have h3 : 0 ≤ Real.log (d.N + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos _)
  have h4 : 0 ≤ max 0 d.laW := le_max_left _ _
  unfold upB
  nlinarith

theorem delc_le_del (c : ι) : d.delc c ≤ d.del :=
  Finset.single_le_sum (f := d.delc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

theorem up_comp (hd : d.AxH 𝒜) (h : d.S1) (hLAM : d.HtLAM) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) (c : ι) :
    ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ (d.D + 2) * d.delc c * d.upB := by
  have hB := d.upB_nonneg hd
  by_cases hpos : ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ 0
  · exact hpos.trans (by positivity)
  replace hpos := not_le.mp hpos
  obtain ⟨F1, m, deF, hm, hdeF, hmd, hirr, hx, hu, hle, hker⟩ := d.irreducible_factor_height_bound hd h F hF c hpos
  have hcd := d.delc_le_del c
  have hdel : 1 ≤ d.del := by
    have : 1 ≤ m * deF := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT0 : 0 < hT F1 := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have : (m : ℝ) * hT F1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
    linarith
  have hu' : UDegLE ((d.D + 1) * d.del) F1 := fun s hs =>
    (hu s hs).trans (Nat.mul_le_mul_left _ hcd)
  obtain ⟨Q, hQx, hQu, hQ, hS⟩ := d.up_siegel hd F1 deF hdeF
    ((Nat.le_mul_of_pos_left deF (by omega)).trans (hmd.trans hcd)) hirr hx hu' hT0
  obtain ⟨g, hg, hgc, hC⟩ := d.up_cauchy hd hdel c F1 deF hx hker Q hQx hQu hQ
  have hL := hLAM c g hg hgc
  have hN := d.up_count hd hdel
  have hn : (0 : ℝ) < d.n96 := by
    have : 0 < d.n96 := by
      unfold n96
      have : 0 < (d.N + 1) := Nat.succ_pos _
      positivity
    exact_mod_cast this
  have hDF : (0 : ℝ) < (d.D + 2) * deF := by
    have : (1 : ℝ) ≤ deF := by exact_mod_cast hdeF
    positivity
  have hlaw : d.laW ≤ max 0 d.laW := le_max_right _ _

  have key : d.n96 * hT F1 / ((d.D + 2) * deF) ≤ d.n96 * d.upB := by
    unfold upB
    nlinarith
  have key2 : hT F1 ≤ (d.D + 2) * deF * d.upB := by
    rw [div_le_iff₀ hDF] at key
    have : d.n96 * hT F1 ≤ d.n96 * ((d.D + 2) * deF * d.upB) := by nlinarith
    exact le_of_mul_le_mul_left this hn
  have hmdR : (m : ℝ) * deF ≤ d.delc c := by exact_mod_cast hmd
  calc ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ m * hT F1 := hle
    _ ≤ m * ((d.D + 2) * deF * d.upB) := by gcongr
    _ = (d.D + 2) * (m * deF) * d.upB := by ring
    _ ≤ (d.D + 2) * d.delc c * d.upB := by gcongr

theorem sum_logHeight_upper_bound (hd : d.AxH 𝒜) (h : d.S1) (hLAM : d.HtLAM) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) :
    ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤
      (d.D + 2) * d.del * (d.PP0' * d.wsize d.wL +
        max 0 (meanK fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j))) +
        Real.log (d.N + 1 : ℕ) + 1) := by
  calc ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ ∑ c, ((d.D : ℝ) + 2) * d.delc c * d.upB :=
        Finset.sum_le_sum fun c _ => d.up_comp hd h hLAM F hF c
    _ = ((d.D : ℝ) + 2) * d.del * d.upB := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        simp [Data.del, Nat.cast_sum]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
