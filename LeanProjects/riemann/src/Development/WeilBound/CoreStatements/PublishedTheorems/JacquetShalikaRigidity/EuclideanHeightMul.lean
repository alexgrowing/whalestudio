import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace EuclideanHeightMul

open GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem euclid_add {F : Type*} [NormedField F] {n : ℕ} (y z : Fin n → F) :
    Reduction.euclidNorm (y + z) ≤ Reduction.euclidNorm y + Reduction.euclidNorm z := by
  have h : ∀ x : Fin n → F, Reduction.euclidNorm x = ‖(WithLp.toLp 2 x : PiLp 2 (fun _ : Fin n => F))‖ := by
    intro x; rw [PiLp.norm_eq_of_L2]; rfl
  rw [h, h, h, WithLp.toLp_add]
  exact norm_add_le _ _

theorem euclid_vecMul_near {F : Type*} [NormedField F] {n : ℕ} {M : Matrix (Fin n) (Fin n) F} {m : ℝ}
    (hm : 0 ≤ m) (hM : ∀ i j, ‖(M - 1) i j‖ ≤ m) (z : Fin n → F) :
    Reduction.euclidNorm (z ᵥ* M) ≤ (1 + √n * (n * m)) * Reduction.euclidNorm z := by
  have e : z ᵥ* M = z + z ᵥ* (M - 1) := by rw [Matrix.vecMul_sub, Matrix.vecMul_one]; abel
  rw [e]
  refine (euclid_add _ _).trans ?_
  have := Reduction.euclidNorm_vecMul_le hm hM z
  linarith

def Vn (m : ℝ) : Set (GA E k) :=
  {c | (∀ w : InfinitePlace E, ∀ i j,
      ‖((Reduction.infAt w c : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ < m) ∧
    ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 E))) →
      Reduction.finAt v c ∈ GLnLocal.integralGL (v.adicCompletion E) k}

theorem Vn_mem {m : ℝ} (hm : 0 < m) : Vn (E := E) (k := k) m ∈ 𝓝 (1 : GA E k) := by
  have hinf : ∀ᶠ c in 𝓝 (1 : GA E k), ∀ w : InfinitePlace E, ∀ i j,
      ‖((Reduction.infAt w c : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ < m := by
    refine Filter.eventually_all.2 fun w => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun c : GA E k =>
        ‖((Reduction.infAt w c : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ := by
      simp only [Matrix.sub_apply]
      exact (((Reduction.continuous_GL_apply i j).comp (Reduction.continuous_infAt w)).sub continuous_const).norm
    have h1 : ‖((Reduction.infAt w (1 : GA E k) : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ = 0 := by
      simp [Reduction.infAt]
    exact hc.continuousAt.eventually_lt continuousAt_const (by rw [h1]; exact hm)
  have hfin := (Reduction.isOpen_setOf_forall_not_mem_imp (K := E) (n := k) ∅).mem_nhds
    (fun v _ => by
      have h1 : Reduction.finAt v (1 : GA E k) = 1 := by
        have h := Reduction.finAt_mul (K := E) (n := k) v 1 1
        rw [mul_one] at h
        exact left_eq_mul.1 h
      rw [h1]; exact Subgroup.one_mem _)
  filter_upwards [hinf, hfin] with c h1 h2
  exact ⟨h1, h2⟩

theorem height_mul_le {m : ℝ} (hm : 0 ≤ m) {c : GA E k} (hc : c ∈ Vn m) (g : GA E k) {ξ : Fin k → E}
    (hξ : ξ ≠ 0) : Reduction.height (g * c) ξ ≤
      (∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult) * Reduction.height g ξ := by
  have hy := Reduction.hasFiniteContent_height g hξ
  have e : Reduction.height (g * c) ξ = Reduction.adelicNorm
      ((Reduction.ratVec ξ ᵥ* (g : Matrix (Fin k) (Fin k) (Ad E))) ᵥ* (c : Matrix (Fin k) (Fin k) (Ad E))) := by
    rw [Reduction.height, Units.val_mul, ← Matrix.vecMul_vecMul]
  rw [e, Reduction.height]
  have := Reduction.adelicNorm_le_of_local (hy.vecMul c) hy (fun _ => 1 + √k * (k * m)) (fun _ => 1) ∅
    (fun w => ?_) (fun _ _ => rfl) (fun v => ?_)
  · simpa only [Finset.prod_empty, mul_one] using this
  · rw [Reduction.infComp_vecMul_GL]
    exact euclid_vecMul_near hm (fun i j => (hc.1 w i j).le) _
  · rw [Reduction.finComp_vecMul_GL, Reduction.norm_vecMul_integralGL v (hc.2 v (Finset.notMem_empty v)), one_mul]

theorem exists_m {s : ℝ} (hs : 1 < s) :
    ∃ m : ℝ, 0 < m ∧ (∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult) ≤ s := by
  have hcont : Continuous fun m : ℝ => ∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult := by
    fun_prop
  have hev : ∀ᶠ m in 𝓝 (0 : ℝ), (∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult) < s :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hs)
  obtain ⟨m, hm, h⟩ := hev.exists_gt
  exact ⟨m, hm, h.le⟩

end EuclideanHeightMul

namespace EuclideanHeightMul

open GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem ht_mul_le (hDpos : ∀ g : GA E k, 0 < Dt g) (hDmul : ∀ g h : GA E k, Dt (g * h) = Dt g * Dt h)
    (hDcont : Continuous (Dt : GA E k → ℝ)) {r : ℝ} (hr : 1 < r) :
    ∃ U ∈ 𝓝 (1 : GA E k), ∀ c ∈ U, ∀ g ξ, ξ ≠ 0 → ht (g * c) ξ ≤ r * ht g ξ := by
  have hs : 1 < √r := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one hr
  obtain ⟨m, hm, hprod⟩ := exists_m (E := E) (k := k) hs
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hDmul 1 1
    rw [mul_one] at h
    exact (mul_left_cancel₀ (hDpos 1).ne' (h.symm.trans (mul_one _).symm))
  have hcont : ContinuousAt (fun c : GA E k => (Dt c ^ (k : ℝ)⁻¹)⁻¹) 1 :=
    ((hDcont.rpow_const (fun _ => Or.inr (by positivity))).inv₀
      (fun c => (Real.rpow_pos_of_pos (hDpos c) _).ne')).continuousAt
  have hev : ∀ᶠ c in 𝓝 (1 : GA E k), (Dt c ^ (k : ℝ)⁻¹)⁻¹ < √r :=
    hcont.eventually_lt continuousAt_const (by simpa [hD1] using hs)
  refine ⟨{c | c ∈ Vn m ∧ (Dt c ^ (k : ℝ)⁻¹)⁻¹ < √r}, Filter.inter_mem (Vn_mem hm) hev, ?_⟩
  rintro c ⟨hc, hc2⟩ g ξ hξ
  have h1 := height_mul_le hm.le hc g hξ
  have hh0 : 0 ≤ Reduction.height g ξ := Reduction.height_nonneg _ _
  have ha : 0 < Dt g ^ (k : ℝ)⁻¹ := Real.rpow_pos_of_pos (hDpos g) _
  have hb : 0 < Dt c ^ (k : ℝ)⁻¹ := Real.rpow_pos_of_pos (hDpos c) _
  have hs0 : 0 ≤ √r := Real.sqrt_nonneg r
  unfold ht
  rw [hDmul, Real.mul_rpow (hDpos g).le (hDpos c).le]
  have h2 : Reduction.height (g * c) ξ ≤ √r * Reduction.height g ξ :=
    h1.trans (mul_le_mul_of_nonneg_right hprod hh0)
  calc Reduction.height (g * c) ξ / (Dt g ^ (k : ℝ)⁻¹ * Dt c ^ (k : ℝ)⁻¹)
      = Reduction.height (g * c) ξ * (Dt c ^ (k : ℝ)⁻¹)⁻¹ / Dt g ^ (k : ℝ)⁻¹ := by
        field_simp
    _ ≤ (√r * Reduction.height g ξ) * √r / Dt g ^ (k : ℝ)⁻¹ := by
        gcongr
    _ = (√r * √r) * (Reduction.height g ξ / Dt g ^ (k : ℝ)⁻¹) := by ring
    _ = r * (Reduction.height g ξ / Dt g ^ (k : ℝ)⁻¹) := by
        rw [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ r)]

theorem bdd (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ) (g : GA E k) :
    BddBelow (Set.range fun ξ : {ξ : Fin k → E // ξ ≠ 0} => ht g ξ.1) :=
  ⟨0, by rintro _ ⟨ξ, rfl⟩; exact (hpos g ξ.1 ξ.2).le⟩

theorem dmin_le (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ) (g : GA E k) {ξ : Fin k → E} (hξ : ξ ≠ 0) :
    dmin g ≤ ht g ξ :=
  ciInf_le (bdd hpos g) (⟨ξ, hξ⟩ : {ξ : Fin k → E // ξ ≠ 0})

theorem dmin_eq (hDpos : ∀ g : GA E k, 0 < Dt g) (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ)
    (hk : 1 ≤ k) (g : GA E k) : ∃ x : Fin k → E, x ≠ 0 ∧ dmin g = ht g x := by
  obtain ⟨x, hx, h⟩ := Reduction.exists_height_min (K := E) hk g
  have : Nonempty {ξ : Fin k → E // ξ ≠ 0} := ⟨⟨x, hx⟩⟩
  refine ⟨x, hx, le_antisymm (dmin_le hpos g hx) (le_ciInf fun ξ => ?_)⟩
  exact div_le_div_of_nonneg_right (h ξ.1 ξ.2) (Real.rpow_nonneg (hDpos g).le _)

theorem dmin_mul_le (hDpos : ∀ g : GA E k, 0 < Dt g) (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ)
    (hk : 1 ≤ k) {r : ℝ} {c : GA E k} (hc : ∀ g ξ, ξ ≠ 0 → ht (g * c) ξ ≤ r * ht g ξ) (g : GA E k) :
    dmin (g * c) ≤ r * dmin g := by
  obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk g
  rw [e]
  exact (dmin_le hpos _ hx).trans (hc g x hx)

end EuclideanHeightMul

open EuclideanHeightMul in
theorem firstCohomologyBound_of_boundaryBound : D0 → H0 → K1 := by
  intro hD hH E _ _ _ k hk
  obtain ⟨hDpos, hDmul, hDcont, -⟩ := hD E k
  obtain ⟨hpos, hrat, -, hcpt, -⟩ := hH E k
  have dpos : ∀ g : GA E k, 0 < dmin g := fun g => by
    obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk g
    rw [e]; exact hpos g x hx
  refine ⟨?_, dpos, fun g ξ hξ => dmin_le hpos g hξ, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g₀ => tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have hev : ∀ᶠ r in 𝓝 (1 : ℝ), r * a < dmin g₀ :=
        (continuous_id.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simpa using ha)
      obtain ⟨r, hr, hra⟩ := hev.exists_gt
      obtain ⟨U, hU, hUr⟩ := ht_mul_le hDpos hDmul hDcont hr
      have ht : Filter.Tendsto (fun g : GA E k => g⁻¹ * g₀) (𝓝 g₀) (𝓝 1) := by
        have h : Filter.Tendsto (fun g : GA E k => g⁻¹ * g₀) (𝓝 g₀) (𝓝 (g₀⁻¹ * g₀)) :=
          (continuous_inv.mul continuous_const).tendsto g₀
        rwa [inv_mul_cancel] at h
      filter_upwards [ht hU] with g hg
      have h := dmin_mul_le hDpos hpos hk (hUr _ hg) g
      rw [mul_inv_cancel_left] at h
      have : r * a < r * dmin g := by linarith
      exact lt_of_mul_lt_mul_left this (by linarith)
    · have hev : ∀ᶠ r in 𝓝 (1 : ℝ), r * dmin g₀ < b :=
        (continuous_id.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simpa using hb)
      obtain ⟨r, hr, hrb⟩ := hev.exists_gt
      obtain ⟨U, hU, hUr⟩ := ht_mul_le hDpos hDmul hDcont hr
      have ht : Filter.Tendsto (fun g : GA E k => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
        have h : Filter.Tendsto (fun g : GA E k => g₀⁻¹ * g) (𝓝 g₀) (𝓝 (g₀⁻¹ * g₀)) :=
          (continuous_const.mul continuous_id).tendsto g₀
        rwa [inv_mul_cancel] at h
      filter_upwards [ht hU] with g hg
      have h := dmin_mul_le hDpos hpos hk (hUr _ hg) g₀
      rw [mul_inv_cancel_left] at h
      linarith
  · have hge : ∀ (γ : GL (Fin k) E) (g : GA E k), dmin g ≤ dmin (ratGL E k γ * g) := by
      intro γ g
      obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk (ratGL E k γ * g)
      rw [e, hrat]
      refine dmin_le hpos g fun h0 => hx ?_
      have := congrArg (· ᵥ* (γ⁻¹ : GL (Fin k) E).val) h0
      simpa [Matrix.vecMul_vecMul] using this
    intro γ g
    refine le_antisymm ?_ (hge γ g)
    have := hge γ⁻¹ (ratGL E k γ * g)
    rwa [map_inv, inv_mul_cancel_left] at this
  · intro C hC
    obtain ⟨B, hB⟩ := hcpt C hC
    refine ⟨max B 1, le_max_right _ _, fun c hc g => ?_⟩
    exact dmin_mul_le hDpos hpos hk (fun g ξ hξ =>
      (hB c hc g ξ hξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos g ξ hξ).le)) g
  · intro f hf M
    obtain ⟨C0, h0⟩ := hf 0
    obtain ⟨C1, h1⟩ := hf M
    refine ⟨max C0 C1, fun g => ?_⟩
    obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk g
    have a := h0 g x hx
    have b := h1 g x hx
    rw [pow_zero, mul_one] at a
    rw [← e] at b
    unfold wt
    by_cases hd : dmin g ≤ 1
    · rw [min_eq_right hd]
      exact b.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (dpos g).le M))
    · rw [min_eq_left (le_of_not_ge hd), one_pow, mul_one]
      exact a.trans (le_max_left _ _)

end PositivityTheory.AdelicQuotientData

end
