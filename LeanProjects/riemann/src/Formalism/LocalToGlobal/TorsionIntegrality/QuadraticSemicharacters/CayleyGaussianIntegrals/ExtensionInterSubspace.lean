import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.KerPNonzero
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock

noncomputable section
open scoped BigOperators ComplexConjugate Nat

namespace Formalism.L2.Th1.H

section ExpSeries

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def powForm (l : V →L[ℂ] ℂ) (n : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin n => V) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap (fun _ => l)

theorem powForm_diag (l : V →L[ℂ] ℂ) (n : ℕ) (y : V) : powForm l n (fun _ => y) = l y ^ n := by
  simp [powForm]

theorem norm_powForm_le (l : V →L[ℂ] ℂ) (n : ℕ) : ‖powForm l n‖ ≤ ‖l‖ ^ n := by
  calc ‖powForm l n‖ ≤ ‖ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ‖ * ∏ _i : Fin n, ‖l‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖l‖ ^ n := by rw [ContinuousMultilinearMap.norm_mkPiAlgebra]; simp

def expTerm {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => V) ℂ :=
  (c x / (n ! : ℂ)) • powForm (l x) n

theorem norm_expTerm_le {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) :
    ‖expTerm c l n x‖ ≤ ‖c x‖ * (‖l x‖ ^ n / (n ! : ℝ)) := by
  have hn : ‖((n ! : ℕ) : ℂ)‖ = (n ! : ℝ) := by simp
  rw [expTerm, norm_smul, norm_div, hn]
  calc ‖c x‖ / (n ! : ℝ) * ‖powForm (l x) n‖ ≤ ‖c x‖ / (n ! : ℝ) * ‖l x‖ ^ n :=
        mul_le_mul_of_nonneg_left (norm_powForm_le _ _) (by positivity)
    _ = ‖c x‖ * (‖l x‖ ^ n / (n ! : ℝ)) := by ring

theorem norm_expTerm_mul_le {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) (r : ℝ)
    (hr : 0 ≤ r) : ‖expTerm c l n x‖ * r ^ n ≤ ‖c x‖ * Real.exp (r * ‖l x‖) := by
  calc ‖expTerm c l n x‖ * r ^ n ≤ ‖c x‖ * (‖l x‖ ^ n / (n ! : ℝ)) * r ^ n :=
        mul_le_mul_of_nonneg_right (norm_expTerm_le c l n x) (pow_nonneg hr n)
    _ = ‖c x‖ * ((r * ‖l x‖) ^ n / (n ! : ℝ)) := by ring
    _ ≤ ‖c x‖ * Real.exp (r * ‖l x‖) :=
        mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (by positivity) n) (norm_nonneg _)

theorem summable_norm_expTerm {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ)
    (h : ∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖l x‖)) (n : ℕ) :
    Summable fun x => ‖expTerm c l n x‖ := by
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (h 1)
  have := norm_expTerm_mul_le c l n x 1 zero_le_one
  simpa using this

def expFPS {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) : FormalMultilinearSeries ℂ V ℂ :=
  fun n => ∑' x, expTerm c l n x

theorem expFPS_radius {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ)
    (h : ∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖l x‖)) : (expFPS c l).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hb : ∀ n, ‖expFPS c l n‖ * (r : ℝ) ^ n ≤
      (∑' x, ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖)) * (1 / 2 : ℝ) ^ n := by
    intro n
    have hs := summable_norm_expTerm c l h n
    have h1 : ‖expFPS c l n‖ ≤ ∑' x, ‖expTerm c l n x‖ := norm_tsum_le_tsum_norm hs
    have h2 : ∀ x, ‖expTerm c l n x‖ * (r : ℝ) ^ n ≤
        ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖) * (1 / 2 : ℝ) ^ n := by
      intro x
      have h3 := norm_expTerm_mul_le c l n x (2 * (r : ℝ)) (by positivity)
      have e : ‖expTerm c l n x‖ * (r : ℝ) ^ n =
          ‖expTerm c l n x‖ * (2 * (r : ℝ)) ^ n * (1 / 2 : ℝ) ^ n := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    calc ‖expFPS c l n‖ * (r : ℝ) ^ n ≤ (∑' x, ‖expTerm c l n x‖) * (r : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ∑' x, ‖expTerm c l n x‖ * (r : ℝ) ^ n := tsum_mul_right.symm
      _ ≤ ∑' x, ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖) * (1 / 2 : ℝ) ^ n :=
          Summable.tsum_le_tsum h2 (hs.mul_right _) ((h (2 * (r : ℝ))).mul_right _)
      _ = (∑' x, ‖c x‖ * Real.exp ((2 * (r : ℝ)) * ‖l x‖)) * (1 / 2 : ℝ) ^ n := tsum_mul_right
  exact Summable.of_nonneg_of_le (fun n => by positivity) hb (summable_geometric_two.mul_left _)

theorem expFPS_hasSum {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ)
    (h : ∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖l x‖)) (y : V) :
    HasSum (fun n => expFPS c l n fun _ => y) (∑' x, c x * Complex.exp (l x y)) := by
  have hterm : ∀ n x, expTerm c l n x (fun _ => y) = c x * (l x y) ^ n / (n ! : ℂ) := by
    intro n x
    rw [expTerm, ContinuousMultilinearMap.smul_apply, powForm_diag, smul_eq_mul]
    ring
  have hev : ∀ n, expFPS c l n (fun _ => y) = ∑' x, c x * (l x y) ^ n / (n ! : ℂ) := by
    intro n
    have hs : HasSum (fun x => expTerm c l n x) (expFPS c l n) :=
      (Summable.of_norm (summable_norm_expTerm c l h n)).hasSum
    have h1 := hs.mapL (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => V) ℂ (fun _ => y))
    exact h1.tsum_eq.symm.trans (tsum_congr fun x => hterm n x)
  let g : X × ℕ → ℂ := fun p => c p.1 * (l p.1 y) ^ p.2 / (p.2 ! : ℂ)
  have hfib : ∀ x, HasSum (fun n => g (x, n)) (c x * Complex.exp (l x y)) := by
    intro x
    have h1 := NormedSpace.expSeries_div_hasSum_exp (l x y)
    rw [← Complex.exp_eq_exp_ℂ] at h1
    have h2 := h1.mul_left (c x)
    simpa [g, mul_div_assoc] using h2
  have hg : ∀ p : X × ℕ, ‖g p‖ = ‖c p.1‖ * (‖l p.1 y‖ ^ p.2 / (p.2 ! : ℝ)) := by
    intro p
    have hn : ‖((p.2 ! : ℕ) : ℂ)‖ = (p.2 ! : ℝ) := by simp
    simp only [g, norm_div, norm_mul, norm_pow, hn]
    ring
  have hnorm : Summable fun p : X × ℕ => ‖g p‖ := by
    simp_rw [hg]
    rw [summable_prod_of_nonneg (fun _ => by positivity)]
    refine ⟨fun x => by simpa using (Real.summable_pow_div_factorial ‖l x y‖).mul_left ‖c x‖, ?_⟩
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) (h ‖y‖)
    have he := NormedSpace.expSeries_div_hasSum_exp (‖l x y‖)
    rw [← Real.exp_eq_exp_ℝ] at he
    dsimp only
    rw [tsum_mul_left, he.tsum_eq]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have := (l x).le_opNorm y
    linarith [mul_comm ‖y‖ ‖l x‖]
  have hsum : Summable g := hnorm.of_norm
  have htot : HasSum g (∑' x, c x * Complex.exp (l x y)) := by
    have h1 := hsum.hasSum
    rw [hsum.tsum_prod' (fun x => (hfib x).summable)] at h1
    have e : (fun b => ∑' n, g (b, n)) = fun b => c b * Complex.exp (l b y) :=
      funext fun b => (hfib b).tsum_eq
    rw [e] at h1
    exact h1
  have hswap : HasSum (fun p : ℕ × X => g (p.2, p.1)) (∑' x, c x * Complex.exp (l x y)) :=
    (Equiv.prodComm ℕ X).hasSum_iff.2 htot
  have hfin := hswap.prod_fiberwise (fun n => (hswap.summable.prod_factor n).hasSum)
  convert hfin using 1
  funext n
  rw [hev n]

end ExpSeries

theorem exp_series_entire : ExpSeriesEntire := by
  unfold ExpSeriesEntire
  intro V _ _ X c ℓ h z _
  have hfps : HasFPowerSeriesOnBall (fun z => ∑' x, c x * Complex.exp (ℓ x z)) (expFPS c ℓ) 0 ⊤ :=
    { r_le := by rw [expFPS_radius c ℓ h]
      r_pos := ENNReal.zero_lt_top
      hasSum := fun {y} _ => by simpa using expFPS_hasSum c ℓ h y }
  exact hfps.analyticAt_of_mem (by simp)

section KerP

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def flipR (H : Sesq V) : V →ₗ[ℝ] (V →L[ℂ] ℂ) where
  toFun u := LinearMap.toContinuousLinearMap (H.flip u)
  map_add' := by intro a b; ext z; simp
  map_smul' := by
    intro r u
    ext z
    show H z (r • u) = r • H z u
    rw [← Complex.coe_smul r u, map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul, Complex.real_smul]

theorem exists_form_bound (H : Sesq V) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u, ‖LinearMap.toContinuousLinearMap (H.flip u)‖ ≤ K * ‖u‖ := by
  let T : V →L[ℝ] (V →L[ℂ] ℂ) := LinearMap.toContinuousLinearMap (flipR H)
  exact ⟨‖T‖, norm_nonneg _, fun u => T.le_opNorm u⟩

def kC (H : Sesq V) (α : V → ℂ) (w x : V) : ℂ :=
  α x * Complex.exp ((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)

def kL (H : Sesq V) (w x : V) : V →L[ℂ] ℂ :=
  (Real.pi : ℂ) • LinearMap.toContinuousLinearMap (H.flip (w - x))

theorem term_eq (H : Sesq V) (α : V → ℂ) (w x z : V) :
    α x * opU H x (kerK H w) z = kC H α w x * Complex.exp (kL H w x z) := by
  simp only [opU, kerK, kC, kL, ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
    LinearMap.flip_apply, smul_eq_mul, map_add, map_sub, LinearMap.add_apply]
  rw [mul_assoc]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [ContinuousLinearMap.sub_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.flip_apply]
  ring

theorem quad_bound (a b t : ℝ) (ha : 0 < a) : b * t ≤ a * t ^ 2 + b ^ 2 / (4 * a) := by
  rw [← sub_nonneg]
  have e : a * t ^ 2 + b ^ 2 / (4 * a) - b * t = (2 * a * t - b) ^ 2 / (4 * a) := by
    field_simp
    ring
  rw [e]
  positivity

theorem kernel_summable_bound (hS : LatGaussSummable) (hN : FormNorm) (H : Sesq V) (Λ : AddSubgroup V)
    (α : V → ℂ) (hH : IsHerm H) (hP : IsPosDef H) (hL : IsLat Λ) (hα : IsSemiChar H Λ α) (w : V) (r : ℝ) :
    Summable fun x : Λ => ‖kC H α w x‖ * Real.exp (r * ‖kL H w x‖) := by
  obtain ⟨c0, C0, hc0, hC0, hn⟩ := hN V H hH hP
  obtain ⟨K, hK0, hK⟩ := exists_form_bound H
  have ha0 : 0 < Real.pi * c0 / 2 := by positivity
  obtain ⟨u, hu, hub⟩ := hS V Λ hL (Real.pi * c0 / 2 / 2) 0 (by positivity)
  refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
    (hu.mul_left (Real.exp ((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) +
      |r| * Real.pi * K * ‖w‖)))
  have hux := hub x 0 (by simp)
  simp only [sub_zero] at hux
  have hαx : ‖α x‖ = 1 := by
    rcases hα.1 x x.2 with h | h <;> simp [h]
  have hxw : ‖H x w‖ ≤ K * ‖w‖ * ‖(x : V)‖ := by
    have h1 : H x w = LinearMap.toContinuousLinearMap (H.flip w) x := rfl
    rw [h1]
    exact ((LinearMap.toContinuousLinearMap (H.flip w)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hK w) (norm_nonneg _))
  have hxx : c0 * ‖(x : V)‖ ^ 2 ≤ (H x x).re := (hn x).1
  have hkL : ‖kL H w x‖ ≤ Real.pi * (K * (‖w‖ + ‖(x : V)‖)) := by
    rw [kL, norm_smul]
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [Real.pi_pos.le]
    rw [hpi]
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    exact (hK (w - x)).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hK0)
  have hre : (((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re ≤
      Real.pi * (K * ‖w‖ * ‖(x : V)‖) - Real.pi * (c0 * ‖(x : V)‖ ^ 2) / 2 := by
    have e : (((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re =
        Real.pi * (H x w).re - Real.pi * (H x x).re / 2 := by simp
    rw [e]
    have h1 : (H x w).re ≤ K * ‖w‖ * ‖(x : V)‖ := (Complex.re_le_norm _).trans hxw
    have h2 := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
    have h3 := mul_le_mul_of_nonneg_left hxx Real.pi_pos.le
    linarith
  have hkC : ‖kC H α w x‖ = Real.exp ((((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re) := by
    rw [kC, norm_mul, hαx, Complex.norm_exp, one_mul]
  have hr : r * ‖kL H w x‖ ≤ |r| * (Real.pi * (K * (‖w‖ + ‖(x : V)‖))) :=
    (mul_le_mul_of_nonneg_right (le_abs_self r) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hkL (abs_nonneg r))
  have hq := quad_bound (Real.pi * c0 / 2 / 2) (Real.pi * K * ‖w‖ + |r| * Real.pi * K) ‖(x : V)‖ (by positivity)
  rw [hkC, ← Real.exp_add]
  calc Real.exp ((((Real.pi : ℂ) * H x w - (Real.pi : ℂ) * H x x / 2)).re + r * ‖kL H w x‖)
      ≤ Real.exp (((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) +
          |r| * Real.pi * K * ‖w‖) + (-(Real.pi * c0 / 2 / 2) * ‖(x : V)‖ ^ 2)) := by
        apply Real.exp_le_exp.2
        nlinarith [hre, hr, hq]
    _ = Real.exp ((Real.pi * K * ‖w‖ + |r| * Real.pi * K) ^ 2 / (4 * (Real.pi * c0 / 2 / 2)) +
          |r| * Real.pi * K * ‖w‖) * Real.exp (-(Real.pi * c0 / 2 / 2) * ‖(x : V)‖ ^ 2) := Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hux (Real.exp_pos _).le

end KerP

theorem KerPTh_of (hE : ExpSeriesEntire) (hS : LatGaussSummable) (hN : FormNorm) : KerPTh := by
  unfold KerPTh
  intro V _ _ _ H Λ α hH hP hL hα w
  refine ⟨fun z => ?_, ?_⟩
  · have hb := kernel_summable_bound hS hN H Λ α hH hP hL hα w ‖z‖
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hb)
    rw [term_eq, norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    calc (kL H w x z).re ≤ ‖kL H w x z‖ := Complex.re_le_norm _
      _ ≤ ‖kL H w x‖ * ‖z‖ := (kL H w x).le_opNorm z
      _ = ‖z‖ * ‖kL H w x‖ := mul_comm _ _
  show AnalyticOnNhd ℂ (fun z => kerP H α Λ z w) Set.univ ∧ (fun z => kerP H α Λ z w) ∈ fixedBy H α Λ
  refine ⟨?_, ?_⟩
  · have hfun : (fun z => kerP H α Λ z w) = fun z => ∑' x : Λ, kC H α w x * Complex.exp (kL H w x z) :=
      funext fun z => tsum_congr fun x => term_eq H α w x z
    rw [hfun]
    exact hE V Λ (fun x => kC H α w x) (fun x => kL H w x) (kernel_summable_bound hS hN H Λ α hH hP hL hα w)
  · intro y hy z
    have hmul := heisenbergMul V H hH
    show α y * (kerP H α Λ (z + y) w *
      Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2)) = kerP H α Λ z w
    unfold kerP
    rw [← tsum_mul_right, ← tsum_mul_left]
    have key : ∀ x : Λ, α y * (α x * opU H x (kerK H w) (z + y) *
        Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2)) =
        α ((x : V) + y) * opU H ((x : V) + y) (kerK H w) z := by
      intro x
      have h1 : opU H x (kerK H w) (z + y) * Complex.exp (-(Real.pi : ℂ) * H z y - (Real.pi : ℂ) * H y y / 2) =
          opU H y (opU H x (kerK H w)) z := rfl
      have h2 := hmul y x (kerK H w) z
      have h3 := hα.2 x x.2 y hy
      have h4 : altE H y x = -altE H x y := by
        unfold altE
        rw [hH x y, Complex.conj_im]
      have h5 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((altE H y x : ℝ) : ℂ)) =
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x y : ℝ) : ℂ)) := by
        rw [h4]
        congr 1
        push_cast
        ring
      rw [mul_assoc (α x), h1, h2, h5, h3, add_comm y (x : V)]
      ring
    rw [tsum_congr key]
    exact (Equiv.addRight (⟨y, hy⟩ : Λ)).tsum_eq (fun x : Λ => α (x : V) * opU H (x : V) (kerK H w) z)

end Formalism.L2.Th1.H
