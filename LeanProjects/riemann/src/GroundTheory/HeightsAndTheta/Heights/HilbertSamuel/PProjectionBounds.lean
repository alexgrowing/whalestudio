import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CNormSt
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace ProjectionBounds

set_option linter.unusedSectionVars false

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

def pnorm (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) : ℝ :=
  Real.sqrt (∑ k, ‖z (e k)‖ ^ 2)

theorem pnorm_nonneg (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) : 0 ≤ pnorm e z :=
  Real.sqrt_nonneg _

theorem continuous_pnorm (e : Fin (D + 1) → Ix κ) : Continuous (pnorm e) := by
  unfold pnorm; fun_prop

theorem pnorm_smul (e : Fin (D + 1) → Ix κ) (c : ℂ) (z : Ix κ → ℂ) :
    pnorm e (c • z) = ‖c‖ * pnorm e z := by
  simp only [pnorm, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem pnorm_eq_sqN (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) : pnorm e z = Real.sqrt (sqN (z ∘ e)) := by
  simp [pnorm, sqN]

theorem fs_rho_eq (t : Fin (D + 1) → ℂ) : (fsMetric (Fin (D + 1))).ρ t = Real.sqrt (sqN t) := by
  simp [fsMetric, sqN, EuclideanSpace.norm_eq]

theorem pnorm_pos {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) {z : Ix κ → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) : 0 < pnorm e z := by
  obtain ⟨k, hk⟩ := exists_proj_ne_zero hfr hz
  refine Real.sqrt_pos.2 (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hk) 2) ?_)
  exact Finset.single_le_sum (f := fun k => ‖z (e k)‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)

theorem form_le_pnorm {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (n : ℕ)
    (f : MvPolynomial (Ix κ) ℂ) (hf : f.IsHomogeneous n) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z f‖ ≤ S * pnorm e z ^ n := by
  classical
  set K : Set (Ix κ → ℂ) := Metric.sphere 0 1 ∩
    {z | ∀ g ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) g) = 0} with hKdef
  have hcl : IsClosed {z : Ix κ → ℂ | ∀ g ∈ coordIdeal ℤ x,
      eval z (map (Int.castRingHom ℂ) g) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun g => isClosed_iInter fun _ =>
      isClosed_eq (continuous_eval _) continuous_const
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_right hcl
  have hKpts : K ⊆ pts (coordIdeal ℤ x) := fun z hz => ⟨fun h0 => by
    have := hz.1
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at this
    exact zero_ne_one this, hz.2⟩
  have hF : ContinuousOn (fun z => ‖eval z f‖ / pnorm e z ^ n) K :=
    (continuous_eval f).norm.continuousOn.div ((continuous_pnorm e).pow n).continuousOn
      fun z hz => pow_ne_zero n (pnorm_pos hfr (hKpts hz)).ne'
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hF
  refine ⟨|C|, abs_nonneg _, fun z hz => ?_⟩
  have ht : 0 < ‖z‖ := norm_pos_iff.mpr hz.1
  set c : ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) with hcdef
  have hcn : ‖c‖ = ‖z‖⁻¹ := by
    rw [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  have hcpos : 0 < ‖c‖ := by rw [hcn]; exact inv_pos.mpr ht
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hzK : c • z ∈ K := by
    refine ⟨?_, (smul_mem_pts_coord x hz hc0).2⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, hcn, inv_mul_cancel₀ ht.ne']
  have hρ := pnorm_pos hfr hz
  have h1 : ‖‖eval (c • z) f‖ / pnorm e (c • z) ^ n‖ ≤ C := hC _ hzK
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eval_smul_of_isHomogeneous hf, pnorm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (norm_nonneg _) (pow_nonneg (mul_nonneg (norm_nonneg _) hρ.le) n)),
    norm_mul, norm_pow, mul_pow, mul_div_mul_left _ _ (pow_ne_zero n hcpos.ne')] at h1
  have h2 : ‖eval z f‖ ≤ C * pnorm e z ^ n := (div_le_iff₀ (pow_pos hρ n)).mp h1
  exact h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hρ.le n))

theorem pts_nonempty {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) :
    (pts (coordIdeal ℤ x)).Nonempty := by
  obtain ⟨Δ, hΔ0, hΔ⟩ := exists_isDiscr hfr
  obtain ⟨w, hw⟩ := (dense_eval_ne_zero hΔ0).nonempty
  obtain ⟨-, hcard, -⟩ := hΔ w hw
  have hpos := projDeg_pos x e hfr.isRatProjFrame
  rw [← hcard] at hpos
  obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
  exact ⟨z, hz.1⟩

theorem trace_le {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) {N : ℕ}
    (f : MvPolynomial (Ix κ) ℤ) (g : MvPolynomial (Fin (D + 1)) ℤ) (hf : f.IsHomogeneous N)
    (hg : g.IsHomogeneous N) (htr : aeval (x ∘ e) g = secTrace x e N (aeval x f)) {S : ℝ}
    (hS : ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z (map (Int.castRingHom ℂ) f)‖ ≤ S * pnorm e z ^ N)
    (w : Fin (D + 1) → ℂ) :
    ‖eval w (map (Int.castRingHom ℂ) g)‖ ≤ (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N := by
  classical
  obtain ⟨Δ, hΔ0, hΔ⟩ := exists_isDiscr hfr
  have hFc : Continuous fun w : Fin (D + 1) → ℂ => ‖eval w (map (Int.castRingHom ℂ) g)‖ :=
    (continuous_eval _).norm
  have hGc : Continuous fun w : Fin (D + 1) → ℂ => (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N := by
    unfold sqN
    fun_prop
  have hgood : ∀ w ∈ {w : Fin (D + 1) → ℂ | eval w Δ ≠ 0},
      w ∈ {w : Fin (D + 1) → ℂ | ‖eval w (map (Int.castRingHom ℂ) g)‖ ≤
        (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N} := by
    intro w hw
    obtain ⟨hfin, hcard, -, htrace⟩ := hΔ w hw
    simp only [Set.mem_ofPred_eq]
    rw [htrace N f g hf hg htr, finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ z ∈ hfin.toFinset,
        ‖eval z (map (Int.castRingHom ℂ) f)‖ ≤ S * Real.sqrt (sqN w) ^ N := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      have h := hS z hz.1
      have hw' : z ∘ e = w := funext hz.2
      rwa [pnorm_eq_sqN, hw'] at h
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hcard, mul_assoc]
  have hcl := closure_minimal hgood (isClosed_le hFc hGc)
  rw [(dense_eval_ne_zero hΔ0).closure_eq] at hcl
  exact hcl (Set.mem_univ w)

theorem rank_bound {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |(Module.finrank ℤ (sec ℤ x n) : ℝ) -
      (projDeg x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ)| ≤ C * ((n : ℝ) + 1) ^ (D - 1) := by
  set F : ℕ → ℝ := fun n => (Module.finrank ℤ (sec ℤ x n) : ℝ) -
    (projDeg x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) with hFdef
  obtain ⟨c, hc⟩ := (finrank_sec_asymp x e hfr).bound
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  refine ⟨|c| + ∑ i ∈ Finset.range (N + 1), |F i|, by positivity, fun n => ?_⟩
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (N + 1), |F i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (D - 1) := one_le_pow₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  change |F n| ≤ _
  by_cases hn : N + 1 ≤ n
  · have hb := hN n (by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hpow : (n : ℝ) ^ D / (n : ℝ) = (n : ℝ) ^ (D - 1) := by
      rw [← pow_sub_one_mul (by omega : D ≠ 0) (n : ℝ), mul_div_assoc, div_self (by linarith), mul_one]
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [hpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hn0 (D - 1))] at hb
    have hle : (n : ℝ) ^ (D - 1) ≤ ((n : ℝ) + 1) ^ (D - 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    calc |F n| ≤ c * (n : ℝ) ^ (D - 1) := hb
      _ ≤ |c| * ((n : ℝ) + 1) ^ (D - 1) :=
          mul_le_mul (le_abs_self c) hle (pow_nonneg (by linarith) _) (abs_nonneg c)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hsum0) (by positivity)
  · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    calc |F n| ≤ ∑ i ∈ Finset.range (N + 1), |F i| :=
          Finset.single_le_sum (f := fun i => |F i|) (fun i _ => abs_nonneg _) hmem
      _ ≤ (|c| + ∑ i ∈ Finset.range (N + 1), |F i|) * 1 := by
          rw [mul_one]; exact le_add_of_nonneg_left (abs_nonneg c)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

end ProjectionBounds

open ProjectionBounds in

theorem ProjectionBounds.proof (hR : ResChiBounds.Statement) : ProjectionBounds.Statement := by
  classical
  intro D Ω _ _ κ _ d e hfr hFS
  have hrat := hfr.isRatProjFrame
  obtain ⟨kχ, Cχ, hχ⟩ := hR D Ω κ d e hfr hFS
  obtain ⟨k₀, ε, hε, hli⟩ := exists_indep_sections d.x e hrat
  have hεH : ∀ l, ∃ Hl : MvPolynomial (Ix κ) ℤ, Hl.IsHomogeneous k₀ ∧ aeval d.x Hl = ε l := fun l => by
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (hε l)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose H hHh hHe using hεH

  let E : Fin (projDeg d.x e) → MvPolynomial (Ix κ) ℤ := fun l => X (e 0) ^ kχ * H l
  have hEh : ∀ l, (E l).IsHomogeneous (kχ + k₀) := fun l => (isHomogeneous_X_pow (e 0) kχ).mul (hHh l)
  have hEv : ∀ l, aeval d.x (E l) = d.x (e 0) ^ kχ * ε l := fun l => by
    simp only [E, map_mul, map_pow, aeval_X, hHe]
  have hx0 : d.x (e 0) ≠ 0 := coord_ne_zero_of_free (d.x ∘ e) hfr.free 0
  have hEmem : ∀ l, aeval d.x (E l) ∈ sec ℤ d.x (kχ + k₀) := fun l =>
    Submodule.mem_map.mpr ⟨E l, (mem_homogeneousSubmodule _ _).mpr (hEh l), rfl⟩
  have hli' : LinearIndependent (fnField (d.x ∘ e)) (fun l => aeval d.x (E l)) := by
    have := hli.map' (LinearMap.mulLeft (fnField (d.x ∘ e)) (d.x (e 0) ^ kχ))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (pow_ne_zero _ hx0)))
    have hfun : (fun l => aeval d.x (E l)) =
        ⇑(LinearMap.mulLeft (fnField (d.x ∘ e)) (d.x (e 0) ^ kχ)) ∘ ε := by
      funext l
      simp [hEv]
    rw [hfun]
    exact this

  have hCl : ∀ l, ∃ S : ℝ, 0 ≤ S ∧ ∀ z ∈ pts (coordIdeal ℤ d.x),
      ‖eval z (map (Int.castRingHom ℂ) (E l))‖ ≤ S * pnorm e z ^ (kχ + k₀) :=
    fun l => form_le_pnorm hfr (kχ + k₀) _ ((hEh l).map _)
  choose Sl hSl0 hSl using hCl
  have hCE0 : 0 ≤ ∑ l, Sl l := Finset.sum_nonneg fun l _ => hSl0 l
  have hCE : ∀ l, ∀ z ∈ pts (coordIdeal ℤ d.x),
      ‖eval z (map (Int.castRingHom ℂ) (E l))‖ ≤ (∑ l, Sl l) * pnorm e z ^ (kχ + k₀) := fun l z hz =>
    (hSl l z hz).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := Sl) (fun i _ => hSl0 i) (Finset.mem_univ l))
      (pow_nonneg (pnorm_nonneg e z) _))
  obtain ⟨Cr, hCr0, hCr⟩ := rank_bound hfr d.one_le
  have hδ0 : (0 : ℝ) ≤ projDeg d.x e := Nat.cast_nonneg _
  have hA0 : 0 ≤ (projDeg d.x e : ℝ) * ∑ l, Sl l := mul_nonneg hδ0 hCE0
  refine ⟨kχ + k₀, E, (projDeg d.x e : ℝ) * (∑ l, Sl l) + (∑ l, Sl l) + Cr + |Cχ|, hEh, hli',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro n s l hs
    have hm : s * aeval d.x (E l) ∈ sec ℤ d.x (n + (kχ + k₀)) := by
      rw [← sec_mul_sec]
      exact Submodule.mul_mem_mul hs (hEmem l)
    exact secTrace_mem d.x e hfr _ hm
  ·
    intro n s hs h0
    exact eq_zero_of_secTrace_mul_eq_zero d.x e hrat (fun l => aeval d.x (E l)) hEmem hli' n hs h0
  ·
    intro n
    refine (hCr n).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    linarith [abs_nonneg Cχ]
  ·
    intro n f g l c hf hg htr hc t ht
    obtain ⟨z₀, hz₀⟩ := pts_nonempty hfr
    have hc0 : 0 ≤ c :=
      le_trans (div_nonneg (norm_nonneg _) (pow_nonneg (d.m.pos z₀ hz₀.1).le n)) (hc z₀ hz₀)
    have htr' : aeval (d.x ∘ e) g = secTrace d.x e (n + (kχ + k₀)) (aeval d.x (f * E l)) := by
      rw [map_mul]; exact htr
    have hS : ∀ z ∈ pts (coordIdeal ℤ d.x), ‖eval z (map (Int.castRingHom ℂ) (f * E l))‖ ≤
        (c * ∑ l, Sl l) * pnorm e z ^ (n + (kχ + k₀)) := by
      intro z hz
      have hρ : 0 < pnorm e z := pnorm_pos hfr hz
      have hmz : d.m.ρ z = pnorm e z := hFS z hz
      have h1 : ‖eval z (map (Int.castRingHom ℂ) f)‖ ≤ c * pnorm e z ^ n := by
        have := hc z hz
        rw [ptNorm, hmz] at this
        exact (div_le_iff₀ (pow_pos hρ n)).mp this
      rw [map_mul, eval_mul, norm_mul, pow_add]
      calc _ ≤ (c * pnorm e z ^ n) * ((∑ l, Sl l) * pnorm e z ^ (kχ + k₀)) :=
            mul_le_mul h1 (hCE l z hz) (norm_nonneg _) (le_trans (norm_nonneg _) h1)
        _ = (c * ∑ l, Sl l) * (pnorm e z ^ n * pnorm e z ^ (kχ + k₀)) := by ring
    have hb := trace_le hfr (f * E l) g (hf.mul (hEh l)) hg htr' hS t
    have hρt : 0 < (fsMetric (Fin (D + 1))).ρ t := (fsMetric _).pos t ht
    rw [ptNorm, div_le_iff₀ (pow_pos hρt _), fs_rho_eq]
    rw [fs_rho_eq] at hρt
    calc _ ≤ (projDeg d.x e : ℝ) * (c * ∑ l, Sl l) * Real.sqrt (sqN t) ^ (n + (kχ + k₀)) := hb
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρt.le _)
          nlinarith [mul_nonneg hA0 hc0, mul_nonneg hCE0 hc0, mul_nonneg hCr0 hc0,
            mul_nonneg (abs_nonneg Cχ) hc0]
  ·
    intro n Q c hkn hQ hc z hz
    have hρ : 0 < pnorm e z := pnorm_pos hfr hz
    have hmz : d.m.ρ z = pnorm e z := hFS z hz
    have hze : z ∘ e ≠ 0 := by
      obtain ⟨j, hj⟩ := exists_proj_ne_zero hfr hz
      exact fun h0 => hj (congrFun h0 j)
    have hfsz : (fsMetric (Fin (D + 1))).ρ (z ∘ e) = pnorm e z := by rw [fs_rho_eq, pnorm_eq_sqN]
    have hc0 : ∀ l, 0 ≤ c l := fun l => le_trans
      (div_nonneg (norm_nonneg _) (pow_nonneg ((fsMetric _).pos _ hze).le _)) (hc l (z ∘ e) hze)
    have hQb : ∀ l, ‖eval (z ∘ e) (map (Int.castRingHom ℂ) (Q l))‖ ≤
        c l * pnorm e z ^ (n - (kχ + k₀)) := fun l => by
      have := hc l (z ∘ e) hze
      rw [ptNorm, hfsz] at this
      exact (div_le_iff₀ (pow_pos hρ _)).mp this
    have hexp : eval z (map (Int.castRingHom ℂ) (∑ l, rename e (Q l) * E l)) =
        ∑ l, eval (z ∘ e) (map (Int.castRingHom ℂ) (Q l)) * eval z (map (Int.castRingHom ℂ) (E l)) := by
      simp only [map_sum, map_mul, map_rename, eval_rename]
    have hs0 : 0 ≤ ∑ l, c l := Finset.sum_nonneg fun l _ => hc0 l
    rw [ptNorm, hmz, div_le_iff₀ (pow_pos hρ n), hexp]
    calc _ ≤ ∑ l, ‖eval (z ∘ e) (map (Int.castRingHom ℂ) (Q l)) *
            eval z (map (Int.castRingHom ℂ) (E l))‖ := norm_sum_le _ _
      _ ≤ ∑ l, (c l * pnorm e z ^ (n - (kχ + k₀))) * ((∑ l, Sl l) * pnorm e z ^ (kχ + k₀)) :=
          Finset.sum_le_sum fun l _ => by
            rw [norm_mul]
            exact mul_le_mul (hQb l) (hCE l z hz) (norm_nonneg _) (le_trans (norm_nonneg _) (hQb l))
      _ = (∑ l, Sl l) * (∑ l, c l) * pnorm e z ^ n := by
          rw [show (∑ l, (c l * pnorm e z ^ (n - (kχ + k₀))) * ((∑ l, Sl l) * pnorm e z ^ (kχ + k₀))) =
              ∑ l, c l * ((∑ l, Sl l) * pnorm e z ^ n) from Finset.sum_congr rfl fun l _ => by
                rw [← pow_sub_mul_pow (pnorm e z) hkn]; ring, ← Finset.sum_mul]
          ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ.le _)
          nlinarith [mul_nonneg hA0 hs0, mul_nonneg hCr0 hs0, mul_nonneg (abs_nonneg Cχ) hs0]
  ·
    intro n hn
    have hmono : Monotone (chiP D) := monotone_nat_of_le_succ fun m => by
      have := chiP_succ_sub_nonneg D m; linarith
    obtain ⟨hlo, hhi⟩ := hχ n (by omega)
    have hP1 : chiP D (n - (kχ + k₀)) ≤ chiP D (n - kχ) := hmono (by omega)
    have hP2 : chiP D (n + kχ) ≤ chiP D (n + (kχ + k₀)) := hmono (by omega)
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hL : 0 ≤ (n : ℝ) ^ D * Real.log (n + 1) :=
      mul_nonneg (pow_nonneg hn0 _) (Real.log_nonneg (by linarith))
    have hCC : Cχ ≤ (projDeg d.x e : ℝ) * (∑ l, Sl l) + (∑ l, Sl l) + Cr + |Cχ| := by
      linarith [le_abs_self Cχ]
    have h3 : Cχ * (n : ℝ) ^ D * Real.log (n + 1) ≤
        ((projDeg d.x e : ℝ) * (∑ l, Sl l) + (∑ l, Sl l) + Cr + |Cχ|) * (n : ℝ) ^ D * Real.log (n + 1) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hCC hL
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hP1 hδ0]
    · nlinarith [mul_le_mul_of_nonneg_left hP2 hδ0]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
