import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.FlagImmersions.RealTowerPlurisubharmonicPotential
import Development.WeilBound.CoreStatements.FlagImmersions.PshSumPotentialsSmallParameter

noncomputable section

namespace RootFieldNumerics.A1

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem gap_eq (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    PB.gap lam p = lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0 := by
  unfold PB.gap PB.gapX
  split_ifs <;> simp

theorem abs_le_l1_norm (lam : Wt Ψ N) (τ : Ψ) (i : Fin N) : |lam τ i| ≤ l1 lam := by
  unfold l1
  calc |lam τ i| ≤ ∑ j : Fin N, |lam τ j| :=
        Finset.single_le_sum (f := fun j => |lam τ j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ σ : Ψ, ∑ j : Fin N, |lam σ j| :=
        Finset.single_le_sum (f := fun σ => ∑ j : Fin N, |lam σ j|)
          (fun σ _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ τ)

theorem abs_gap_le (mu : Wt Ψ N) (b : ℝ) (hb : ∀ τ i, |mu τ i| ≤ b) (p : Ψ × Fin N) :
    |PB.gap (fun x => mu x.1 x.2) p| ≤ 2 * b := by
  rw [gap_eq]
  have h0 : 0 ≤ b := le_trans (abs_nonneg _) (hb p.1 p.2)
  refine le_trans (abs_sub _ _) ?_
  have h1 : |mu p.1 p.2| ≤ b := hb p.1 p.2
  split_ifs with h
  · have h2 := hb p.1 ⟨(p.2 : ℕ) + 1, h⟩
    simp only at h1 h2 ⊢
    linarith
  · simp only [abs_zero] at h1 ⊢
    linarith

theorem comp_psh {D : ℕ} (S : PB.AnSys D (Option (Ψ × Fin N))) (k : ℕ) (hk : 0 < k) (b : ℝ)
    (h0 : ∀ t x, S.phT none t x = 0)
    (hfl : ∀ τ (i : Fin N), (i : ℕ) + 1 = N → ∀ t, IsPsh S.A ((S.potT (some (τ, i)) t).rsmul (-1)) ∧
      IsPsh S.A (S.potT (some (τ, i)) t))
    (hpos : IsPosPot S.A (S.th none)) :
    ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → scale s ≤ S.t₀ ∧ ∀ mu : Wt Ψ N, (∀ τ i, |mu τ i| ≤ b) → Dominant mu →
      IsPsh S.A (PB.sumPot (PB.gapS (fun x => mu x.1 x.2) (s / k)) fun a => S.potT a (scale s)) := by
  have hth : IsPotential S.A (S.th none) := (S.sing none).1
  obtain ⟨c₀, hc₀, hcmp⟩ := compare_global hth hpos S.potΘ
  have hpotb : IsPotential S.A (S.th none + LocPot.rsmul (-c₀) S.Θ) :=
    isPotentialAdd S.A _ _ hth (isPotentialRsmul S.A (-c₀) S.Θ S.potΘ)
  have hbase : IsPsh S.A (S.th none + LocPot.rsmul (-c₀) S.Θ) := by
    rw [isPsh_iff hpotb]
    intro j y hy w
    rw [dl_add_rsmul hth S.potΘ (-c₀) j hy w]
    have := hcmp j y hy w
    linarith
  have ha' : ∀ t, IsPsh S.A (S.potT none t + LocPot.rsmul (-c₀) S.Θ) := by
    intro t x j y hy w
    have hy' : y ∈ (S.A.chart j).target ∩ ↑(S.A.chart j).symm ⁻¹'
        (S.th none + LocPot.rsmul (-c₀) S.Θ).U x := by
      refine ⟨hy.1, ?_⟩
      have h2 := hy.2
      simp only [Set.mem_preimage] at h2 ⊢
      exact ⟨h2.1.1, h2.2⟩
    have h3 := hbase x j y hy' w
    convert h3 using 2
    funext z
    simp only [Function.comp_apply]
    show (S.th none).φ x _ + S.phT none t _ + -c₀ * S.Θ.φ x _ =
      (S.th none).φ x _ + -c₀ * S.Θ.φ x _
    rw [h0]
    ring
  let Fl : Set (Option (Ψ × Fin N)) := {a | ∃ p : Ψ × Fin N, a = some p ∧ (p.2 : ℕ) + 1 = N}
  have hFl : ∀ a ∈ Fl, ∀ t, IsPsh S.A (LocPot.rsmul (-1) (S.potT a t)) ∧ IsPsh S.A (S.potT a t) := by
    rintro a ⟨p, rfl, hp⟩ t
    exact hfl p.1 p.2 hp t
  have hnone : (none : Option (Ψ × Fin N)) ∉ Fl := by
    rintro ⟨p, hp, -⟩
    cases hp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set abelian₂ : ℝ := 1 + ∑ _p : Ψ × Fin N, (k : ℝ) * (2 * b) with hLam
  obtain ⟨s₁, hs₁, hall⟩ := psh_sum_potentials_small_parameter D _ S Fl none c₀ abelian₂ hc₀ hFl ha' hnone
  refine ⟨min s₁ 1, lt_min hs₁ one_pos, fun s hs hss => ?_⟩
  obtain ⟨hsc, hmain⟩ := hall s hs (le_trans hss (min_le_left _ _))
  have hs1 : s ≤ 1 := le_trans hss (min_le_right _ _)
  refine ⟨hsc, fun mu hmu hdom => ?_⟩
  have hpot : ∀ a, IsPotential S.A (S.potT a (scale s)) :=
    fun a => potT_potential S a (Real.exp_pos _) hsc
  set c : Option (Ψ × Fin N) → ℝ := PB.gapS (fun x => mu x.1 x.2) (s / k) with hc
  have hcn : c none = s / k := rfl
  have hcs : ∀ p, c (some p) = PB.gap (fun x => mu x.1 x.2) p := fun p => rfl
  let c' : Option (Ψ × Fin N) → ℝ := fun a => (k : ℝ) * c a
  have h1 : c' none = s := by
    show (k : ℝ) * c none = s
    rw [hcn]
    field_simp
  have h2 : ∑ a, |c' a| ≤ abelian₂ := by
    rw [Fintype.sum_option, hLam]
    have e1 : |c' none| ≤ 1 := by rw [h1, abs_of_pos hs]; exact hs1
    have e2 : ∑ p : Ψ × Fin N, |c' (some p)| ≤ ∑ _p : Ψ × Fin N, (k : ℝ) * (2 * b) := by
      refine Finset.sum_le_sum fun p _ => ?_
      show |(k : ℝ) * c (some p)| ≤ _
      rw [abs_mul, abs_of_pos hkR, hcs]
      exact mul_le_mul_of_nonneg_left (abs_gap_le mu b hmu p) hkR.le
    linarith
  have h3 : ∀ a ∉ Fl, 0 ≤ c' a := by
    intro a ha
    cases a with
    | none => rw [h1]; exact hs.le
    | some p =>
      show 0 ≤ (k : ℝ) * c (some p)
      refine mul_nonneg hkR.le ?_
      rw [hcs, gap_eq]
      have hlt : (p.2 : ℕ) + 1 < N := by
        have hne : (p.2 : ℕ) + 1 ≠ N := fun h => ha ⟨p, rfl, h⟩
        have := p.2.isLt
        omega
      rw [dif_pos hlt]
      have := hdom p.1 p.2 ⟨(p.2 : ℕ) + 1, hlt⟩ (by
        show (p.2 : ℕ) ≤ (p.2 : ℕ) + 1
        omega)
      simp only
      linarith
  have hP : IsPsh S.A (PB.sumPot c' (fun a => S.potT a (scale s)) +
      LocPot.rsmul (-(s * c₀ / 2)) S.Θ) := hmain c' h1 h2 h3
  rw [isPsh_iff (isPotential_sumPot c hpot)]
  intro j y hy w
  have hq := dl_nonneg hP j hy w
  rw [dl_add_rsmul (isPotential_sumPot c' hpot) S.potΘ _ j hy w, dl_sumPot c' hpot j hy w] at hq
  rw [dl_sumPot c hpot j hy w]
  have hΘ := dl_nonneg_of_pos S.posΘ j hy w
  have hsum : ∑ a, c' a * dl S.A (S.potT a (scale s)) j y w =
      (k : ℝ) * ∑ a, c a * dl S.A (S.potT a (scale s)) j y w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    show (k : ℝ) * c a * _ = _
    ring
  rw [hsum] at hq
  have hsc0 : 0 ≤ s * c₀ / 2 * dl S.A S.Θ j y w := mul_nonneg (by positivity) hΘ
  have hk2 : 0 ≤ (k : ℝ) * ∑ a, c a * dl S.A (S.potT a (scale s)) j y w := by linarith
  exact (mul_nonneg_iff_of_pos_left hkR).mp hk2

end RootFieldNumerics.A1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.real_tower_mean_slope_condition : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → R.Pos → T.A1 := by
  intro _hin II _hII Ψ _ _ N T R hSm hFl hPos
  haveI := T.finC
  haveI := T.neC
  intro abelian₂
  set b : ℝ := abelian₂ + l1 T.nu with hb
  have hex : ∀ c : T.Comp, ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → scale s ≤ (R.Sys c).t₀ ∧
      ∀ mu : Wt Ψ N, (∀ τ i, |mu τ i| ≤ b) → Dominant mu →
        ReciprocityTheory.AnForm.M.IsPsh (R.Sys c).A (PB.sumPot (PB.gapS (fun x => mu x.1 x.2)
          (s / ((T.M 2 c).kA : ℕ))) fun a => (R.Sys c).potT a (scale s)) := by
    intro c
    exact RootFieldNumerics.A1.comp_psh (R.Sys c) (T.M 2 c).kA (T.M 2 c).kA_pos b ((R.tie 2 c).phT_none)
      (hFl c) (hPos c)
  choose f hfpos hf using hex
  refine ⟨min 1 (Finset.univ.inf' Finset.univ_nonempty f),
    lt_min one_pos ((Finset.lt_inf'_iff _).2 fun c _ => hfpos c), ?_⟩
  intro B _hB c lam s hlam hs hss hdom
  have hs1 : s ≤ 1 := le_trans hss (min_le_left _ _)
  have hsf : s ≤ f c :=
    le_trans hss (le_trans (min_le_right _ _) (Finset.inf'_le f (Finset.mem_univ c)))
  obtain ⟨hsc, hmain⟩ := hf c s hs hsf
  set mu := T.lamS lam s with hmu
  have hbd : ∀ τ i, |mu τ i| ≤ b := by
    intro τ i
    have e1 := RootFieldNumerics.A1.abs_le_l1_norm lam τ i
    have e2 := RootFieldNumerics.A1.abs_le_l1_norm T.nu τ i
    have e0 : mu τ i = lam τ i - s * T.nu τ i := rfl
    rw [e0]
    have e3 : |s * T.nu τ i| ≤ |T.nu τ i| := by
      rw [abs_mul, abs_of_pos hs]
      exact mul_le_of_le_one_left (abs_nonneg _) hs1
    calc |lam τ i - s * T.nu τ i| ≤ |lam τ i| + |s * T.nu τ i| := abs_sub _ _
      _ ≤ b := by rw [hb]; linarith
  have hpsh := hmain mu hbd hdom
  have hk : ((T.M B c).kA : ℝ) = ((T.M 2 c).kA : ℕ) := by rw [R.kA_eq B 2 c]
  obtain ⟨hJ, alg, hsmooth⟩ := hSm B c
  letI := alg
  have ht0 : 0 < scale s := Real.exp_pos _
  intro z hz w hw
  refine RootFieldNumerics.Levi.levi_nonneg (T.M B c).Ω (T.M B c).y (dimFl Ψ N) (T.M B c).arith hsmooth hJ
    (R.tie B c).Re.R ((T.M B c).weight (scale s) mu s)
    (fun k => ∑ j, (T.M B c).coef mu s j * (((T.M B c).line (scale s) j).a k : ℝ)) ?_ ?_ ?_ z hz w hw
  · intro cc zz hcc hzz
    simp only [RootModel.weight, RootFieldNumerics.Levi.log_h_torus _ cc zz hcc hzz]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  · intro zz hzz
    have hsm : ∀ j, IsSmoothHerm ((T.M B c).line (scale s) j) := by
      intro j
      cases j with
      | none => exact (T.M B c).A_smooth
      | some r => exact (T.M B c).x_smooth (scale s) r
    show ContDiffAt ℝ 2
      (fun z => ∑ j, (T.M B c).coef mu s j * Real.log (((T.M B c).line (scale s) j).h z)) zz
    exact ContDiffAt.sum fun j _ =>
      contDiffAt_const.mul (RootFieldNumerics.Levi.contDiffAt_log_h (hsm j) zz hzz)
  · intro x j hx u
    refine RootFieldNumerics.Levi.levi_chart_nonneg (R.tie B c).Re (scale s) ht0 hsc _ hpsh x
      (fun y => (T.M B c).weight (scale s) mu s ((R.tie B c).Re.R.lift x y)) ?_ j hx u
    intro y hy
    have hzm : (R.tie B c).Re.R.lift x y ∈ mcPts (T.M B c).P := (R.tie B c).Re.R.mem x y hy
    have hl : ∀ a, Real.log (((R.tie B c).Re.ref a).h ((R.tie B c).Re.R.lift x y)) +
        (R.Sys c).phT a (scale s) ((R.tie B c).Re.π y) =
        Real.log (((R.tie B c).Re.line a (scale s)).h ((R.tie B c).Re.R.lift x y)) :=
      fun a => (RootFieldNumerics.Levi.log_line_lift (R.tie B c).Re a (scale s) ht0 hsc x y hy).symm
    simp only [hl]
    have hnone : Real.log (((R.tie B c).Re.line none (scale s)).h ((R.tie B c).Re.R.lift x y)) =
        Real.log ((T.M B c).A.h ((R.tie B c).Re.R.lift x y)) := by
      rw [← hl none, (R.tie B c).phT_none, add_zero, (R.tie B c).ref_none.2 _ hzm]
    have hsome : ∀ p : Ψ × Fin N,
        Real.log (((R.tie B c).Re.line (some p) (scale s)).h ((R.tie B c).Re.R.lift x y)) =
        -∑ k ≤ p.2, Real.log (((T.M B c).x (scale s) (p.1, k)).h ((R.tie B c).Re.R.lift x y)) :=
      fun p => (R.tie B c).fund_reg p.1 p.2 (scale s) ht0 hsc _ hzm
    rw [Fintype.sum_option, hnone]
    simp only [hsome]
    have hsg := RootFieldNumerics.Levi.sum_gap_mul (fun x => mu x.1 x.2)
      (fun r => Real.log (((T.M B c).x (scale s) r).h ((R.tie B c).Re.R.lift x y)))
    simp only [RootModel.weight, Fintype.sum_option, RootModel.coef, RootModel.line, PB.gapS,
      Option.elim, mul_neg, Finset.sum_neg_distrib, neg_mul, hsg]
    rw [hk]
