import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.SatW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem coef_step_of (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ)
    (hgpi0 : ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W))
    (hA2 : ∀ f ∈ W.AΔ, ∃ g ∈ W.AΔ, W.γA W.gam f - f = W.π₀ * qA W * g)
    (hA3 : ∀ k ≥ 1, ∃ g ∈ W.AΔ, W.γA W.gam (ps W k) = ps W k * (1 + W.π₀ * qA W * g))
    (hA4 : ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g)
    (hinj : Function.Injective (algebraMap O LL))
    (cc : ℤ → O) (hcc : ∀ m : ℤ, (-((PD.p : ℕ) : O)) * cc m = (((W.χΓ W.gam) ^ (-m) : Oˣ) : O) - 1)
    (bi : ℕ) (s : W.EE) (s' : LetA O n) (hs' : s' ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k})
    (hs : algebraMap (LetA O n) W.EE (qA W ^ bi) * s = algebraMap (LetA O n) W.EE s')
    (j : ℕ) (hj : j ≤ bi) (g : LetA O n) (hg : g ∈ W.AΔ) :
    ∃ h ∈ W.AΔ, W.γE W.gam (algebraMap (LetA O n) W.EE (qA W ^ j * g) * s) -
        algebraMap (LetA O n) W.EE (qA W ^ j * g) * s =
      algebraMap (LetA O n) W.EE (W.π₀ * qA W ^ j *
        (algebraMap O (LetA O n) (cc ((bi : ℤ) - j)) * g + qA W * h)) * s := by
  obtain ⟨hbij, hs1, hp2⟩ := hcase
  have hfin : Module.finrank K₀ K = 1 := finrank_one_of_bij' hbij
  obtain ⟨-, -, h9c⟩ := hP9 T hT hs1 hp2
  obtain ⟨⟨hπΔ', -, ⟨wπ, hwπ⟩, -⟩, -⟩ := h9c hfin
  have hπ : W.π₀ ∈ W.AΔ := hπΔ'
  have hp1 : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  have hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0 := p_nzd_O W hinj
  have hQe : qA W = W.π₀ + ((PD.p : ℕ) : LetA O n) := rfl
  have hQΔ : qA W ∈ W.AΔ := by rw [hQe]; exact add_mem hπ (natCast_mem _ _)
  have hUπ : UPi PD.p W.π₀ := ⟨wπ, PD.p - 1, 0, by rw [hwπ, mul_zero, add_zero]⟩
  have hUQ : UPi PD.p (qA W) := ⟨wπ, PD.p - 1, 1, by rw [hQe, hwπ, mul_one]⟩
  have hEQ : IsUnit (algebraMap (LetA O n) W.EE (qA W)) := isUnit_EE_of_UPi W hUQ
  have hΓ : ∀ a : LetA O n, W.γE W.gam (algebraMap (LetA O n) W.EE a) =
      algebraMap (LetA O n) W.EE (W.γA W.gam a) := fun a => W.γE_ext W.gam a

  obtain ⟨g4, hg4, h4⟩ := hA4
  obtain ⟨Xc, hXc⟩ : ∃ X : LetA O n, X = algebraMap O (LetA O n) ((W.χΓ W.gam : Oˣ) : O) :=
    ⟨_, rfl⟩
  have hXcΔ : Xc ∈ W.AΔ := by rw [hXc]; exact Subalgebra.algebraMap_mem _ _
  obtain ⟨w, hw⟩ : ∃ w : LetA O n, w = Xc + qA W * g4 := ⟨_, rfl⟩
  have hwΔ : w ∈ W.AΔ := by rw [hw]; exact add_mem hXcΔ (mul_mem hQΔ hg4)
  have h4' : W.γA W.gam (qA W) = qA W * w := by
    rw [h4, hw, hXc, Algebra.smul_def]; ring
  obtain ⟨g5, hg5, h5⟩ := hA2 (qA W) hQΔ
  have hw1 : w = 1 + W.π₀ * g5 := by
    apply W.EE_inj
    apply hEQ.mul_left_cancel
    rw [← map_mul (algebraMap (LetA O n) W.EE), ← map_mul (algebraMap (LetA O n) W.EE)]
    exact congrArg (algebraMap (LetA O n) W.EE) (by linear_combination h5 - h4')

  have hmulw : w * (fun i => PowerSeries.invOfUnit (w i) 1) = 1 := funext fun i => by
    show w i * PowerSeries.invOfUnit (w i) 1 = 1
    refine PowerSeries.mul_invOfUnit (w i) 1 ?_
    rw [hw1, hwπ]
    simp [letπ, zero_pow hp1]
  have hwU : IsUnit w := ⟨⟨w, _, hmulw, by rw [mul_comm]; exact hmulw⟩, rfl⟩
  obtain ⟨wu, hwu⟩ := id hwU
  obtain ⟨wi, hwi⟩ : ∃ x : LetA O n, x = ((wu⁻¹ : (LetA O n)ˣ) : LetA O n) := ⟨_, rfl⟩
  have hwwi : w * wi = 1 := by rw [hwi, ← hwu]; exact wu.mul_inv
  have hwiΔ : wi ∈ W.AΔ := by
    have hwδ : ∀ δ ∈ W.DelF, W.γA δ w = w := hwΔ
    show ∀ δ ∈ W.DelF, W.γA δ wi = wi
    intro δ hδ
    apply hwU.mul_left_cancel
    calc w * W.γA δ wi = W.γA δ w * W.γA δ wi := by rw [hwδ δ hδ]
      _ = W.γA δ (w * wi) := (map_mul (W.γA δ) w wi).symm
      _ = w * wi := by rw [hwwi, map_one]

  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = bi - j := ⟨_, rfl⟩
  have hbi : bi = j + m := by omega
  have e' : -((bi : ℤ) - (j : ℤ)) = -((m : ℕ) : ℤ) := by rw [hm, Nat.cast_sub hj]
  have key : ((((W.χΓ W.gam) ^ m)⁻¹ : Oˣ) : O) = 1 - ((PD.p : ℕ) : O) * cc ((bi : ℤ) - j) := by
    have h0 := hcc ((bi : ℤ) - j)
    rw [e', zpow_neg, zpow_natCast] at h0
    linear_combination -h0
  have hc' : ((W.χΓ W.gam : Oˣ) : O) ^ m * (1 - ((PD.p : ℕ) : O) * cc ((bi : ℤ) - j)) = 1 := by
    rw [← key, ← Units.val_pow_eq_pow_val, Units.mul_inv]
  obtain ⟨C, hC⟩ : ∃ C : LetA O n, C = algebraMap O (LetA O n) (cc ((bi : ℤ) - j)) := ⟨_, rfl⟩
  have hCΔ : C ∈ W.AΔ := by rw [hC]; exact Subalgebra.algebraMap_mem _ _
  have hcA : Xc ^ m * (1 - ((PD.p : ℕ) : LetA O n) * C) = 1 := by
    have := congrArg (algebraMap O (LetA O n)) hc'
    simpa only [map_mul, map_sub, map_one, map_pow, map_natCast, ← hC, ← hXc] using this

  obtain ⟨R1, hR1d⟩ : ∃ R : LetA O n,
      R = (Finset.range m).sum (fun i => w ^ i * Xc ^ (m - 1 - i)) := ⟨_, rfl⟩
  obtain ⟨R2, hR2d⟩ : ∃ R : LetA O n, R = (Finset.range m).sum (fun i => w ^ i) := ⟨_, rfl⟩
  have hR1 : R1 * (w - Xc) = w ^ m - Xc ^ m := by rw [hR1d]; exact geom_sum₂_mul w Xc m
  have hR2 : R2 * (w - 1) = w ^ m - 1 := by rw [hR2d]; exact geom_sum_mul w m
  have hR1Δ : R1 ∈ W.AΔ := by
    rw [hR1d]; exact sum_mem fun i _ => mul_mem (pow_mem hwΔ _) (pow_mem hXcΔ _)
  have hR2Δ : R2 ∈ W.AΔ := by rw [hR2d]; exact sum_mem fun i _ => pow_mem hwΔ _
  obtain ⟨M, hMd⟩ : ∃ M : LetA O n, M = Xc ^ m * C + g4 * R1 * (1 + W.π₀ * C) := ⟨_, rfl⟩
  obtain ⟨N, hNd⟩ : ∃ N : LetA O n, N = g5 * R2 * (1 + W.π₀ * C) + C := ⟨_, rfl⟩
  have hQM : w ^ m * (1 + W.π₀ * C) = 1 + qA W * M := by
    linear_combination (-(1 + W.π₀ * C)) * hR1 + (R1 * (1 + W.π₀ * C)) * hw + hcA -
      (Xc ^ m * C) * hQe - qA W * hMd
  have hπN : w ^ m * (1 + W.π₀ * C) = 1 + W.π₀ * N := by
    linear_combination (-(1 + W.π₀ * C)) * hR2 + (R2 * (1 + W.π₀ * C)) * hw1 - W.π₀ * hNd
  have hpM : ((PD.p : ℕ) : LetA O n) ^ 1 * M = W.π₀ * (N - M) := by
    linear_combination hπN - hQM - M * hQe
  obtain ⟨Z, hZ⟩ := dvd_of_UPi hO hUπ 1 (N - M) M hpM
  have hMZ : M = W.π₀ * Z := by
    apply p_cancel hO
    linear_combination hpM + W.π₀ * hZ
  have hMΔ : M ∈ W.AΔ := by
    rw [hMd]
    exact add_mem (mul_mem (pow_mem hXcΔ _) hCΔ)
      (mul_mem (mul_mem hg4 hR1Δ) (add_mem (one_mem _) (mul_mem hπ hCΔ)))
  have hNΔ : N ∈ W.AΔ := by
    rw [hNd]
    exact add_mem (mul_mem (mul_mem hg5 hR2Δ) (add_mem (one_mem _) (mul_mem hπ hCΔ))) hCΔ
  have hZΔ : Z ∈ W.AΔ := mem_AΔ_of_p_pow W hO 1 (by rw [← hZ]; exact sub_mem hNΔ hMΔ)
  have hYM : w ^ m * (1 + W.π₀ * C) = 1 + qA W * (W.π₀ * Z) := by rw [← hMZ]; exact hQM

  let S : Submonoid (LetA O n) :=
    { carrier := {x | ∃ t ∈ W.AΔ, W.γA W.gam x = x * (1 + W.π₀ * qA W * t)}
      mul_mem' := by
        rintro a b ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        refine ⟨ta + tb + W.π₀ * qA W * ta * tb,
          add_mem (add_mem hta htb) (mul_mem (mul_mem (mul_mem hπ hQΔ) hta) htb), ?_⟩
        rw [map_mul (W.γA W.gam), ha, hb]; ring
      one_mem' := ⟨0, zero_mem _, by simp⟩ }
  have hsub : {x : LetA O n | ∃ k ≥ 1, x = ps W k} ⊆ (S : Set (LetA O n)) := by
    rintro x ⟨k, hk, rfl⟩
    exact hA3 k hk
  have hsS : s' ∈ S := Submonoid.closure_le.mpr hsub hs'
  obtain ⟨t, ht, hts⟩ := hsS

  have h1 := congrArg (W.γE W.gam) hs
  rw [map_mul (W.γE W.gam), hΓ, hΓ, hts, map_pow (W.γA W.gam), h4', mul_pow,
    map_mul (algebraMap (LetA O n) W.EE), map_mul (algebraMap (LetA O n) W.EE), ← hs] at h1
  have hu : IsUnit (algebraMap (LetA O n) W.EE (qA W ^ bi)) := by
    rw [map_pow]; exact hEQ.pow bi
  have h2' : algebraMap (LetA O n) W.EE (w ^ bi) * W.γE W.gam s =
      s * algebraMap (LetA O n) W.EE (1 + W.π₀ * qA W * t) := by
    apply hu.mul_left_cancel
    linear_combination h1
  have hEwb : algebraMap (LetA O n) W.EE w ^ bi * algebraMap (LetA O n) W.EE wi ^ bi = 1 := by
    rw [← mul_pow, ← map_mul, hwwi, map_one, one_pow]
  rw [map_pow] at h2'
  have hΓs : W.γE W.gam s = algebraMap (LetA O n) W.EE wi ^ bi *
      (s * algebraMap (LetA O n) W.EE (1 + W.π₀ * qA W * t)) := by
    linear_combination (algebraMap (LetA O n) W.EE wi ^ bi) * h2' - (W.γE W.gam s) * hEwb

  obtain ⟨g2, hg2, h2⟩ := hA2 g hg
  have hg' : W.γA W.gam g = g + W.π₀ * qA W * g2 := by linear_combination h2
  have hwj : w ^ j * wi ^ j = 1 := by rw [← mul_pow, hwwi, one_pow]
  have hwm1 : w ^ m * wi ^ m = 1 := by rw [← mul_pow, hwwi, one_pow]
  have hwbi : wi ^ bi = wi ^ j * wi ^ m := by rw [← pow_add, ← hbi]
  obtain ⟨h, hh⟩ : ∃ h : LetA O n,
      h = wi ^ m * (g2 + g * t + W.π₀ * qA W * g2 * t - g * Z) := ⟨_, rfl⟩
  have keyA : W.γA W.gam (qA W ^ j * g) * (wi ^ bi * (1 + W.π₀ * qA W * t)) =
      qA W ^ j * g + W.π₀ * qA W ^ j * (C * g + qA W * h) := by
    rw [map_mul (W.γA W.gam), map_pow (W.γA W.gam), h4', hg']
    linear_combination
      ((qA W * w) ^ j * (g + W.π₀ * qA W * g2) * (1 + W.π₀ * qA W * t)) * hwbi +
      (qA W ^ j * (g + W.π₀ * qA W * g2) * (1 + W.π₀ * qA W * t) * wi ^ m) * hwj -
      (qA W ^ j * g * wi ^ m) * hYM + (qA W ^ j * g * (1 + W.π₀ * C)) * hwm1 -
      (W.π₀ * qA W ^ j * qA W) * hh
  have hfin2 : W.γE W.gam (algebraMap (LetA O n) W.EE (qA W ^ j * g) * s) =
      algebraMap (LetA O n) W.EE (qA W ^ j * g + W.π₀ * qA W ^ j * (C * g + qA W * h)) * s := by
    rw [map_mul (W.γE W.gam), hΓ, hΓs, ← keyA]
    simp only [map_mul, map_pow]
    ring
  refine ⟨h, ?_, ?_⟩
  · rw [hh]
    exact mul_mem (pow_mem hwiΔ _) (sub_mem (add_mem (add_mem hg2 (mul_mem hg ht))
      (mul_mem (mul_mem (mul_mem hπ hQΔ) hg2) ht)) (mul_mem hg hZΔ))
  · rw [← hC, hfin2, map_add]
    ring

end Formalism.MainNotions.N.FrobeniusPowerSeries
