import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftBlockDatum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftBlockSections

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem chartLat_smul_one (y : (Σ k, ι k) → Ω) (m : ℕ) (b : K → ℤ) :
    chartLat y (m • b) 1 = chartLat y b m := by
  ext s
  show (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (m • b) k)) ∈ chartRingZ y c) ↔
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → s * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * b k)) ∈ chartRingZ y c)
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_one, one_mul]

theorem secM_le_chartLat [DecidableEq K] {r : ℕ} (y : (Σ k, ι k) → Ω) (v : Fin r → Ω) (b : K → ℤ)
    (hv : ∀ j, v j ∈ chartLat y b 1) (n : ℕ) :
    secM (addBlock y v) (blockDeg (none : Option K) n) ≤ chartLat y (n • b) 1 := by
  classical
  intro s hs
  have hle : Submodule.span ℤ {s | ∃ g : MRing (addIdx ι r), IsMultiHomog g (blockDeg (none : Option K) n) ∧
      aeval (addBlock y v) g = s} ≤ (chartLat y (n • b) 1).toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    show aeval (addBlock y v) g ∈ chartLat y (n • b) 1
    rw [g.as_sum, map_sum]
    refine AddSubgroup.sum_mem _ fun m hm => ?_
    have hold : ∀ (k : K) (i : ι k), m ⟨some k, i⟩ = 0 := by
      intro k i
      have h := hg m hm (some k)
      simp only [blockDeg, reduceCtorEq, if_false] at h
      exact Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ _)
    have htot : ∑ p ∈ m.support, m p = n := by
      rw [Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => Finsupp.notMem_support_iff.mp hp),
        Fintype.sum_sigma, Fintype.sum_option]
      have h0 := hg m hm none
      simp only [blockDeg, if_true] at h0
      have h1 : ∑ k : K, ∑ i : addIdx ι r (some k), m ⟨some k, i⟩ = 0 :=
        Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => hold k i
      rw [h0, h1, add_zero]
    have hprod : m.prod (fun p e => addBlock y v p ^ e) ∈ chartLat y (n • b) 1 := by
      have h := LiftBirationalAmple.chartLat_prod (y := y) m.support (fun p => addBlock y v p ^ m p)
        (fun p => m p • b) (fun p _ => by
          rcases p with ⟨_ | k, i⟩
          · exact LiftBirationalAmple.chartLat_pow (hv i) _
          · simp only [hold k i, pow_zero, zero_smul]
            exact LiftBirationalAmple.chartLat_one_mem)
      rwa [← Finset.sum_smul, htot] at h
    rw [aeval_monomial, algebraMap_int_eq, eq_intCast, ← zsmul_eq_mul]
    exact AddSubgroup.zsmul_mem _ hprod _
  exact hle hs

def oldEmb (r : ℕ) : (Σ k, ι k) → (Σ k, addIdx ι r k) := fun p => ⟨some p.1, p.2⟩

theorem oldEmb_injective (r : ℕ) : Function.Injective (oldEmb (ι := ι) r) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  cases h
  rfl

theorem homog_rename_old (r : ℕ) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog (rename (oldEmb (ι := ι) r) g) (fun o => Option.elim o 0 d) := by
  classical
  intro m' hm' o
  rw [support_rename_of_injective (oldEmb_injective r)] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
  rcases o with _ | k
  · refine Finset.sum_eq_zero fun j _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨p, hp⟩
    exact Option.some_ne_none _ (congrArg Sigma.fst hp)
  · have h := hg m hm k
    simp only [Option.elim_some]
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply (oldEmb_injective r) m ⟨k, i⟩

theorem addBlock_comp_oldEmb {r : ℕ} (y : (Σ k, ι k) → Ω) (v : Fin r → Ω) : addBlock y v ∘ oldEmb r = y := by
  funext p
  rfl

theorem eval_rename_old {r : ℕ} (z : (Σ k, addIdx ι r k) → ℂ) (g : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename (oldEmb r) g)) = eval (basePart₂ z) (map (Int.castRingHom ℂ) g) := by
  rw [map_rename, eval_rename]
  rfl

theorem isSmallH_of_lift [DecidableEq K] {r : ℕ} {y : (Σ k, ι k) → Ω} {v : Fin r → Ω} {N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {a : ℕ}
    {B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι r)} (hB : B.a = unitDeg (none : Option K))
    (hv : ∀ j, v j ∈ chartLat y N.a a)
    (hmet : ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j,
      secNormAt y N a (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖)
    (hlift : ∀ w ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal (addBlock y v)), basePart₂ z = w)
    {n : ℕ} {s : Ω} (hs : IsSmallH (mCoordIdeal (addBlock y v)) (addBlock y v) B n s) :
    IsSmallH (mCoordIdeal y) y N (a * n) s := by
  classical
  intro dg dh g h w hg hh hdeg he hw
  obtain ⟨z, hz, rfl⟩ := hlift w hw
  obtain ⟨j, hj⟩ := hz.1 none
  choose c hc using hw.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (by
    have := SectionBounded.vanish hw (SectionBounded.homog_X (ι := ι) ⟨k, c k⟩) (by rw [aeval_X]; exact h0)
    simpa using this)

  obtain ⟨δ, e, he_h, he_v⟩ := SectionBounded.exists_form_of_mem_chartRingZ y c hyc (hv j c hyc)
  set t : K → ℤ := fun k => (a : ℤ) * N.a k with ht
  set β : K → ℕ := fun k => δ k + (-t k).toNat with hβ
  set γ : K → ℕ := fun k => (t k).toNat with hγ
  set q₁ := SectionBounded.chartMon c β with hq₁
  set r₁ := e * SectionBounded.chartMon c γ with hr₁
  have hq₁h : IsMultiHomog q₁ β := SectionBounded.homog_chartMon c β
  have hr₁h : IsMultiHomog r₁ (δ + γ) := SectionBounded.homog_mul he_h (SectionBounded.homog_chartMon c γ)
  have hdeg₁ : ∀ k, (((δ + γ) k : ℕ) : ℤ) = β k + t k := by
    intro k
    simp only [Pi.add_apply, hβ, hγ]
    omega
  have hval₁ : aeval y r₁ = v j * aeval y q₁ := by
    rw [hr₁, hq₁, map_mul, SectionBounded.aeval_chartMon, SectionBounded.aeval_chartMon, he_v]
    have hk : ∀ k, y ⟨k, c k⟩ ^ β k =
        y ⟨k, c k⟩ ^ (-((a : ℤ) * N.a k)) * y ⟨k, c k⟩ ^ δ k * y ⟨k, c k⟩ ^ γ k := by
      intro k
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]
      congr 1
      simp only [hβ, hγ, ht]
      omega
    rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring

  set w := basePart₂ z with hw_def
  set σ := secNormAt y N a (v j) w with hσ
  have hBpos : 0 < B.h z := B.pos z hz.1
  have hZ : 0 < ‖z ⟨none, j⟩‖ := norm_pos_iff.mpr hj
  have hσB : σ * B.h z = ‖z ⟨none, j⟩‖ := hmet z hz j
  have hσpos : 0 < σ := by
    by_contra hle
    push Not at hle
    nlinarith
  have hQ : 0 < ‖eval w (map (Int.castRingHom ℂ) q₁)‖ := by
    rw [hq₁, SectionBounded.eval_chartMon]
    exact norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  have hM : 0 < N.h w ^ a := pow_pos (N.pos w hw.1) _
  have hR : ‖eval w (map (Int.castRingHom ℂ) r₁)‖ ≤ σ * (‖eval w (map (Int.castRingHom ℂ) q₁)‖ * N.h w ^ a) := by
    have hS : {c' : ℝ | 0 ≤ c' ∧ IsBoundedAt y N a c' (v j) w}.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have : σ = 0 := by rw [hσ, secNormAt, hne, Real.sInf_empty]
      linarith
    rw [← div_le_iff₀ (mul_pos hQ hM)]
    refine le_csInf hS fun c' ⟨_, hc'⟩ => ?_
    rw [div_le_iff₀ (mul_pos hQ hM)]
    have := hc' (δ + γ) β r₁ q₁ hr₁h hq₁h (fun k => hdeg₁ k) hval₁
    linarith

  set G := rename (oldEmb r) g * rename (oldEmb r) (q₁ ^ n) * (X ⟨none, j⟩ : MRing (addIdx ι r)) ^ n with hG
  set H := rename (oldEmb r) h * rename (oldEmb r) (r₁ ^ n) with hH
  set dG : Option K → ℕ := (fun o => Option.elim o 0 dg) + (fun o => Option.elim o 0 (n • β)) +
      n • Pi.single (none : Option K) 1 with hdG
  set dH : Option K → ℕ := (fun o => Option.elim o 0 dh) + (fun o => Option.elim o 0 (n • (δ + γ))) with hdH
  have hGh : IsMultiHomog G dG :=
    SectionBounded.homog_mul (SectionBounded.homog_mul (homog_rename_old r hg)
      (homog_rename_old r (SectionBounded.homog_pow hq₁h n)))
      (SectionBounded.homog_pow (SectionBounded.homog_X (ι := addIdx ι r) ⟨none, j⟩) n)
  have hHh : IsMultiHomog H dH :=
    SectionBounded.homog_mul (homog_rename_old r hh) (homog_rename_old r (SectionBounded.homog_pow hr₁h n))
  have hdegGH : ∀ o, (dG o : ℤ) = dH o + n * B.a o := by
    intro o
    rw [hB, hdG, hdH]
    rcases o with _ | k
    · simp [unitDeg]
    · have h1 := hdeg k
      have h2 := hdeg₁ k
      simp only [Pi.add_apply, Pi.smul_apply, Option.elim_some, smul_eq_mul, Pi.single_apply, reduceCtorEq,
        if_false, mul_zero, add_zero, unitDeg] at h2 ⊢
      push_cast at h1 h2 ⊢
      simp only [ht] at h2
      linear_combination h1 - (n : ℤ) * h2
  have hvalGH : aeval (addBlock y v) G = s * aeval (addBlock y v) H := by
    have e1 : aeval (addBlock y v) G = aeval y g * aeval y q₁ ^ n * v j ^ n := by
      simp only [hG, map_mul, map_pow, aeval_rename, addBlock_comp_oldEmb, aeval_X]
      rfl
    have e2 : aeval (addBlock y v) H = aeval y h * aeval y r₁ ^ n := by
      simp only [hH, map_mul, map_pow, aeval_rename, addBlock_comp_oldEmb]
    rw [e1, e2, hval₁, he]
    ring
  have hsm := hs _ _ G H z hGh hHh hdegGH hvalGH hz
  simp only [hG, hH, map_mul, map_pow, eval_rename_old, map_X, eval_X, norm_mul, norm_pow] at hsm
  rw [← hw_def] at hsm

  set Gw := ‖eval w (map (Int.castRingHom ℂ) g)‖
  set Hw := ‖eval w (map (Int.castRingHom ℂ) h)‖
  set Q := ‖eval w (map (Int.castRingHom ℂ) q₁)‖
  set R := ‖eval w (map (Int.castRingHom ℂ) r₁)‖
  set M := N.h w ^ a
  have hb := B.h z
  have h1 : Gw * (Q * σ) ^ n * B.h z ^ n ≤ Hw * R ^ n * B.h z ^ n := by
    have e1 : Gw * (Q * σ) ^ n * B.h z ^ n = Gw * Q ^ n * ‖z ⟨none, j⟩‖ ^ n := by
      rw [← hσB]
      ring
    rw [e1]
    exact hsm
  have h2 : Gw * (Q * σ) ^ n ≤ Hw * R ^ n := le_of_mul_le_mul_right h1 (pow_pos hBpos n)
  have h3 : R ^ n ≤ (σ * (Q * M)) ^ n := pow_le_pow_left₀ (norm_nonneg _) hR n
  have h4 : Gw * (Q * σ) ^ n ≤ Hw * M ^ n * (Q * σ) ^ n := by
    calc Gw * (Q * σ) ^ n ≤ Hw * R ^ n := h2
      _ ≤ Hw * (σ * (Q * M)) ^ n := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = Hw * M ^ n * (Q * σ) ^ n := by ring
  have h5 := le_of_mul_le_mul_right h4 (pow_pos (mul_pos hQ hσpos) n)
  rw [pow_mul]
  exact h5

theorem smallSectionCount_mono {P P' : ℕ → Ω → Prop} {La La' : ℕ → AddSubgroup Ω} {τ τ' : ℕ}
    (h : ∀ s ∈ La τ, P τ s → s ∈ La' τ' ∧ P' τ' s) (hfin : {s : La' τ' | P' τ' (s : Ω)}.Finite) :
    smallSectionCount P La τ ≤ smallSectionCount P' La' τ' := by
  unfold smallSectionCount
  have : Finite {s : La' τ' // P' τ' (s : Ω)} := hfin.to_subtype
  have hcard : Nat.card {s : La τ // P τ (s : Ω)} ≤ Nat.card {s : La' τ' // P' τ' (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨s.1.1, (h s.1.1 s.1.2 s.2).1⟩, (h s.1.1 s.1.2 s.2).2⟩) fun s t hst => by
      simp only [Subtype.mk.injEq] at hst
      exact Subtype.ext (Subtype.ext hst)
  rcases Nat.eq_zero_or_pos (Nat.card {s : La τ // P τ (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end LiftBlockSections

end

end GroundTheory.Heights₂.Heights.Targets
