import Mathlib
import GroundTheory.PAdicHodge.TiltAlgebra
import GroundTheory.PAdicHodge.OrthoBasis
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

theorem exists_lt_mul_mul_lt_one {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ q < s * s * s := by
  refine ⟨(3 + q) / 4, by linarith, by linarith, ?_⟩
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 27 - 10 * q - q * q := by nlinarith
  nlinarith [mul_pos h1 h2]

section

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

omit [IsUltrametricDist K] [IsUltrametricDist C] [Fact p.Prime] [IsPerfectoidField K p]
  [IsPerfectoidField C p] in

theorem norm_natCast_algebra : ‖(p : C)‖ = ‖(p : K)‖ := by
  rw [← map_natCast (algebraMap K C), norm_algebraMap']

omit [NontriviallyNormedField K] [IsUltrametricDist K] [NontriviallyNormedField C] [NormedAlgebra K C]
  [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p] in

theorem norm_eq_of_norm_sub_lt {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {x y : E} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne
  rw [sub_add_cancel, max_eq_right h.le] at this
  exact this

theorem lt_norm_sum_smul_tiltSharp {ι : Type*} [Fintype ι] {w : ι → C♭} {t r ρ : ℝ}
    (hw : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwr : ∀ i, r < ‖w i‖) (ht : 0 < t) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (hp : ‖(p : K)‖ ≤ t * r * ρ) {l : ι → K} (hl1 : ∀ i, ‖l i‖ ≤ 1) {j : ι} (hj : ρ < ‖l j‖) :
    t * r * ρ < ‖∑ i, l i • tiltSharp C p (w i)‖ := by
  classical
  have hwj0 : 0 < ‖w j‖ := hr.trans_lt (hwr j)

  have ht1 : t ≤ 1 := by
    have e : ∑ j', (Pi.single j (1 : K♭) : ι → K♭) j' • w j' = w j := by
      rw [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]
    have := hw (Pi.single j 1) j
    rw [e, Pi.single_eq_same, one_smul] at this
    exact le_of_mul_le_mul_right (by linarith) hwj0
  have hr1 : r < 1 := (hwr j).trans_le (hw1 j)
  have htr : t * r ≤ 1 := by nlinarith
  have hpρ : ‖(p : K)‖ ≤ ρ := hp.trans (by nlinarith)
  have hpl : ‖(p : K)‖ < ‖l j‖ := hpρ.trans_lt hj

  have hA : ∀ i, ∃ a : 𝒪K♭, ‖((a.untilt : normInteger K) : K) - l i‖ ≤ ‖(p : K)‖ := fun i => by
    obtain ⟨a, ha⟩ := exists_mk_untilt_eq (p := p)
      (⟨l i, mem_normInteger.2 (hl1 i)⟩ : normInteger K)
    exact ⟨a, mk_eq_mk_iff_norm_sub_le.1 ha⟩
  choose a ha using hA
  choose b hb using fun i => (norm_le_one_iff_exists_algebraMap (K := C) (p := p)).1 (hw1 i)
  set φ := preTiltMap p (algebraMap K C) (norm_algebraMap' C) with hφ
  set d : ι → 𝒪C♭ := fun i => φ (a i) * b i with hd
  have hdw : ∀ i, algebraMap 𝒪C♭ C♭ (d i) = algebraMap 𝒪K♭ K♭ (a i) • w i := by
    intro i
    rw [Algebra.smul_def, algebraMap_tilt_eq, tiltMap_algebraMap, ← hb i, ← map_mul]
  have hsharp : ∀ i, tiltSharp C p (w i) = ((b i).untilt : C) := by
    intro i; rw [← hb i, tiltSharp_algebraMap]
  have hdu : ∀ i, ((d i).untilt : C) = algebraMap K C ((a i).untilt : K) * tiltSharp C p (w i) := by
    intro i
    rw [hd, untilt_mul, Subring.coe_mul, coe_untilt_preTiltMap, hsharp]
  set A : C := ((∑ i, d i).untilt : C) with hA

  have hAn : ‖A‖ = ‖∑ i, algebraMap 𝒪K♭ K♭ (a i) • w i‖ := by
    rw [hA, ← tiltSharp_algebraMap, norm_tiltSharp, map_sum]
    simp only [hdw]
  have hsw : ∀ i, ‖tiltSharp C p (w i)‖ ≤ 1 := fun i => by rw [norm_tiltSharp]; exact hw1 i

  have haj : ‖algebraMap 𝒪K♭ K♭ (a j)‖ = ‖l j‖ := by
    rw [norm_algebraMap_preTilt, preTilt_norm_def]
    exact norm_eq_of_norm_sub_lt ((ha j).trans_lt hpl)
  have hAbig : t * r * ρ < ‖A‖ := by
    rw [hAn]
    refine lt_of_lt_of_le ?_ (hw _ j)
    rw [norm_smul, haj]
    have : ρ * r < ‖l j‖ * ‖w j‖ :=
      mul_lt_mul'' hj (hwr j) hρ.le hr
    nlinarith

  have hS : ‖∑ i, ((d i).untilt : C) - A‖ ≤ ‖(p : K)‖ := by
    rw [norm_sub_rev, hA, ← norm_natCast_algebra (C := C)]
    exact norm_untilt_sum_sub_le Finset.univ d
  have hT : ‖∑ i, l i • tiltSharp C p (w i) - ∑ i, ((d i).untilt : C)‖ ≤ ‖(p : K)‖ := by
    rw [← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [hdu, Algebra.smul_def, ← sub_mul, ← map_sub, norm_mul, norm_algebraMap', norm_sub_rev]
    calc ‖((a i).untilt : K) - l i‖ * ‖tiltSharp C p (w i)‖ ≤ ‖(p : K)‖ * 1 := by
          gcongr
          · exact ha i
          · exact hsw i
      _ = _ := mul_one _
  have hE : ‖∑ i, l i • tiltSharp C p (w i) - A‖ ≤ ‖(p : K)‖ := by
    have e : ∑ i, l i • tiltSharp C p (w i) - A =
        (∑ i, l i • tiltSharp C p (w i) - ∑ i, ((d i).untilt : C)) +
          (∑ i, ((d i).untilt : C) - A) := by abel
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hT hS)
  rw [norm_eq_of_norm_sub_lt (hE.trans_lt (hp.trans_lt hAbig))]
  exact hAbig

theorem mul_norm_le_norm_sum_smul_tiltSharp {ι : Type*} [Fintype ι] {w : ι → C♭} {t r ρ : ℝ}
    (hw : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwr : ∀ i, r < ‖w i‖) (ht : 0 < t) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hp : ‖(p : K)‖ ≤ t * r * ρ) (l : ι → K) (i : ι) :
    t * r * ρ * ‖l i‖ ≤ ‖∑ j, l j • tiltSharp C p (w j)‖ := by
  by_cases hli : l i = 0
  · rw [hli, norm_zero, mul_zero]; exact norm_nonneg _
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun j => ‖l j‖)
    ⟨i, Finset.mem_univ i⟩
  set m := ‖l i0‖ with hm
  have hli0 : ‖l i‖ ≤ m := hi0 i (Finset.mem_univ i)
  have hm0 : 0 < m := (norm_pos_iff.2 hli).trans_le hli0
  obtain ⟨c, hc1, hc2⟩ := exists_norm_mem_Ioc p (K := K) (div_pos hρ hm0)
    (div_lt_div_of_pos_right hρ1 hm0)
  have hc0 : 0 < ‖c‖ := (div_pos hρ hm0).trans hc1
  have hcm : ‖c‖ * m ≤ 1 := by rwa [le_div_iff₀ hm0] at hc2
  have hcm' : ρ < ‖c‖ * m := by rwa [div_lt_iff₀ hm0] at hc1
  have key := lt_norm_sum_smul_tiltSharp (C := C) hw hw1 hwr ht hr hρ hp
    (l := fun j => c * l j) (j := i0)
    (fun j => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hi0 j (Finset.mem_univ j)) (norm_nonneg c)).trans hcm)
    (by rw [norm_mul]; exact hcm')
  have e : ∑ j, (c * l j) • tiltSharp C p (w j) = c • ∑ j, l j • tiltSharp C p (w j) := by
    rw [Finset.smul_sum]; simp only [mul_smul]
  rw [e, norm_smul] at key
  have hX := norm_nonneg (∑ j, l j • tiltSharp C p (w j))
  have htrρ : 0 ≤ t * r * ρ := by positivity
  calc t * r * ρ * ‖l i‖ ≤ t * r * ρ * m := by gcongr
    _ ≤ ‖c‖ * ‖∑ j, l j • tiltSharp C p (w j)‖ * m := by gcongr
    _ = (‖c‖ * m) * ‖∑ j, l j • tiltSharp C p (w j)‖ := by ring
    _ ≤ 1 * ‖∑ j, l j • tiltSharp C p (w j)‖ := by gcongr
    _ = _ := one_mul _

theorem linearIndependent_tiltSharp {ι : Type*} [Fintype ι] {w : ι → C♭} {t r ρ : ℝ}
    (hw : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwr : ∀ i, r < ‖w i‖) (ht : 0 < t) (hr : 0 < r) (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hp : ‖(p : K)‖ ≤ t * r * ρ) :
    LinearIndependent K (fun i => tiltSharp C p (w i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := mul_norm_le_norm_sum_smul_tiltSharp (C := C) hw hw1 hwr ht hr.le hρ hρ1 hp g i
  rw [hg, norm_zero] at h
  have hpos : 0 < t * r * ρ := by positivity
  have : ‖g i‖ ≤ 0 := by nlinarith [norm_nonneg (g i)]
  exact norm_le_zero_iff.1 this

theorem exists_orthogonal_normalized {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) {t r : ℝ} (ht : t < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ w : ι → C♭, LinearIndependent K♭ w ∧ (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧
      (∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖) ∧
      ∀ i, ‖w i‖ ≤ 1 ∧ r < ‖w i‖ := by
  obtain ⟨w', hli, hspan, horth⟩ := exists_orthogonal_of_linearIndependent hv ht
  have hw'0 : ∀ i, 0 < ‖w' i‖ := fun i => norm_pos_iff.2 (hli.ne_zero i)
  have hE : ∀ i, ∃ e : K♭, r / ‖w' i‖ < ‖e‖ ∧ ‖e‖ ≤ 1 / ‖w' i‖ := fun i =>
    exists_norm_mem_Ioc p (div_pos hr0 (hw'0 i)) (div_lt_div_of_pos_right hr1 (hw'0 i))
  choose e he1 he2 using hE
  have he0 : ∀ i, e i ≠ 0 := fun i => norm_pos_iff.1 ((div_pos hr0 (hw'0 i)).trans (he1 i))
  have hsmul : ∀ c : ι → K♭, ∑ j, c j • (e j • w' j) = ∑ j, (c j * e j) • w' j := fun c => by
    simp only [mul_smul]
  refine ⟨fun i => e i • w' i, ?_, fun i => Submodule.smul_mem _ _ (hspan i), ?_, fun i => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [hsmul] at hg
    have := (Fintype.linearIndependent_iff.1 hli) _ hg i
    exact (mul_eq_zero.1 this).resolve_right (he0 i)
  · intro c i
    rw [hsmul, ← mul_smul]
    exact horth (fun j => c j * e j) i
  · rw [norm_smul]
    constructor
    · calc ‖e i‖ * ‖w' i‖ ≤ 1 / ‖w' i‖ * ‖w' i‖ := by gcongr; exact he2 i
        _ = 1 := one_div_mul_cancel (hw'0 i).ne'
    · calc r = r / ‖w' i‖ * ‖w' i‖ := (div_mul_cancel₀ r (hw'0 i).ne').symm
        _ < ‖e i‖ * ‖w' i‖ := mul_lt_mul_of_pos_right (he1 i) (hw'0 i)

theorem exists_tiltSharp_family {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) :
    ∃ (w : ι → C♭) (t r ρ : ℝ), 0 < t ∧ t < 1 ∧ 0 < r ∧ r < 1 ∧ 0 < ρ ∧ ρ < 1 ∧
      ‖(p : K)‖ ≤ t * r * ρ ∧ LinearIndependent K♭ w ∧
      (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧
      (∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖) ∧
      (∀ i, ‖w i‖ ≤ 1 ∧ r < ‖w i‖) ∧
      ∀ (l : ι → K) (i : ι), t * r * ρ * ‖l i‖ ≤ ‖∑ j, l j • tiltSharp C p (w j)‖ := by
  obtain ⟨s, hs0, hs1, hs⟩ := exists_lt_mul_mul_lt_one (norm_nonneg (p : K))
    (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p))
  obtain ⟨w, hli, hspan, horth, hnorm⟩ := exists_orthogonal_normalized (K := K) (C := C) hv hs1 hs0 hs1
  exact ⟨w, s, s, s, hs0, hs1, hs0, hs1, hs0, hs1, hs.le, hli, hspan, horth, hnorm,
    mul_norm_le_norm_sum_smul_tiltSharp horth (fun i => (hnorm i).1) (fun i => (hnorm i).2)
      hs0 hs0.le hs0 hs1 hs.le⟩

theorem exists_tiltSharp_linearIndependent {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) :
    ∃ w : ι → C♭, (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧ (∀ i, ‖w i‖ ≤ 1) ∧
      LinearIndependent K♭ w ∧ LinearIndependent K (fun i => tiltSharp C p (w i)) := by
  obtain ⟨w, t, r, ρ, ht0, -, hr0, -, hρ0, hρ1, hp, hli, hspan, horth, hnorm, -⟩ :=
    exists_tiltSharp_family (K := K) (C := C) hv
  exact ⟨w, hspan, fun i => (hnorm i).1, hli,
    linearIndependent_tiltSharp horth (fun i => (hnorm i).1) (fun i => (hnorm i).2) ht0 hr0 hρ0
      hρ1 hp⟩

end

end GroundTheory.PAdicHodge
