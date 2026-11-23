import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open Filter Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfInt

theorem eulOf_of_faceMap_comp_succAbove_castSucc : E1 → faceMap_comp_succAbove_castSucc → E2 → E3 → EulOf := by
  intro hE1 hE1b hE2 hE3 hShim N _ χ D f a hf ha hs c δ S hA
  classical
  obtain ⟨⟨e, he⟩, -⟩ := hE1b
  have hp : ∀ v, (pOf v).Prime := fun v => by rw [← he v]; exact (e v).2
  have hinj : Function.Injective pOf := fun v w h =>
    e.injective (Subtype.ext (by rw [he, he, h]))
  have hM₀ : 0 < 4 * N * ∏ v ∈ S, pOf v := by
    have h1 := NeZero.pos N
    have h2 : 0 < ∏ v ∈ S, pOf v := Finset.prod_pos fun v _ => (hp v).pos
    positivity
  obtain ⟨M, hMz, c', hdvd, hc'⟩ := hE1 c hA.fin _ hM₀
  haveI := hMz
  have hNM : N ∣ M := (Dvd.intro_left 4 rfl |>.mul_right _).trans hdvd
  have h4M : 4 ∣ M := ((Dvd.intro _ rfl : 4 ∣ 4 * N).mul_right _).trans hdvd
  have hfin : {v : Pl | pOf v ∣ M}.Finite := by
    refine Set.Finite.of_finite_image (f := pOf) ((Nat.divisors M).finite_toSet.subset ?_)
      hinj.injOn
    rintro _ ⟨v, hv, rfl⟩
    exact Nat.mem_divisors.2 ⟨hv, NeZero.ne M⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset Pl, ∀ v, v ∈ T ↔ pOf v ∣ M :=
    ⟨hfin.toFinset, fun v => by simp⟩
  have hST : S ⊆ T := fun v hv =>
    (hT v).2 (((Finset.dvd_prod_of_mem _ hv).trans (Dvd.intro_left _ rfl)).trans hdvd)
  have hAT : admitted D c δ T :=
    ⟨hA.fin, hA.sgn, hA.bad.trans hST, fun v hv => hA.unr v fun h => hv (hST h)⟩
  obtain ⟨Λ₀, hd₀, ho₀, hΛ₀⟩ := hShim D.k N M hNM h4M D.three χ f a hf c'
  obtain ⟨hdE, hsplit, hlf⟩ := hE3 D c δ S hA
  have hsplitT := hsplit T hST
  have hb : ∀ v ∈ T \ S, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, 1 / 4 ≤ s.re → ‖lf3 (D.ν v) (localChar c v) s‖ ≤ C := fun v hv => by
    obtain ⟨C, hC⟩ := (hlf v (Finset.mem_sdiff.1 hv).2).2
    exact ⟨|C|, abs_nonneg C, fun s h => (hC s h).trans (le_abs_self C)⟩
  choose! Cv hCv0 hCv using hb
  have hPd : DifferentiableOn ℂ (fun s => ∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s) (HP 0) :=
    DifferentiableOn.fun_finset_prod fun v hv => (hlf v (Finset.mem_sdiff.1 hv).2).1
  have hsub : {s : ℂ | 1 / 4 < s.re} ⊆ HP 0 := fun s (h : 1 / 4 < s.re) =>
    show (0 : ℝ) < s.re by linarith
  have hsub1 : HP 1 ⊆ {s : ℂ | 1 / 4 < s.re} := fun s (h : 1 < s.re) =>
    show 1 / 4 < s.re by linarith
  have hΛd : DifferentiableOn ℂ
      (fun s => (∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s) * Λ₀ s) {s | 1 / 4 < s.re} :=
    (hPd.mono hsub).mul hd₀
  refine ⟨fun s => (∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s) * Λ₀ s, hΛd, ?_, ?_⟩
  · intro b
    obtain ⟨C₀, hC₀⟩ := ho₀ b
    have hP0 : 0 ≤ ∏ v ∈ T \ S, Cv v := Finset.prod_nonneg hCv0
    refine ⟨((∏ v ∈ T \ S, Cv v) + 1) * |C₀|, fun s h1 h2 => ?_⟩
    set P := ∏ v ∈ T \ S, Cv v with hPdef
    have hPs : ‖∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s‖ ≤ P := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        fun v hv => hCv v hv s (by linarith)
    have ht : 0 ≤ s.im ^ 2 := sq_nonneg _
    have hA0 : 0 ≤ |C₀| := abs_nonneg _
    have hΛs : ‖Λ₀ s‖ ≤ |C₀| * Real.exp (|C₀| * s.im ^ 2) := by
      refine (hC₀ s h1 h2).trans ?_
      have he1 : Real.exp (C₀ * s.im ^ 2) ≤ Real.exp (|C₀| * s.im ^ 2) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self _) ht)
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_left he1 hA0)
    have he2 : Real.exp (|C₀| * s.im ^ 2) ≤ Real.exp ((P + 1) * |C₀| * s.im ^ 2) := by
      refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ ht)
      nlinarith
    calc ‖(∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s) * Λ₀ s‖
        ≤ P * (|C₀| * Real.exp (|C₀| * s.im ^ 2)) := by
          rw [norm_mul]
          exact mul_le_mul hPs hΛs (norm_nonneg _) hP0
      _ ≤ (P + 1) * |C₀| * Real.exp (|C₀| * s.im ^ 2) := by
          have := Real.exp_pos (|C₀| * s.im ^ 2)
          nlinarith [mul_nonneg hA0 this.le]
      _ ≤ (P + 1) * |C₀| * Real.exp ((P + 1) * |C₀| * s.im ^ 2) :=
          mul_le_mul_of_nonneg_left he2 (by positivity)
  · have hopen : ∀ r : ℝ, IsOpen (HP r) := fun r => isOpen_lt continuous_const Complex.continuous_re
    have hconn : IsPreconnected (HP 1) := (convex_halfSpace_re_gt 1).isPreconnected
    have hg : AnalyticOnNhd ℂ
        (fun s => (∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s) * Λ₀ s) (HP 1) :=
      (hΛd.mono hsub1).analyticOnNhd (hopen 1)
    have hh : AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) ^ 1 * eul D c S s) (HP 1) :=
      (((differentiable_id.sub_const 1).pow 1).differentiableOn.mul hdE).analyticOnNhd (hopen 1)
    have h3 : (3 : ℂ) ∈ HP 1 := show (1 : ℝ) < (3 : ℂ).re by norm_num
    have hev : (fun s => (∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s) * Λ₀ s)
        =ᶠ[𝓝 (3 : ℂ)] fun s : ℂ => (s - 1) ^ 1 * eul D c S s := by
      have h32 : (3 : ℂ) ∈ HP 2 := show (2 : ℝ) < (3 : ℂ).re by norm_num
      filter_upwards [(hopen 2).mem_nhds h32] with s (h2 : 2 < s.re)
      rw [hsplitT s (by linarith), hΛ₀ s h2,
        hE2 N M hNM χ D a ha hs c δ T hAT hT c'
          (fun v hv => hc' v hv) s h2]
      ring
    intro s h1
    exact hg.eqOn_of_preconnected_of_eventuallyEq hh hconn h3 hev (show s ∈ HP 1 from h1)

end GlobalTheory.CompanionTheory.HalfInt

end
