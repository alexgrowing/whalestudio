import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst

open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.InterpCurv

theorem ddbar_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {f g : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (ξ η : E) :
    ddbar (fun x => f x * g x) z ξ η = f z * ddbar g z ξ η + del f z ξ * dbar g z η
      + del g z ξ * dbar f z η + g z * ddbar f z ξ η := by
  have hfg : ContDiffAt ℝ 2 (fun x => f x * g x) z := hf.mul hg
  have hf1 : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ f x :=
    (hf.eventually (by simp)).mono fun x hx => hx.differentiableAt two_ne_zero
  have hg1 : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ g x :=
    (hg.eventually (by simp)).mono fun x hx => hx.differentiableAt two_ne_zero
  have he : (fun x => dbar (fun y => f y * g y) x η) =ᶠ[𝓝 z]
      fun x => f x * dbar g x η + dbar f x η * g x := by
    filter_upwards [hf1, hg1] with x h1 h2
    exact dbar_mul h1 h2 η
  have df : DifferentiableAt ℝ f z := hf.differentiableAt two_ne_zero
  have dg : DifferentiableAt ℝ g z := hg.differentiableAt two_ne_zero
  have dgb := differentiableAt_dbar_apply hg η
  have dfb := differentiableAt_dbar_apply hf η
  rw [ddbar_eq_del_dbar hfg, del_congr he, del_add (df.fun_mul dgb) (dfb.fun_mul dg),
    ContinuousLinearMap.add_apply, del_mul df dgb, del_mul dfb dg,
    ← ddbar_eq_del_dbar hg, ← ddbar_eq_del_dbar hf]
  ring

section Frame

variable {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]

theorem contDiffAt_form {k : WithTop ℕ∞} {H : (ι → ℂ) → Matrix n n ℂ} {z : ι → ℂ}
    (h : MContDiffAt k H z) (v w : n → ℂ) : ContDiffAt ℝ k (fun x => form (H x) v w) z := by
  simp only [form_eq_sum]
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
    (contDiffAt_const.mul (h a b)).mul contDiffAt_const

theorem del_form_const {H : (ι → ℂ) → Matrix n n ℂ} {z : ι → ℂ} (h : MContDiffAt 1 H z)
    (hu : IsUnit (H z).det) (ξ : ι → ℂ) (v : n → ℂ) :
    del (fun x => form (H x) v v) z ξ = form (H z) (conn H z ξ *ᵥ v) v := by
  have h0 : (fun a => dbar (fun _ : ι → ℂ => v a) z ξ) = 0 := by funext a; simp
  have h1 : (fun a => del (fun _ : ι → ℂ => v a) z ξ) = 0 := by funext a; simp
  rw [del_form (s := fun _ => v) (t := fun _ => v) h hu (fun _ => contDiffAt_const)
    (fun _ => contDiffAt_const) ξ, covDel, h1, zero_add, h0]
  simp [form]

theorem dbar_form_const {H : (ι → ℂ) → Matrix n n ℂ} {z : ι → ℂ} (h : MContDiffAt 1 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det) (ξ : ι → ℂ) (v : n → ℂ) :
    dbar (fun x => form (H x) v v) z ξ = form (H z) v (conn H z ξ *ᵥ v) := by
  have he : (fun x => form (H x) v v) =ᶠ[𝓝 z] fun x => starRingEnd ℂ (form (H x) v v) :=
    hh.mono fun x hx => (conj_form hx v v).symm
  rw [dbar_congr he, dbar_conj, del_form_const h hu, conj_form hh.self_of_nhds]

theorem ddbar_form_interp {H₀ H : (ι → ℂ) → Matrix n n ℂ} {s : (ι → ℂ) → ℝ} {z : ι → ℂ}
    (hH₀ : MContDiffAt 2 H₀ z) (hH : MContDiffAt 2 H z) (hs : ContDiffAt ℝ 2 s z)
    (hh₀ : ∀ᶠ x in 𝓝 z, (H₀ x).IsHermitian) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu₀ : IsUnit (H₀ z).det) (hu : IsUnit (H z).det) (ξ : ι → ℂ) (v : n → ℂ) :
    ddbar (fun x => form (interp H₀ H s x) v v) z ξ ξ =
      ((1 - s z : ℝ) : ℂ) * ddbar (fun x => form (H₀ x) v v) z ξ ξ +
      (s z : ℂ) * ddbar (fun x => form (H x) v v) z ξ ξ +
      (form (H z) v v - form (H₀ z) v v) * leviForm s z ξ ξ +
      del (fun x => (s x : ℂ)) z ξ *
        (form (H z) v (conn H z ξ *ᵥ v) - form (H₀ z) v (conn H₀ z ξ *ᵥ v)) +
      starRingEnd ℂ (del (fun x => (s x : ℂ)) z ξ) *
        (form (H z) (conn H z ξ *ᵥ v) v - form (H₀ z) (conn H₀ z ξ *ᵥ v) v) := by
  have hV : (fun x => form (interp H₀ H s x) v v) = fun x =>
      ((1 - s x : ℝ) : ℂ) * form (H₀ x) v v + (s x : ℂ) * form (H x) v v := by
    funext x; simp only [interp, form_add, form_smul]
  have ht : ContDiffAt ℝ 2 (fun x => ((1 - s x : ℝ) : ℂ)) z :=
    contDiffAt_ofReal_comp (contDiffAt_const.sub hs)
  have hσ : ContDiffAt ℝ 2 (fun x => (s x : ℂ)) z := contDiffAt_ofReal_comp hs
  have ha := contDiffAt_form hH₀ v v
  have hb := contDiffAt_form hH v v
  have h1 : ddbar (fun x => ((1 - s x : ℝ) : ℂ)) z ξ ξ = -leviForm s z ξ ξ := by
    change leviForm (fun x => 1 - s x) z ξ ξ = _
    rw [leviForm_sub contDiffAt_const hs, leviForm_const]; simp
  have h2 : del (fun x => ((1 - s x : ℝ) : ℂ)) z ξ = -del (fun x => (s x : ℂ)) z ξ := by
    have : (fun x => ((1 - s x : ℝ) : ℂ)) = fun x => 1 - (s x : ℂ) := by funext x; push_cast; rfl
    rw [this, del_sub (differentiableAt_const _) (hσ.differentiableAt two_ne_zero)]
    simp
  have h3 : dbar (fun x => ((1 - s x : ℝ) : ℂ)) z ξ = -starRingEnd ℂ (del (fun x => (s x : ℂ)) z ξ) := by
    rw [dbar_ofReal, h2, map_neg]
  have h4 : dbar (fun x => (s x : ℂ)) z ξ = starRingEnd ℂ (del (fun x => (s x : ℂ)) z ξ) :=
    dbar_ofReal _ _ _
  have h5 : ddbar (fun x => (s x : ℂ)) z ξ ξ = leviForm s z ξ ξ := rfl
  have h1' := hH₀.of_le one_le_two
  have h1'' := hH.of_le one_le_two
  rw [hV, ddbar_add (ht.mul ha) (hσ.mul hb), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, ddbar_mul ht ha, ddbar_mul hσ hb, h1, h2, h3, h4, h5,
    del_form_const h1' hu₀, del_form_const h1'' hu, dbar_form_const h1' hh₀ hu₀,
    dbar_form_const h1'' hh hu]
  ring

end Frame

end GlobalTheory.InterpCurv
