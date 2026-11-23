import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem sub_smooth {f : X → HV E a} {x : X} (h : ContDiffAt ℝ ∞ (fun y => (f y).1) x) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨r, hr⟩ := (HV E a).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have e : f = fun y => LinearMap.toContinuousLinearMap r (f y).1 :=
    funext fun y => (LinearMap.congr_fun hr (f y)).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap r).contDiff.contDiffAt.comp x h

private theorem sand_smooth {σ : X → GL (Fin a) (Cinf E)} {v : X → HV E a} {x : X}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => (σ y).val i j) x) (hv : ∀ i j, ContDiffAt ℝ ∞ (fun y => (v y).1 i j) x) :
    ContDiffAt ℝ ∞ (fun y => sand (σ y) (v y)) x := by
  refine sub_smooth (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_)
  have e : (fun y => (sand (σ y) (v y)).1 i j) =
      fun y => ∑ l, (∑ k, (σ y).val i k * (v y).1 k l) * star ((σ y).val j l) := by
    funext y
    change ((σ y).val * Matrix.of (v y).1 * star (σ y).val) i j = _
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiffAt.sum fun l _ => (ContDiffAt.sum fun k _ => (h i k).mul (hv k l)).mul ?_
  exact (starL' ℝ : Cinf E ≃L[ℝ] Cinf E).contDiff.contDiffAt.comp x (h j l)

end UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.fieldSm :
    FieldSm := by
  intro E _ _ _ a U Y C hY W hW s p₀ hp₀
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ∞ (fun p => sand (τ p) (hv (Y (infGL E a (τ p) * finGL E a x)))) p₀ := by
    refine sand_smooth (fun i j => contDiffAt_pi.1 (contDiffAt_pi.1 hτ i) j) fun i j => contDiffAt_pi.2 fun w => ?_
    obtain ⟨φ, hφ, -⟩ := hY.sm i j w
    have := (contDiffAt_chart φ.2 (finGL E a x) (val_mem_invSet (τ p₀))).comp p₀ hτ
    simp only [Function.comp_def, chart_val, hφ] at this
    simp only [infGL_comm]
    exact this
  refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
  have := hW (τ p) x
  rwa [hp] at this
