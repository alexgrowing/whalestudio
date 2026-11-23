import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.ConjSch

open scoped Classical

noncomputable def conjSch {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := star (f x)
  smooth' := (Complex.conjLIE.toContinuousLinearEquiv.contDiff).comp f.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => star (f x)) = Complex.conjLIE ∘ f := rfl
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjSch_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSch f x = star (f x) := rfl

theorem star_mem_schA {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨conjSch f, fun y => star (g y),
      ⟨hg.1.comp _, hg.2.comp_left (g := star) (star_zero _)⟩, ?_⟩
    funext y
    simp only [pureA, conjSch_apply, star_mul', mul_comm]
  | zero =>
    simp only [Pi.zero_apply, star_zero]
    exact (schA F κ).zero_mem
  | add x y _ _ hx hy =>
    have := (schA F κ).add_mem hx hy
    convert this using 1
    funext z; simp
  | smul c x _ hx =>
    have := (schA F κ).smul_mem (star c) hx
    convert this using 1
    funext z; simp [star_mul', mul_comm]

end GlobalTheory.ConjSch

theorem GlobalTheory.star_mem_schA_main : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ :=
  fun κ _ => GlobalTheory.ConjSch.star_mem_schA κ
