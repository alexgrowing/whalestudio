import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift.OneSide

section Abstract

variable {n : ℕ} {Y S M : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup M] [Module ℂ M]

theorem exists_shift (A : Fin n → Fin n → Module.End ℂ S) (B : Fin n → Fin n → Module.End ℂ M)
    (hA : Formalism.REAL.GlRel A) (hB : Formalism.REAL.GlRel B) (L : Y → M →ₗ[ℂ] S) (lam : Fin n → Fin n → ℂ)
    (h : ∀ i j y f, A i j (L y f) = L y (B i j f + lam i j • f)) :
    ∃ c : ℂ, ∀ i j y f, A i j (L y f) =
      L y ((B i j + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) f) := by
  by_cases h0 : ∀ y f, L y f = 0
  · exact ⟨0, fun i j y f => by rw [h0, h0, map_zero]⟩
  push Not at h0
  obtain ⟨y, f, h0⟩ := h0
  have key : ∀ i j k l, (if j = k then lam i l else 0) = (if l = i then lam k j else 0) := by
    intro i j k l
    have h1 : (A i j * A k l - A k l * A i j) (L y f) = L y ((B i j * B k l - B k l * B i j) f) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, h, map_add, map_smul, map_sub, smul_add]
      module
    rw [hA, hB] at h1
    have h2 : ((if j = k then lam i l else 0) - (if l = i then lam k j else 0)) • L y f = 0 := by
      rw [sub_smul]
      split_ifs at h1 ⊢ <;>
        simp only [LinearMap.sub_apply, LinearMap.zero_apply, h, map_add, map_smul, map_sub, map_zero,
          zero_smul] at h1 ⊢ <;>
        linear_combination (norm := module) h1
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right h0)
  rcases n with _ | n
  · exact ⟨0, fun i => i.elim0⟩
  refine ⟨lam 0 0, fun i j y f => ?_⟩
  rw [h]
  by_cases c : i = j
  · subst c
    have := key i 0 0 i
    simp only [if_true] at this
    simp [this]
  · have := key i i i j
    simp only [if_true, if_neg (Ne.symm c)] at this
    simp [this, c]

theorem prod_intertwine (L : M →ₗ[ℂ] S) : ∀ (k : ℕ) (a : Fin k → Module.End ℂ S) (b : Fin k → Module.End ℂ M),
    (∀ i f, a i (L f) = L (b i f)) → ∀ f, (List.ofFn a).prod (L f) = L ((List.ofFn b).prod f)
  | 0, _, _, _, f => by simp
  | k + 1, a, b, e, f => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply,
      prod_intertwine L k _ _ fun i => e i.succ, e]

theorem gelfA_intertwine (L : M →ₗ[ℂ] S) (A : Fin n → Fin n → Module.End ℂ S) (B : Fin n → Fin n → Module.End ℂ M)
    (h : ∀ i j f, A i j (L f) = L (B i j f)) (k : ℕ) (f : M) :
    GlobalTheory.SmoothForms.gelfA A k (L f) = L (GlobalTheory.SmoothForms.gelfA B k f) := by
  rw [GlobalTheory.SmoothForms.gelfA, GlobalTheory.SmoothForms.gelfA, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun idx _ => prod_intertwine L _ _ _ (fun _ => h _ _) f

end Abstract

theorem gelf_kernel : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ (Y M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (Y → GA D V → ℂ)), (∀ f y, κ f y ∈ SmFun θ V) → ∀ (τ : D.what₂.Tau) (Q : Matrix (Fin V.rank) (Fin V.rank) ℂ →ₗ[ℂ] Module.End ℂ M), Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1)) → (∀ X ∈ lieAt V τ, ∃ lam : ℂ, ∀ f y g, HasDerivAt (fun t : ℝ => κ f y (g * oneP θ V τ X t)) (κ (Q X f + lam • f) y g) 0) → ∃ c : ℂ, ∀ k f y, gelf θ V τ k (κ f y) = κ (GlobalTheory.SmoothForms.gelfA (fun i j => Q (Matrix.single i j 1) + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) k f) y := by
  intro D θ hθ V Y M _ _ κ hκ τ Q hQ hd
  choose lam hlam using hd
  have hR : ∀ X (hX : X ∈ lieAt V τ) f y, Rder θ V τ X (κ f y) = κ (Q X f + lam X hX • f) y :=
    fun X hX f y => funext fun g => (hlam X hX f y g).deriv
  have hC : ∀ Z, ∃ l : ℂ, ∀ f y, RderC θ V τ Z (κ f y) = κ (Q Z f + l • f) y := by
    intro Z
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    refine ⟨lam _ h1 + Complex.I * lam _ h2, fun f y => ?_⟩
    rw [RderC, hR _ h1, hR _ h2]
    have e := GlobalTheory.SmoothAutCheck.parts_sum V τ Z
    generalize lam _ h1 = a
    generalize lam _ h2 = b
    generalize (1 / 2 : ℂ) • (Z + conjAt V τ Z) = P at e ⊢
    generalize (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) = P' at e ⊢
    rw [← e]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply]
    module
  choose l hl using hC
  let L : Y → M →ₗ[ℂ] SmFun θ V := fun y =>
    LinearMap.codRestrict (SmFun θ V) ((LinearMap.proj y).comp κ) fun f => hκ f y
  obtain ⟨c, hc⟩ := exists_shift _ _ (glRel_derEnd hθ V τ) hQ L (fun i j => l (Matrix.single i j 1))
    fun i j y f => Subtype.ext (hl _ f y)
  refine ⟨c, fun k f y => ?_⟩
  have := gelfA_intertwine (L y) _ (fun i j => Q (Matrix.single i j 1) +
    if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) (fun i j => hc i j y) k f
  exact (GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (L y f)).trans (congrArg Subtype.val this)

end GlobalTheory.Mem.Lift.OneSide

end
