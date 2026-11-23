import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChainPts
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.VB

theorem IsFrame.of_retract {X : Scheme.{0}} {F F₁ : X.Modules} (i : F₁ ⟶ F) (q : F ⟶ F₁)
    (hiq : i ≫ q = 𝟙 F₁) {r r' : ℕ} (σ : Fin r' → Fin r) (hσ : Function.Injective σ)
    {U : X.Opens} (s : Fin r → Γ(F, U)) (hs : GlobalTheory.VB.IsFrame s)
    (h₁ : ∀ k, i.app U (q.app U (s (σ k))) = s (σ k))
    (h₀ : ∀ j, j ∉ Set.range σ → q.app U (s j) = 0) :
    GlobalTheory.VB.IsFrame (fun k => q.app U (s (σ k))) := by
  refine isFrame_iff.2 fun V h => ?_
  obtain ⟨hli, hsp⟩ := isFrame_iff.1 hs V h
  constructor
  · refine LinearIndependent.of_comp (GlobalTheory.QCoh.appLinear i V) ?_
    have e : (GlobalTheory.QCoh.appLinear i V) ∘ (fun k => Twist.resM F₁ h (q.app U (s (σ k)))) =
        (fun j => Twist.resM F h (s j)) ∘ σ := by
      funext k
      exact (Twist.app_resM i h _).trans (congrArg _ (h₁ k))
    rw [e]
    exact hli.comp σ hσ
  · intro x _
    have hx : GlobalTheory.QCoh.appLinear q V (i.app V x) = x := by
      refine (GlobalTheory.QCoh.app_app i q V x).trans ?_
      rw [hiq]
      rfl
    have hle : Submodule.span Γ(X, V) (Set.range fun j => Twist.resM F h (s j)) ≤
        (Submodule.span Γ(X, V) (Set.range fun k => Twist.resM F₁ h (q.app U (s (σ k))))).comap
          (GlobalTheory.QCoh.appLinear q V) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      change q.app V (Twist.resM F h (s j)) ∈ Submodule.span Γ(X, V) _
      rw [Twist.app_resM]
      by_cases hj : j ∈ Set.range σ
      · obtain ⟨k, rfl⟩ := hj
        exact Submodule.subset_span ⟨k, rfl⟩
      · rw [h₀ j hj, map_zero]
        exact zero_mem _
    rw [← hx]
    exact hle (hsp Submodule.mem_top)

end GlobalTheory.VB
