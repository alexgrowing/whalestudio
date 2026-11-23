import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem existsUnique_isTwistPull : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (T : Over S) (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])), α.IsGen → ∀ s : LB.Sec (LPow A L b T), ∃! s' : LB.Sec (LPow A L a T), IsTwistPull A L ψ m hm a b α s s' := by
  intro S A _ L hL T ψ m hm a b α hα s
  obtain ⟨s₀, hs₀⟩ := ThetaPtExist.exists_isTwistPull hL ψ m hm a b α hα s
  refine ⟨s₀, hs₀, fun s₁ hs₁ => ?_⟩

  have hf : ∀ j, s₁.f j = s₀.f j :=
    sec_ext_val (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) hL
      (fun y J hJ => (twist_val hs₁ (𝟙 _) y hJ).trans (twist_val hs₀ (𝟙 _) y hJ).symm)

  obtain ⟨f₁, c₁⟩ := s₁
  obtain ⟨f₀, c₀⟩ := s₀
  obtain rfl : f₁ = f₀ := funext hf
  rfl

end GlobalTheory
