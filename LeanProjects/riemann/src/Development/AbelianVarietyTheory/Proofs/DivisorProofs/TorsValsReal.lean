import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.SiegelTor GlobalTheory.UT
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ThetaLevel

def TorsVals {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (T : Over S)
    (θ : LB.Sec (LPow P.A P.L 1 T)) (m : ℕ) {I : Type} (t : I → Γ(T.left, ⊤)) : Prop :=
  ∃ (pt : I → (T ⟶ P.A))
    (fr : ∀ a, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1))),
    (∀ a, IsTorsFrame P rig m (pt a) (fr a)) ∧ (∀ a, IsValueAt P.A P.L 1 θ (pt a) (fr a) (t a)) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ T.left) (z : Over.mk (x ≫ T.hom) ⟶ P.A), z ^ m = 1 →
      ∃ a, z.left = x ≫ (pt a).left

theorem torsVals_real {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    TorsVals ρ.P ρ.rig (baseOver (Sp S.R)) ρ.th₁ (S.r * S.N) (fun a => fn (⟨S.th a, S.th_mem a⟩ : S.R)) := by
  refine ⟨ρ.pt, ρ.fr, ρ.fr_tors, ρ.th_val, fun K _ _ x z hz => ?_⟩
  obtain ⟨a, ha, -⟩ := ρ.pt_bij K (x ≫ (baseOver (Sp S.R)).hom) z hz
  refine ⟨a, ?_⟩
  rw [← ha]
  exact congrArg (· ≫ (ρ.pt a).left) (Category.comp_id x)

theorem isGenSec_real {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := by
  intro s
  obtain ⟨r, hr, -⟩ := ρ.th₁_basis s
  exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩

end GlobalTheory.ThetaLevel
end
