import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGroupTest

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.ThetaScalar

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}

def noCharts (X : Scheme.{0}) : LB X := ⟨PEmpty, PEmpty.elim, fun i => i.elim⟩

theorem weilIs_noCharts (k : ℤ) (x y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ) : WeilIs A (noCharts A.left) k x y c :=
  fun _ => ⟨⊤, trivial,
    ⟨⟨_, ⟨fun j => (j 0).elim⟩, fun j => (j 0).elim⟩, ⟨_, ⟨fun j => (j 0).elim⟩, fun j => (j 0).elim⟩, rfl, rfl⟩,
    fun _ _ _ _ j => (j (Sum.inl 0)).elim⟩

theorem not_isLB_noCharts (X : Scheme.{0}) [Nonempty X] : ¬ (noCharts X).IsLB := fun h => by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : x ∈ ⨆ i, (noCharts X).U i := h.cover ▸ trivial
  obtain ⟨i, -⟩ := Opens.mem_iSup.1 hx
  exact i.elim

theorem weilIs_unique_of_local (p : T.left) (hp : ∀ V : T.left.Opens, p ∈ V → V = ⊤) (hL : L.IsLB) {x y : T ⟶ A}
    {c c' : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k x y c) (h' : WeilIs A L k x y c') :
    unitRes (T := T) ⊤ c = unitRes (T := T) ⊤ c' := by
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', -, H'⟩ := h' p
  obtain rfl := hp V hV
  obtain rfl := hp V' hV'
  exact commIsOf_unique hL θx θy _ _ (H θx θy hx hy) (H' θx θy hx hy)

end GlobalTheory.ThetaGroupTest
