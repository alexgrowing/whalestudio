import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelDominatedOfMapToBaseModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models.Domination

theorem dominates_of_above : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (R O' : Type) [CommRing R] [CommRing O'] (ω : R →+* c.F) (β' : O' →+* c.F) (bR : RZ H (n * l₀.M) 1 →+* R) (C : Model (Xo l) c ω) (Y' : Model (Xo l) c β') (b' : R →+* O') (k : KA l₀ →+* c.F) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap C.oF.t (Xo l₀).univ.t r), r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k → IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k → LevComp C.oF (Xo l₀).univ r ν → (ofModel C).Above B.C bR r ν → IsDedFrac ω → IsDedFrac β' → β'.comp b' = ω → Raises B Y' → Dominates C Y' b' := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N T l₀ l B c R O' _ _ ω β' bR C Y' b' k r ν hr hk hlev A hω hβ' hb hR
  obtain ⟨_, _, _, _, _, m₁, -⟩ := sabPull Out.CubePf.cubePull (pullback.fst C.s (spMap b')) C.t
  obtain ⟨m₂, hm₂⟩ := GlobalTheory.LevelCover.sab_comp m₁ A.mu rfl
  refine dominates_of_map_to_base L₁ L₂ L₃ E H D Xo n N T l₀ l B c R O' ω β' C Y' b' _ _ m₁ m₂ r ν k hω hβ' hb hR
    hlev hk hr (fun g hg => ?_) (fun y hy => ?_)
  · have hj : C.j ≫ A.π = r ≫ B.C.j := A.j_comm
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ A.π) hg).trans hj)
  · have hφ : C.m.φ ≫ A.mu.φ = ν.φ ≫ B.C.m.φ := A.φ_comm
    rw [hm₂, ← Category.assoc, hy, hφ]

end GlobalTheory.Models.Domination
