import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm

namespace GlobalTheory.HeightParts

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {K : Type} [Field K] [NumberField K] {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X}

def lieCoordLat (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) {n : ℕ} (b : Fin n → TanM xK t.G) :
    Submodule (𝓞 K) (Fin n → K) where
  carrier := {c | ∃ w : TanM xO t.G, bcTan (algebraMap (𝓞 K) K) hx w = ∑ i, c i • b i}
  add_mem' := by
    rintro c c' ⟨w, hw⟩ ⟨w', hw'⟩
    refine ⟨w + w', ?_⟩
    rw [map_add, hw, hw', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a c ⟨w, hw⟩
    refine ⟨a • w, ?_⟩
    rw [map_smulₛₗ, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Algebra.smul_def, mul_smul]

end Lat

variable {D : D7} (O : Setup D)

def IsLieAt (y : Pt O.s) (K : Type) [Field K] [NumberField K] (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K))
    (h : HermFam K (Fin (D.R.f * O.N) → K)) : Prop :=
  ∃ (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) (io : K →+* Qb) (fK : O.κ.c.F →+* K) (yK : Sp K ⟶ gen O.s.T.Z)
    (xO : Sp (𝓞 K) ⟶ O.s.T.Z.X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = yK ≫ genι O.s.T.Z)
    (hio : spMap io ≫ yK = y.y) (e : Fin (D.R.f * O.N) ≃ Letter O.S.Dw)
    (b : Fin (D.R.f * O.N) → TanM (yK ≫ genι O.s.T.Z) O.s.T.Z.t.G),
    O.CoreWith x P ∧ yK ≫ genStr O.s.T.Z = spMap fK ∧
    (∀ i, (tv (bcTan io (by rw [← Category.assoc, hio]) (b i))).left = y.u (e i).1 (e i).2) ∧
    L = lieCoordLat O.s.T.Z.t hx b ∧
    ∀ (σ : K →+* ℂ) (z : CxPts (genStr O.s.T.Z) (σ.comp fK)) (hz : z.1 = spMap σ ≫ yK) (u v : Fin (D.R.f * O.N) → K),
      h.form σ u v = x.met (σ.comp fK) z (bcTan σ (by rw [hz, Category.assoc]) (∑ i, v i • b i))
        (bcTan σ (by rw [hz, Category.assoc]) (∑ i, u i • b i))

end GlobalTheory.HeightParts

end
