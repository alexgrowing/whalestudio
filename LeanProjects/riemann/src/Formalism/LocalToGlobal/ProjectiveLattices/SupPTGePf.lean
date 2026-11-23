import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

def SupPtAt (σ : Tc.Q.c.F →+* ℂ) : Type :=
  Σ k : (Tc.U j σ).Comp, {x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((Tc.U j σ).X k).Ψ D.R.r // x ∈ ((Tc.U j σ).X k).dom}

variable {j} in

def NrmTieK (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j)
    (pt : ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ), SupPtAt j (goodOf Tc.Q.c (sgOf P))) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ) (F : Tc.R j),
    nrmC fn (yP Z) (wtZ (wtA ka) ka.n) (valC h (wtA ka) ka.n F Z) P =
      recNrm (Tc.U j (goodOf Tc.Q.c (sgOf P))) (xiR D) (wtA ka) ka.n F (pt Z P).1 (pt Z P).2.1

def DensK (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c) (ka : WeightFamilies.Wt D j)
    (pt : ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ), SupPtAt j (goodOf Tc.Q.c (sgOf P))) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (F : (recB hL).Cusp j ka), F ∈ (recB hL).Mlat j ka →
    evC h Z (F : Tc.R j) ≠ 0 →
    ∃ F' ∈ (recB hL).Mlat j ka, F' ≠ 0 ∧ ∀ sg : Tc.Q.c.F →+* ℂ,
      (recB hL).supN j ka sg F' ≤
        ⨆ P : PT (Ω := Om Z) sg, recNrm (Tc.U j (goodOf Tc.Q.c (sgOf (P : Om Z →+* ℂ)))) (xiR D) (wtA ka) ka.n
          (F : Tc.R j) (pt Z P).1 (pt Z P).2.1

theorem supPTGe_of (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j)
    (pt : ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ), SupPtAt j (goodOf Tc.Q.c (sgOf P)))
    (htie : NrmTieK h fn yP ka pt) (hden : DensK hL j h ka pt) :
    SupPTGe hL j h fn yP ka := by
  intro Z F hF hev
  obtain ⟨F', hF', hne, hsup⟩ := hden Z F hF hev
  refine ⟨F', hF', hne, fun sg => (hsup sg).trans (le_of_eq ?_)⟩
  exact iSup_congr fun P => (htie Z P (F : Tc.R j)).symm

end Formalism.L2.Pj
