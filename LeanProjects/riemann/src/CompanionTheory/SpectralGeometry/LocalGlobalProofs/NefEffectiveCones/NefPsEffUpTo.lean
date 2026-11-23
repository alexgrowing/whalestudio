import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.CompanionTheory.NefKleiman

def NefPsEffUpTo (k : Type) [Field k] (d : ℕ) : Prop :=
  ∀ (V : Scheme.{0}) [IsIntegral V] [Algebra k Γ(V, ⊤)], IsProjOver (strHom k V) →
    topologicalKrullDim V ≤ (d : WithBot ℕ∞) → ∀ N : LB V, IsNef k N → IsPsEff N

theorem NefPsEffUpTo.mono {k : Type} [Field k] {d e : ℕ} (h : NefPsEffUpTo k d) (he : e ≤ d) :
    NefPsEffUpTo k e := fun V _ _ hp hV N hN =>
  h V hp (hV.trans (by exact_mod_cast he)) N hN

end GlobalTheory.CompanionTheory.NefKleiman
