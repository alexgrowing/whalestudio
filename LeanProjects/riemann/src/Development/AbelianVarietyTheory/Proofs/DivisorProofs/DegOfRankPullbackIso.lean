import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false
noncomputable section
open scoped GlobalTheory.ProjSpace
namespace GlobalTheory.CxLine

section Iso

variable {X Y : Scheme.{0}} (e : Y ≅ X)

def pullEquiv : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackId X).symm ≪≫ Scheme.Modules.pullbackCongr e.inv_hom_id.symm ≪≫
      (Scheme.Modules.pullbackComp e.inv e.hom).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId Y)

def pushPullIso (G : X.Modules) :
    G ≅ (Scheme.Modules.pushforward e.hom).obj ((Scheme.Modules.pullback e.hom).obj G) :=
  (pullEquiv e).unitIso.app G ≪≫
    ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).rightAdjointUniq
      (pullEquiv e).toAdjunction).symm.app ((Scheme.Modules.pullback e.hom).obj G)

variable {k : Type} [Field k] [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]

theorem degOfRank_pullback_iso
    (hf : ∀ r : k, e.hom.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r)
    (G : X.Modules) (r : ℕ) :
    degOfRank k ((Scheme.Modules.pullback e.hom).obj G) r = degOfRank k G r := by
  have h₁ : chi k G = chi k ((Scheme.Modules.pullback e.hom).obj G) :=
    (chi_congr k (pushPullIso e G)).trans (chi_pushforward_of_isClosedImmersion hf _)
  have h₂ : chi k (structureModule X) = chi k (structureModule Y) :=
    (chi_congr k (asIso (unitToPush e.hom))).trans (chi_pushforward_of_isClosedImmersion hf _)
  rw [degOfRank, degOfRank, h₁, h₂]

end Iso

end GlobalTheory.CxLine
