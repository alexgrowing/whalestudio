import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyFamHomog

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

theorem famHomog_of_homog : ∀ (N : ℕ → ℕ) (κ : Rule), Homog N κ → FamHomog N κ := by
  intro N κ hH S _ _ _ P hg rig hr th hth v hv th' hth' v' hv' a M u u' ha hM hu hu'
  obtain ⟨Q, hg₁, rig₁, hr₁, th₁, hth₁, v₁, hv₁, th₁', hth₁', v₁', hv₁', M₁, h₁, h₂, ha₁, hN, hd⟩ :=
    KeyGalDesc.exists_keyPB_pair (algebraMap S (FractionRing S)) P hg rig hr th hth v hv th' hth' v' hv' a M ha hM
  have e := hH _ Q hg₁ rig₁ hr₁ th₁ hth₁ v₁ hv₁ th₁' hth₁' v₁' hv₁' _ M₁ ha₁ hN
  have hgQ : Q.g = P.g := KeyGalDesc.g_eq h₁
  rw [hu _ _ _ h₁, hu' _ _ _ h₂, hd] at e
  have hn : N Q.g = N P.g := congrArg N hgQ
  rw [hn] at e
  apply IsFractionRing.injective S (FractionRing S)
  simpa only [map_mul, map_pow] using e

end GlobalTheory.KeyFamHomog
