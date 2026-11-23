import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SchFnPtTw
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
import BuildAid.D3

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisTransition

section

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

theorem red_galBase_le (σ : Gal(PadicAlgCl l/K)) {m n : ℕ} (h : n ≤ m) (r : (base l).Acr m) :
    (base l).red h (galBase σ m r) = galBase σ n ((base l).red h r) :=
  ((pdOk_twId σ _).red_acr h _).trans (congrArg (twAcr σ _ n) ((pdOk_hom (baseTw σ)).red_acr h r))

def redMle (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem reduction_commutes_galois_action (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F κ k m j) :
    redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) := by
  unfold redHc galHc redMor galMorC
  exact cr_square (SH.galM F κ σ hσ k m) (redMle F κ k h) (redMle F κ k h) (SH.galM F κ σ hσ k n) (galBase_cris σ m)
    (red_cris _ h) (red_cris _ h) (galBase_cris σ n) (red_galBase_le σ h)
    (SH.base_base F (gal_κb κ σ hσ k m) (red_κb κ k h) (red_κb κ k h) (gal_κb κ σ hσ k n)) j x

end

theorem redHc_galHc : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j), redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) := by
  intro l _ O _ F κ K σ hσ k m n h j x
  exact reduction_commutes_galois_action F κ σ hσ k h j x

end GlobalTheory.CompanionTheory.CrisTransition
