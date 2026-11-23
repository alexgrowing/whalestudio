import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
import BuildAid.D3
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisCmp

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redMk (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

def cmpMk (n : ℕ) : Mor (Lc F κ false n) (Lc F κ true n) (RingHom.id _) :=
  B.crMor (F := F) (F' := F) (b := bs l false n) (b' := bs l true n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    ((base l).dp_fil_pfil n) (basePt F (Ideal.Quotient.factor le_sup_right) rfl) fun _ _ _ => rfl

theorem fac_κb (n : ℕ) :
    (Ideal.Quotient.factor (S := JJ false (base l) n) (T := JJ true (base l) n) le_sup_right).comp (κb κ false n) = κb κ true n := rfl

theorem cmp_pt {m n : ℕ} (h : n ≤ m) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) :
    ((cmpMk F κ m).pt.app B₀ ((redMk F κ true h).pt.app B₀ y)).1.2 =
      ((redMk F κ false h).pt.app B₀ ((cmpMk F κ n).pt.app B₀ y)).1.2 :=
  SH.base_base F (κ₁ := κb κ false m) (κ₂ := κb κ true m) (κ₃ := κb κ false n) (κ₄ := κb κ true n)
    (fac_κb κ m) (red_κb κ true h) (red_κb κ false h) (fac_κb κ n) B₀ y

theorem red_cmp {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j) :
    redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) := by
  unfold redHc redMor cmpMor
  exact cr_square (cmpMk F κ m) (redMk F κ true h) (redMk F κ false h) (cmpMk F κ n) (SH.idc _)
    (red_cris _ h) (red_cris _ h) (SH.idc _) (fun r => (SH.idc ((base l).red h) r).symm)
    (cmp_pt F κ h) j x

theorem main : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j), redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) :=
  fun F κ _ _ h j x => red_cmp F κ h j x

end GlobalTheory.CompanionTheory.CrisCmp
