import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

universe w w' v u v' u'

namespace GlobalTheory.CompanionTheory.CrisFil

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

def subMor (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) :
    CH.Mor S.fn S'.fn σ where
  G := m.G
  τ T := ((m.τ T).domRestrict (S.S (m.G.obj T))).codRestrict (S'.S T) fun x => h T x.1 x.2
  nat φ x := Subtype.ext (m.nat φ x.1)

theorem pull_inc (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) (n : ℕ) (y : CH.H S.fn n) :
    m.pull n (S.inc.pull n y) = S'.inc.pull n ((subMor m S S' h).pull n y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

theorem pull_img (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) (n : ℕ) (x : CH.H F n)
    (hx : x ∈ S.img n) : m.pull n x ∈ S'.img n := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(subMor m S S' h).pull n y, (pull_inc m S S' h n y).symm⟩

end General

section Thick

variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R}

theorem pdPow_obj (m : GlobalTheory.LogCris.Mor L L' σ) (T : Thick L') (r : ℕ) : (m.obj T).pdPow r = T.pdPow r := rfl

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}

theorem omMor_img (m : GlobalTheory.LogCris.Mor L L' σ) (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) (r j : ℕ)
    (x : CH.H (OM L c) j) (hx : x ∈ (pdS L c r).img j) : (omMor m σ₀ h).pull j x ∈ (pdS L' c' r).img j :=
  pull_img (omMor m σ₀ h) (pdS L c r) (pdS L' c' r) (fun _ _ hz => hz) j x hx

end Thick

theorem red_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m)
    (r j : ℕ), ∀ x ∈ HcFil F κ k m r j, redHc F κ k h j x ∈ HcFil F κ k n r j := by
  intro l _ O _ F κ k m n h r j x hx
  exact omMor_img _ _ _ r j x hx

end GlobalTheory.CompanionTheory.CrisFil
