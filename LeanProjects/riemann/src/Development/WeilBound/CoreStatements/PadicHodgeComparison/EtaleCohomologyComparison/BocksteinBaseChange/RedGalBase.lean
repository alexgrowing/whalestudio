import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SchFnPtTw
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison

namespace SH

open B PAlg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

section
variable {k₁ k₂ k₃ k₄ : Type} [CommRing k₁] [CommRing k₂] [CommRing k₃] [CommRing k₄] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂} {κ₃ : O →+* k₃}
  {κ₄ : O →+* k₄}

theorem base_base {τa : k₁ →+* k₂} {τb : k₂ →+* k₄} {τc : k₁ →+* k₃} {τd : k₃ →+* k₄} (ha : τa.comp κ₁ = κ₂) (hb : τb.comp κ₂ = κ₄)
    (hc : τc.comp κ₁ = κ₃) (hd : τd.comp κ₃ = κ₄) (B₀ : CommRingCat.{0}) (y : (F.ptK κ₄).obj B₀) :
    ((basePt F τa ha).app B₀ ((basePt F τb hb).app B₀ y)).1.2 = ((basePt F τc hc).app B₀ ((basePt F τd hd).app B₀ y)).1.2 := rfl

theorem base_map {F F' : Fn O} (u : Fn.Map F F') {τ : k₁ →+* k₂} (h : τ.comp κ₁ = κ₂) (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀) :
    ((u.ptK κ₁).app B₀ ((basePt F τ h).app B₀ y)).1.2 = ((basePt F' τ h).app B₀ ((u.ptK κ₂).app B₀ y)).1.2 := rfl

theorem base_snd {τ : k₁ →+* k₂} (h : τ.comp κ₁ = κ₂) (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀) :
    ((basePt F τ h).app B₀ y).1.2 = y.1.2 := rfl

theorem idc {Λ S : Type} [CommRing Λ] [CommRing S] (c : Λ →+* S) (a : Λ) : RingHom.id S (c a) = c (RingHom.id Λ a) := rfl

end

theorem phi_snd (n : ℕ) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) (h : (l : B₀) = 0) :
    ((phiPt F κ n).app B₀ y).1.2 = F.Pt.map (CommRingCat.ofHom (frb h)) y.1.2 := rfl

theorem phi_base (n : ℕ) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) :
    ((phiPt F κ (n + 1)).app B₀ ((basePt F _ (red_κb κ true n.le_succ)).app B₀ y)).1.2 =
      ((basePt F _ (red_κb κ true n.le_succ)).app B₀ ((phiPt F κ n).app B₀ y)).1.2 := by
  rw [phi_snd F κ (n + 1) B₀ _ (l_zero y.1.1), base_snd, base_snd, phi_snd F κ n B₀ _ (l_zero y.1.1)]

theorem red_galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) (r : (base l).Acr (n + 1)) :
    (base l).red n.le_succ (galBase σ (n + 1) r) = galBase σ n ((base l).red n.le_succ r) :=
  ((pdOk_twId σ _).red_acr n.le_succ _).trans (congrArg (twAcr σ _ n) ((pdOk_hom (baseTw σ)).red_acr n.le_succ r))

def redM (k : Bool) (n : ℕ) : Mor (Lc F κ k (n + 1)) (Lc F κ k n) ((base l).red n.le_succ) :=
  B.crMor (F := F) (F' := F) (b := bs l k (n + 1)) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red n.le_succ) rfl
    (dd_red k _ n.le_succ) (basePt F _ (red_κb κ k n.le_succ)) fun _ _ _ => rfl

def galM (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n : ℕ) : Mor (Lc F κ k n) (Lc F κ k n) (galBase σ n) :=
  B.crMor (F := F) (F' := F) (b := bs l k n) (b' := bs l k n) (ht := rfl) (ht' := rfl) (galBase σ n) rfl (dd_gal k σ n)
    (basePt F _ (gal_κb κ σ hσ k n)) fun _ _ _ => rfl

def phiM (n : ℕ) : Mor (Lc F κ true n) (Lc F κ true n) ((base l).phi n) :=
  B.crMor (F := F) (F' := F) (b := bs l true n) (b' := bs l true n) (ht := rfl) (ht' := rfl) ((base l).phi n) rfl
    ((base l).dpP_phi n) (phiPt F κ n) fun _ y r => ((congrArg y.1.1 (phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm

theorem red_gal (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k (n + 1) j) :
    redHc F κ k n.le_succ j (galHc F κ σ hσ k (n + 1) j x) = galHc F κ σ hσ k n j (redHc F κ k n.le_succ j x) := by
  unfold redHc galHc redMor galMorC
  exact cr_square (galM F κ σ hσ k (n + 1)) (redM F κ k n) (redM F κ k n) (galM F κ σ hσ k n) (galBase_cris σ (n + 1))
    (red_cris _ n.le_succ) (red_cris _ n.le_succ) (galBase_cris σ n) (red_galBase σ n)
    (base_base F (gal_κb κ σ hσ k (n + 1)) (red_κb κ k n.le_succ) (red_κb κ k n.le_succ) (gal_κb κ σ hσ k n)) j x

theorem red_phi (n j : ℕ) (x : Hc F κ true (n + 1) j) :
    redHc F κ true n.le_succ j (phiHc F κ (n + 1) j x) = phiHc F κ n j (redHc F κ true n.le_succ j x) := by
  unfold redHc phiHc redMor phiMorC
  exact cr_square (phiM F κ (n + 1)) (redM F κ true n) (redM F κ true n) (phiM F κ n) ((base l).phi_cris (n + 1))
    (red_cris _ n.le_succ) (red_cris _ n.le_succ) ((base l).phi_cris n) ((pdOk_frob _).red_acr n.le_succ) (phi_base F κ n) j x

variable {F} {F' : Fn O}

def pullM (u : Fn.Map F F') (k : Bool) (n : ℕ) : Mor (Lc F' κ k n) (Lc F κ k n) (RingHom.id _) :=
  B.crMor (F := F') (F' := F) (b := bs l k n) (b' := bs l k n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    (DPMorphism.id _).isDPMorphism (u.ptK _) fun _ _ _ => rfl

theorem red_pull (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k (n + 1) j) :
    redHc F κ k n.le_succ j (pullHc κ u k (n + 1) j x) = pullHc κ u k n j (redHc F' κ k n.le_succ j x) := by
  unfold redHc pullHc redMor pullMorC
  exact cr_square (pullM κ u k (n + 1)) (redM F κ k n) (redM F' κ k n) (pullM κ u k n) (idc _)
    (red_cris _ n.le_succ) (red_cris _ n.le_succ) (idc _) (fun r => (idc ((base l).red n.le_succ) r).symm)
    (base_map u (red_κb κ k n.le_succ)) j x

end SH

end CrystallineSemistableComparison
