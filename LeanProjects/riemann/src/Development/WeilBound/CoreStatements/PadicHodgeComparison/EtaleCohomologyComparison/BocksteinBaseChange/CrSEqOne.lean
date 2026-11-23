import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison

universe u v w

section
variable {O : Type} [CommRing O] {F : B.Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem cr_s_eq_one (T : Thick (F.cr b ht κ)) : T.s = 1 := by
  have h := (Finset.prod_of_isEmpty (ι := Empty) _).symm.trans T.hs
  rw [ht, map_one, mul_one] at h
  exact Units.ext h.symm

def crHom {T T' : Thick (F.cr b ht κ)} (φ : T.B →+* T'.B) (comm : ∀ r, φ (T.i r) = T'.i r) (dp : IsDPMorphism T.δ T'.δ φ)
    (pt : ∀ h, F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ h)) T.y.1.2 = T'.y.1.2) : T ⟶ T' where
  φ := φ
  u j := j.elim
  comm := comm
  dp := dp
  hle := Ideal.map_le_iff_le_comap.1 dp.1
  pt := Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun r => by
    have h1 : T.y.1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T.J (T.i r) := T.w r
    have h2 : T'.y.1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T'.J (T'.i r) := T'.w r
    change Ideal.quotientMap T'.J φ (Ideal.map_le_iff_le_comap.1 dp.1) (T.y.1.1 (Ideal.Quotient.mk _ r)) = T'.y.1.1 (Ideal.Quotient.mk _ r)
    rw [h1, h2, Ideal.quotientMap_mk, comm])) (pt _))
  hx j := j.elim
  hs := by
    rw [cr_s_eq_one T, cr_s_eq_one T']
    exact ((congrArg₂ (· * ·) (Finset.prod_of_isEmpty (ι := Empty) _) (map_one _)).trans (mul_one 1)).symm
  hv j := j.elim

theorem cr_pull_eq {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {σ : Λ →+* Λ'} {C' : Type u} [Category.{v} C']
    {F' : C' ⥤ ModuleCat.{w} Λ'} (m m' : CH.Mor (B.OM (F.cr b ht κ) c) F' σ) (η : ∀ T, m.G.obj T ⟶ m'.G.obj T)
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (m.G.obj T).B), (η T').φ ((m.G.map f).φ x) = (m'.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') (x : (m.G.obj T).B), m'.τ T ((η T).φ x) = m.τ T x) (n : ℕ) (x : CH.H (B.OM (F.cr b ht κ) c) n) :
    m.pull n x = m'.pull n x :=
  CrystallineSemistableComparison.P.prism m m' ⟨η, fun _ _ f => Thick.Hom.ext (RingHom.ext (nat f)) (funext fun j => j.elim)⟩ hτ n x

theorem pt_id {B₀ : Type} [CommRing B₀] (J : Ideal B₀) (h) (y : F.Pt.obj (CommRingCat.of (B₀ ⧸ J))) :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B₀) h)) y = y := by
  have e : Ideal.quotientMap J (RingHom.id B₀) h = RingHom.id _ := by ext; rfl
  rw [e, CommRingCat.ofHom_id, F.Pt.map_id]; rfl

end

theorem pull_pull {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {σ : R →+* R'} {σ' : R' →+* R''} (σ'' : R →+* R'')
    [RingHomCompTriple σ σ' σ''] {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C'] [Category.{0} C''] {F : C ⥤ ModuleCat.{0} R}
    {F' : C' ⥤ ModuleCat.{0} R'} {F'' : C'' ⥤ ModuleCat.{0} R''} (m : CH.Mor F F' σ) (m' : CH.Mor F' F'' σ') (n : ℕ) (x : CH.H F n) :
    m'.pull n (m.pull n x) = (m.comp (σ'' := σ'') m').pull n x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem cr_square {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τ : Λ →+* Λ}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τ a)) (hb : ∀ a, σb (c₂ a) = c₄ (RingHom.id Λ a)) (hc : ∀ a, σc (c₁ a) = c₃ (RingHom.id Λ a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τ a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb (RingHom.id Λ) hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τ ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τ hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc (RingHom.id Λ) hc).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

end CrystallineSemistableComparison
