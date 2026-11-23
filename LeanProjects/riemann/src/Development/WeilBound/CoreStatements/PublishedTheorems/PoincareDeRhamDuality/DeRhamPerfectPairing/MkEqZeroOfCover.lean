import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.ExistsSecCover

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.Points

namespace CrystallinePoints.Pd

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y : Scheme.{0}}

def pre {B : Type} [CommRing B] (y : Sp B ⟶ Sp R) : R →+* B := (Spec.preimage y).hom

theorem spMap_pre {B : Type} [CommRing B] (y : Sp B ⟶ Sp R) : spMap (pre y) = y := Spec.map_preimage y

theorem pre_spMap {B : Type} [CommRing B] (ρ : R →+* B) : pre (spMap ρ) = ρ :=
  congrArg CommRingCat.Hom.hom (Spec.preimage_map (CommRingCat.ofHom ρ))

theorem pre_comp {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Sp R) :
    pre (spMap ρ ≫ y) = ρ.comp (pre y) := by
  conv_lhs => rw [← spMap_pre y, ← GlobalTheory.Cris.spMap_comp, pre_spMap]

theorem valR_cst {B : Type} [CommRing B] (t : Y ⟶ Sp R) (y : Sp B ⟶ Y) (r : R) :
    valR y ⊤ (GlobalTheory.AbLaw.cst t ⊤ r) = pre (y ≫ t) r :=
  (valR_res y le_top (le_preimage_top y) _).trans
    ((valR_comp y t ⊤ _).symm.trans (preimage_apply (y ≫ t) r).symm)

@[reducible] def ptOf (s : X ⟶ Sp R) {B : Type} [CommRing B] (x : Sp B ⟶ X) : Pt s where
  B := B
  alg := (pre (x ≫ s)).toAlgebra
  x := x
  w := (spMap_pre _).symm

def homOf (s : X ⟶ Sp R) {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X) (x' : Sp B' ⟶ X)
    (h : spMap ρ ≫ x = x') : ptOf s x ⟶ ptOf s x' :=
  letI : Algebra R B := (pre (x ≫ s)).toAlgebra
  letI : Algebra R B' := (pre (x' ≫ s)).toAlgebra
  { ρ := { ρ with
      commutes' := fun r ↦ by
        change ρ (pre (x ≫ s) r) = pre (x' ≫ s) r
        rw [← h, Category.assoc, pre_comp]
        rfl }
    pt := h }

variable {s : X ⟶ Sp R}

def cv (z : Z1 (FP s)) {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X) : B' :=
  z.1 _ _ (homOf s ρ x _ rfl)

theorem cv_homOf (z : Z1 (FP s)) {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X)
    (x' : Sp B' ⟶ X) (h : spMap ρ ≫ x = x') : (z.1 _ _ (homOf s ρ x x' h) : B') = cv z ρ x := by
  subst h
  rfl

theorem cv_eq (z : Z1 (FP s)) {P Q : Pt s} (φ : P ⟶ Q) :
    (z.1 P Q φ : Q.B) = cv z (φ.ρ : P.B →+* Q.B) P.x := by
  rw [← cv_homOf z _ _ _ φ.pt]
  obtain @⟨B, rB, aB, x, w⟩ := P
  obtain @⟨B', rB', aB', x', w'⟩ := Q
  have e : aB = (pre (x ≫ s)).toAlgebra := Algebra.algebra_ext _ _ fun r ↦ by
    change _ = pre (x ≫ s) r
    rw [w, pre_spMap]
  have e' : aB' = (pre (x' ≫ s)).toAlgebra := Algebra.algebra_ext _ _ fun r ↦ by
    change _ = pre (x' ≫ s) r
    rw [w', pre_spMap]
  subst e
  subst e'
  exact congrArg (z.1 _ _) (hom_ext fun _ ↦ rfl)

section
variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']

theorem cv_comp (z : Z1 (FP s)) (ρ : B →+* B') (τ : B' →+* B'') (x : Sp B ⟶ X) :
    cv z (τ.comp ρ) x = τ (cv z ρ x) + cv z τ (spMap ρ ≫ x) :=
  (cv_eq z (homOf s ρ x _ rfl ≫ homOf s τ (spMap ρ ≫ x) _ rfl)).symm.trans
    (Z1.comp z (homOf s ρ x _ rfl) (homOf s τ (spMap ρ ≫ x) _ rfl))

theorem cv_add (z z' : Z1 (FP s)) (ρ : B →+* B') (x : Sp B ⟶ X) : cv (z + z') ρ x = cv z ρ x + cv z' ρ x := rfl

theorem cv_smul (z : Z1 (FP s)) (r : R) (ρ : B →+* B') (x : Sp B ⟶ X) :
    cv (r • z) ρ x = ρ (pre (x ≫ s) r) * cv z ρ x := by
  change pre ((spMap ρ ≫ x) ≫ s) r * cv z ρ x = _
  rw [Category.assoc, pre_comp]
  rfl

theorem cv_pull {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (z : Z1 (FP s))
    (ρ : B →+* B') (x : Sp B ⟶ X') : cv ((pushC h).pullbackOneCocycle z) ρ x = cv z ρ (x ≫ φ) :=
  cv_eq z (pushHom h (homOf s' ρ x _ rfl))

theorem cv_of_mk_eq {z z' : Z1 (FP s)} (h : H1.mk _ z = H1.mk _ z') :
    ∃ g : ∀ (B : Type) [CommRing B], (Sp B ⟶ X) → B, ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B')
      (x : Sp B ⟶ X), cv z ρ x = cv z' ρ x + (g B' (spMap ρ ≫ x) - ρ (g B x)) := by
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 h
  refine ⟨fun B _ x ↦ g (ptOf s x), fun B B' _ _ ρ x ↦ ?_⟩
  have e : (g (ptOf s (spMap ρ ≫ x)) : B') - ρ (g (ptOf s x)) = cv z ρ x - cv z' ρ x :=
    congrFun (congrFun (congrFun hg _) _) (homOf s ρ x _ rfl)
  linear_combination -e

end

open Classical in

def gam (z : Z1 (FP s)) (U : X.affineOpens) (B : Type) [CommRing B] (x : Sp B ⟶ X) : B :=
  if h : Inn x U.1 then
    cv z (B := GlobalTheory.CechDR.Sec s U.1) (valMap x U.1 h).hom (GlobalTheory.CechDR.affPt s U) else 0

theorem gam_map (z : Z1 (FP s)) (U : X.affineOpens) {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B')
    {x : Sp B ⟶ X} (h : Inn x U.1) : gam z U B' (spMap ρ ≫ x) = ρ (gam z U B x) + cv z ρ x := by
  have e : (valMap (spMap ρ ≫ x) U.1 (h.map ρ)).hom = ρ.comp (valMap x U.1 h).hom := RingHom.ext fun f ↦ by
    rw [← valR_eq, valR_spMap_comp _ _ _ h, valR_eq _ _ h]
    rfl
  have e' : spMap (R := GlobalTheory.CechDR.Sec s U.1) (valMap x U.1 h).hom ≫ GlobalTheory.CechDR.affPt s U = x :=
    specMap_valMap_fromSpec U.2 x h
  rw [gam, gam, dif_pos h, dif_pos (h.map ρ), e]
  exact (cv_comp z (B := GlobalTheory.CechDR.Sec s U.1) (valMap x U.1 h).hom ρ _).trans (by rw [e'])

theorem eq_of_cover {J : Type} (U : J → X.Opens) (hU : ⨆ j, U j = ⊤) {B : Type} [CommRing B] (x : Sp B ⟶ X)
    (b b' : B) (H : ∀ (j : J) (C : Type) [CommRing C] (τ : B →+* C), Inn (spMap τ ≫ x) (U j) → τ b = τ b') :
    b = b' := by
  have hc : ⨆ j, x ⁻¹ᵁ U j = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  have e := sec_ext_cover (fun j ↦ x ⁻¹ᵁ U j) hc ⊤ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b') fun j C _ y _ hy ↦ by
      rw [← preimage_apply, ← preimage_apply]
      refine H j C (pre y) ?_
      rw [spMap_pre]
      exact hy
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1 e

theorem mk_eq_zero_of_cover (z : Z1 (FP s)) {J : Type} (U : J → X.Opens) (hU : ⨆ j, U j = ⊤)
    (G : J → ∀ (B : Type) [CommRing B], (Sp B ⟶ X) → B)
    (h1 : ∀ (i j : J) (B : Type) [CommRing B] (x : Sp B ⟶ X), Inn x (U i) → Inn x (U j) → G i B x = G j B x)
    (h2 : ∀ (i : J) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X), Inn x (U i) →
      G i B' (spMap ρ ≫ x) = ρ (G i B x) + cv z ρ x) : H1.mk _ z = 0 := by
  classical
  let G₀ : ∀ (B : Type) [CommRing B], (Sp B ⟶ X) → B := fun B _ x ↦
    if h : ∃ j, Inn x (U j) then G h.choose B x else 0
  have hG : ∀ (j : J) (B : Type) [CommRing B] (x : Sp B ⟶ X), Inn x (U j) → G₀ B x = G j B x := by
    intro j B _ x hx
    have h : ∃ j, Inn x (U j) := ⟨j, hx⟩
    simp only [G₀, dif_pos h]
    exact h1 _ _ B x h.choose_spec hx
  have ex : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ X), ∃ g : B, ∀ (j : J) (C : Type) [CommRing C] (τ : B →+* C),
      Inn (spMap τ ≫ x) (U j) → τ g = G j C (spMap τ ≫ x) - cv z τ x := by
    intro B _ x
    have hc : ⨆ j, x ⁻¹ᵁ U j = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
    obtain ⟨f, hf⟩ := exists_sec_cover (fun j ↦ x ⁻¹ᵁ U j) ⊤ (fun _ ↦ le_top) hc.ge
      (fun C _ y ↦ G₀ C (y ≫ x) - cv z (pre y) x) fun j C C' _ _ τ y hy ↦ by
        have hy' : Inn (y ≫ x) (U j) := hy
        rw [Category.assoc, hG j _ _ hy', hG j _ _ (hy'.map τ), h2 j _ _ τ _ hy', pre_comp, cv_comp, spMap_pre,
          map_sub]
        ring
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom f, fun j C _ τ hτ ↦ ?_⟩
    have a := hf j C (spMap τ) hτ
    have b := valR_specMap (CommRingCat.ofHom τ) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom f)
    have c : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom f) = f := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
      rfl
    rw [c] at b
    rw [pre_spMap, hG j _ _ hτ] at a
    exact b.symm.trans a.symm
  choose g hg using ex
  refine H1.mk_eq_zero.2 ⟨fun P ↦ g P.B P.x, ?_⟩
  funext P Q φ
  rw [cv_eq z φ]
  change (g Q.B Q.x - φ.ρ (g P.B P.x) : Q.B) = _
  refine eq_of_cover U hU Q.x _ _ fun j C _ τ hτ ↦ ?_
  have e : spMap (τ.comp (φ.ρ : P.B →+* Q.B)) ≫ P.x = spMap τ ≫ Q.x := by
    rw [GlobalTheory.Cris.spMap_comp, Category.assoc, φ.pt]
  have a := hg Q.B Q.x j C τ hτ
  have b := hg P.B P.x j C (τ.comp (φ.ρ : P.B →+* Q.B)) (e ▸ hτ)
  rw [e, cv_comp, φ.pt] at b
  have b' : τ (φ.ρ (g P.B P.x)) = _ := b
  rw [map_sub, a, b']
  ring

end CrystallinePoints.Pd
