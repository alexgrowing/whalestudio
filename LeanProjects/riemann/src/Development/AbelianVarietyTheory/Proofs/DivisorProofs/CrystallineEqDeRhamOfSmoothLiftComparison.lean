import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CrysLift

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def diagSec (X : Scheme.{0}) : AffOp X ⥤ (Pair (𝟙 X))ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ (⟨(U, U), by simp⟩ : Pair (𝟙 X))) fun _ _ h ↦
      Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h, h⟩)).op

def diagCoef (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (OPair (𝟙 X) s) (OAff s) where
  G := diagSec X
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem diag_res_degree_one (s : X ⟶ Sp R) (c : HH1 s) :
    pullHyp1 (diagCoef s) (pullHyp1 (pairRes (𝟙 X) s) c) = c := by
  rw [← pullHyp1_comp]
  exact (pullHyp1_eq_of_natTrans _ (CoefMap.id _) { app U := 𝟙 U }
    (fun U b ↦ mp_id (OAff s) U b) c).trans (pullHyp1_id c)

theorem diag_res_degree_two (s : X ⟶ Sp R) (c : HH2 s) :
    pullHyp2 (diagCoef s) (pullHyp2 (pairRes (𝟙 X) s) c) = c := by
  rw [← pullHyp2_comp]
  exact (pullHyp2_eq_of_natTrans _ (CoefMap.id _) { app U := 𝟙 U }
    (fun U b ↦ mp_id (OAff s) U b) c).trans (pullHyp2_id c)

theorem eq_of_isPull1 {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) {c c' : HH1 s}
    (e : IsPull1 h c c') : c = c' := by
  have e' : pullHyp1 (pairRes (𝟙 X) s) c = pullHyp1 (pairRes (𝟙 X) s) c' :=
    (isPull1_id h c).symm.trans e
  rw [← diag_res_degree_one s c, e', diag_res_degree_one]

theorem eq_of_isPull2 {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) {c c' : HH2 s}
    (e : IsPull2 h c c') : c = c' := by
  have e' : pullHyp2 (pairRes (𝟙 X) s) c = pullHyp2 (pairRes (𝟙 X) s) c' :=
    (isPull2_id h c).symm.trans e
  rw [← diag_res_degree_two s c, e', diag_res_degree_two]

theorem red_of {R₀ : Type} [CommRing R₀] {I : Ideal R} {π : R →+* R₀} (hπ : Function.Surjective π)
    (hI : RingHom.ker π = I) {X₀ : Scheme.{0}} {s : X ⟶ Sp R} {s₀ : X₀ ⟶ Sp R₀} {i : X₀ ⟶ X}
    (hp : IsPullback i s₀ s (spMap π)) :
    ∃ s₀' : X₀ ⟶ Sp (R ⧸ I), IsPullback i s₀' s (spMap (Ideal.Quotient.mk I)) ∧
      s₀ ≫ spMap π = s₀' ≫ spMap (Ideal.Quotient.mk I) := by
  subst hI
  let e := RingHom.quotientKerEquivOfSurjective hπ
  have he : (e : R ⧸ RingHom.ker π →+* R₀).comp (Ideal.Quotient.mk _) = π := RingHom.ext fun _ ↦ rfl
  have hs : spMap π = spMap (e : R ⧸ RingHom.ker π →+* R₀) ≫ spMap (Ideal.Quotient.mk _) := by
    conv_lhs => rw [← he]
    show Spec.map _ = Spec.map _ ≫ Spec.map _; rw [← Spec.map_comp]; rfl
  have : IsIso (CommRingCat.ofHom (e : R ⧸ RingHom.ker π →+* R₀)) := e.toCommRingCatIso.isIso_hom
  refine ⟨s₀ ≫ spMap (e : R ⧸ RingHom.ker π →+* R₀), ?_, by rw [hs, Category.assoc]⟩
  exact hp.of_iso (Iso.refl _) (Iso.refl _) (asIso (spMap (e : R ⧸ RingHom.ker π →+* R₀))) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp [hs])

end GlobalTheory.CrysLift

namespace GlobalTheory.CrysLift

open GlobalTheory.SmoothLift

theorem crystallineDeRham_of_smoothLift : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.CrystallineDeRham := by
  rintro ⟨e₁, e₂, -, -, hnat⟩ R _ I κ hκ R₀ _ π hπ hI X X₀ s s₀ i hs hsep hqc hp m
  have hid : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have : IsIso (spMap (RingHom.id R)) := by rw [hid]; infer_instance
  let D : Data :=
    { R := R, I := ⊥, κ := dp0 R, nil := isDPNilpotent_bot R, X := X, X₀ := X, s := s, t := s, i := 𝟙 X,
      smooth := hs, sep := hsep, qc := hqc,
      red := by
        obtain ⟨s', h1, h2⟩ := red_of (π := RingHom.id R) Function.surjective_id
          ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id)
          (IsPullback.of_horiz_isIso (fst := 𝟙 X) (g := spMap (RingHom.id R)) (snd := s) (f := s)
            ⟨by rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]⟩)
        refine ⟨s', h1, ?_⟩
        rw [← h2, show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.comp_id] }
  let D' : Data :=
    { R := R, I := I, κ := κ, nil := hκ, X := X, X₀ := X₀, s := s, t := s₀ ≫ spMap π, i := i,
      smooth := hs, sep := hsep, qc := hqc,
      red := by
        obtain ⟨s', h1, h2⟩ := red_of hπ hI hp
        exact ⟨s', h1, h2⟩ }
  have h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R) := by
    rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]
  obtain ⟨h1, h2⟩ := hnat D D' (RingHom.id R) (𝟙 X) i h m (by simp [D, D'])
  have k1 : ∀ c, m.pull1 c = ((e₁ D).trans (e₁ D').symm) c := fun c ↦
    ((e₁ D').symm_apply_apply _).symm.trans (congrArg (e₁ D').symm (eq_of_isPull1 h (h1 c)).symm)
  have k2 : ∀ c, m.pull2 c = ((e₂ D).trans (e₂ D').symm) c := fun c ↦
    ((e₂ D').symm_apply_apply _).symm.trans (congrArg (e₂ D').symm (eq_of_isPull2 h (h2 c)).symm)
  exact ⟨(funext k1 : (⇑m.pull1 : _ → _) = _) ▸ ((e₁ D).trans (e₁ D').symm).bijective,
    (funext k2 : (⇑m.pull2 : _ → _) = _) ▸ ((e₂ D).trans (e₂ D').symm).bijective⟩

end GlobalTheory.CrysLift
