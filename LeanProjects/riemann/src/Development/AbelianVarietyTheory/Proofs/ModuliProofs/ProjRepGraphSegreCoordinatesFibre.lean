import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjectiveCoordinateRepresentationClosedSubsch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GraphSegre

theorem idealOf_eq_graphIdeal {K σ₁ σ₂ : Type} [CommRing K] {Y X₁ X₂ : Scheme.{0}} (s : Y ⟶ Sp K)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (N : LB Y) (ty : σ₁ × σ₂ → N.Sec) (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) (hN : N.IsLB)
    (H : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ →
      SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2)) :
    idealOf s N ty (𝟙 Y) = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  ext F
  simp only [idealOf, graphIdeal, Ideal.mem_iInf, RingHom.mem_ker, Category.comp_id]
  constructor
  · intro hF T _ β y v₁ v₂ h
    exact hF T _ β y _ ⟨h.1, H T y v₁ v₂ h.2.1 h.2.2⟩
  · intro hF T _ β y v h
    refine eq_zero_of_localization _ fun J hJ => ?_
    set φ := algebraMap T (Localization.AtPrime J) with hφ
    obtain ⟨v₁, hv₁⟩ := (GlobalTheory.ZM.LocalCoord.secCoord_local X₁ M₁ σ₁ th₁ h₁).1 (Localization.AtPrime J) ((spMap φ ≫ y) ≫ a₁)
    obtain ⟨v₂, hv₂⟩ := (GlobalTheory.ZM.LocalCoord.secCoord_local X₂ M₂ σ₂ th₂ h₂).1 (Localization.AtPrime J) ((spMap φ ≫ y) ≫ a₂)
    have hv := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N _ ty T y v hN h.2).1 _ φ
    obtain ⟨u, hu⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N _ ty _ _ _ hN (H _ _ v₁ v₂ hv₁ hv₂)).2.2 _ hv
    have hv₁' := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique X₁ M₁ _ th₁ _ _ _ h₁ hv₁).2.1 u
    have hs : (spMap φ ≫ y) ≫ s = spMap (φ.comp β) := by
      rw [Category.assoc, h.1]
      exact (Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom φ)).symm
    have key := hF _ _ (φ.comp β) (spMap φ ≫ y) _ v₂ ⟨hs, hv₁', hv₂⟩
    rw [MvPolynomial.map_eval₂Hom, ← key]
    congr 2
    funext i
    rw [hu i, _root_.mul_assoc]

theorem projRep_graph : ∀ (R K σ₁ σ₂ : Type) [CommRing R] [CommRing K] [Finite σ₁] [Finite σ₂] (x : R →+* K) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (Z₁ Z₂ : Over (Sp R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (Y : Scheme.{0}) (s : Y ⟶ Sp K) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsPullback a₁ s Z₁.hom (spMap x) → a₂ ≫ Z₂.hom = s ≫ spMap x → ∃ (N : LB Y) (ty : σ₁ × σ₂ → N.Sec), ProjRep (graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂) s N ty ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ → SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2) := by
  intro R K σ₁ σ₂ _ _ _ _ x I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ Y s a₁ a₂ r₁ r₂ hp ha₂
  obtain ⟨I₃, M₃, th₃, r₃, hseg⟩ := GlobalTheory.ZM.SegreCoord.segre_coordinates R σ₁ σ₂ I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ r₁ r₂
  have hprop : IsProper Z₂.hom := (GlobalTheory.ZM.projRep_projective_ample R σ₂ I₂ Z₂ M₂ th₂ r₂).2.1
  have hP : IsPullback (fst Z₁ Z₂).left (snd Z₁ Z₂).left Z₁.hom Z₂.hom := IsPullback.of_hasPullback Z₁.hom Z₂.hom
  have hW := IsPullback.of_hasPullback (Z₁ ⊗ Z₂).hom (spMap x)
  generalize pullback.fst (Z₁ ⊗ Z₂).hom (spMap x) = π at hW
  generalize pullback.snd (Z₁ ⊗ Z₂).hom (spMap x) = s' at hW
  generalize pullback (Z₁ ⊗ Z₂).hom (spMap x) = Wd at π s' hW
  obtain ⟨th', r', hbc⟩ := GlobalTheory.ZM.RepBC.projRep_baseChange R K _ x I₃ _ Wd _ s' π M₃ th₃ r₃ hW
  have hfw : (fst Z₁ Z₂).left ≫ Z₁.hom = (Z₁ ⊗ Z₂).hom := Over.w _
  let a : Y ⟶ (Z₁ ⊗ Z₂).left := hP.lift a₁ a₂ (hp.w.trans ha₂.symm)
  have e₁ : a ≫ (fst Z₁ Z₂).left = a₁ := hP.lift_fst _ _ _
  have e₂ : a ≫ (snd Z₁ Z₂).left = a₂ := hP.lift_snd _ _ _
  let i : Y ⟶ Wd := hW.lift a s (by rw [← hfw, ← Category.assoc, e₁, hp.w])
  have i₁ : i ≫ π = a := hW.lift_fst _ _ _
  have i₂ : i ≫ s' = s := hW.lift_snd _ _ _
  let q : Wd ⟶ Y := hp.lift (π ≫ (fst Z₁ Z₂).left) s' (by rw [Category.assoc, hfw, hW.w])
  have q₁ : q ≫ a₁ = π ≫ (fst Z₁ Z₂).left := hp.lift_fst _ _ _
  have q₂ : q ≫ s = s' := hp.lift_snd _ _ _
  have hq : IsPullback π q (fst Z₁ Z₂).left a₁ := by
    refine IsPullback.of_bot ?_ q₁.symm hp
    rw [q₂, hfw]; exact hW
  have hsf : IsSeparated (fst Z₁ Z₂).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  have hsq : IsSeparated q := MorphismProperty.of_isPullback (P := @IsSeparated) hq hsf
  have hiq : i ≫ q = 𝟙 Y := by
    refine hp.hom_ext ?_ ?_
    · rw [Category.assoc, q₁, ← Category.assoc, i₁, e₁, Category.id_comp]
    · rw [Category.assoc, q₂, i₂, Category.id_comp]
  have hci : IsClosedImmersion i := by
    have : IsClosedImmersion (i ≫ q) := by rw [hiq]; infer_instance
    exact IsClosedImmersion.of_comp i q
  have hN : ((M₃.pull π).pull i).IsLB := pull_isLB r'.1 i
  have hc : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v : σ₁ × σ₂ → T),
      SecCoord ((M₃.pull π).pull i) (fun j => GlobalTheory.ZM.RepBC.secPull _ i (th' j)) y v ↔
        SecCoord (M₃.pull π) th' (y ≫ i) v := fun T _ y v => GlobalTheory.ZM.RepBC.secCoord_pull _ th' i y v
  have rY := GlobalTheory.ZM.ClosedCoord.projRep_closed K _ _ Wd Y s' _ th' i _ _ r' hci hN hc
  have H : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ →
      SecCoord M₂ th₂ (y ≫ a₂) v₂ →
      SecCoord ((M₃.pull π).pull i) (fun j => GlobalTheory.ZM.RepBC.secPull _ i (th' j)) y (fun i => v₁ i.1 * v₂ i.2) := by
    intro T _ y v₁ v₂ h₁ h₂
    rw [hc, hbc, Category.assoc, i₁]
    refine hseg T _ v₁ v₂ ?_ ?_
    · rwa [Category.assoc, e₁]
    · rwa [Category.assoc, e₂]
  rw [i₂, idealOf_eq_graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ _ _ r₁.1 r₂.1 hN H] at rY
  exact ⟨_, _, rY, H⟩

end GlobalTheory.ZM.GraphSegre
