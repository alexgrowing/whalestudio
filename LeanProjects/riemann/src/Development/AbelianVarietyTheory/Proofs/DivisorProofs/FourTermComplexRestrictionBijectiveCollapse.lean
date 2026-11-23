import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyZeroOneInstancesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstancesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH0BijectiveH1InjectiveUniversesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH1SurjectiveUniversesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH2InjectiveAllUniversesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH2SurjectiveUniversesStatement
open CategoryTheory GlobalTheory.CxCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CxCoh.Collapse

theorem bij_of_two {A B X Y : Type*} (r : A → B) (w : B → X) (s : X → Y) (U : A → X) (E : B → Y)
    (hU : ∀ x, U x = w (r x)) (hE : ∀ y, E y = s (w y))
    (bU : Function.Bijective U) (bE : Function.Bijective E) : Function.Bijective r := by
  have wi : Function.Injective w := fun y y' h ↦ bE.1 (by rw [hE, hE, h])
  refine ⟨fun x x' h ↦ bU.1 (by rw [hU, hU, h]), fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := bU.2 (w y)
  exact ⟨x, wi (by rw [← hU, hx])⟩

variable {C : Type 1} [Category.{0} C] {D : Type} [Category.{0} D]

def uMap (K : Cx C) (S : C ⥤ C) (u : 𝟭 C ⟶ S) : CxMap K (K.res S) where
  G := 𝟭 C
  a0 T := K.M0.map (u.app T)
  a1 T := K.M1.map (u.app T)
  a2 T := K.M2.map (u.app T)
  a3 T := K.M3.map (u.app T)
  compDegreeZero_natural φ x := by
    have h := u.naturality φ
    simp only [Functor.id_map] at h ⊢
    rw [← K.M0.map_comp, ← K.M0.map_comp, h]
  compDegreeOne_natural φ x := by
    have h := u.naturality φ
    simp only [Functor.id_map] at h ⊢
    rw [← K.M1.map_comp, ← K.M1.map_comp, h]
  compDegreeTwo_natural φ x := by
    have h := u.naturality φ
    simp only [Functor.id_map] at h ⊢
    rw [← K.M2.map_comp, ← K.M2.map_comp, h]
  comp_commutes_diffZero T x := (K.diffZero_natural _ x).symm
  comp_commutes_diffOne T x := (K.diffOne_natural _ x).symm
  comp_commutes_diffTwo T x := (K.diffTwo_natural _ x).symm

def wMap (K : Cx C) (ℓ : D ⥤ C) (q : C ⥤ D) (S : C ⥤ C) (w : q ⋙ ℓ ⟶ S) : CxMap (K.res ℓ) (K.res S) where
  G := q
  a0 T := K.M0.map (w.app T)
  a1 T := K.M1.map (w.app T)
  a2 T := K.M2.map (w.app T)
  a3 T := K.M3.map (w.app T)
  compDegreeZero_natural {T T'} φ x := by
    have := w.naturality φ
    simp only [Functor.comp_map] at this
    change K.M0.map (w.app T') (K.M0.map (ℓ.map (q.map φ)) x) = K.M0.map (S.map φ) (K.M0.map (w.app T) x)
    rw [← K.M0.map_comp, ← K.M0.map_comp, this]
  compDegreeOne_natural {T T'} φ x := by
    have := w.naturality φ
    simp only [Functor.comp_map] at this
    change K.M1.map (w.app T') (K.M1.map (ℓ.map (q.map φ)) x) = K.M1.map (S.map φ) (K.M1.map (w.app T) x)
    rw [← K.M1.map_comp, ← K.M1.map_comp, this]
  compDegreeTwo_natural {T T'} φ x := by
    have := w.naturality φ
    simp only [Functor.comp_map] at this
    change K.M2.map (w.app T') (K.M2.map (ℓ.map (q.map φ)) x) = K.M2.map (S.map φ) (K.M2.map (w.app T) x)
    rw [← K.M2.map_comp, ← K.M2.map_comp, this]
  comp_commutes_diffZero T x := (K.diffZero_natural _ x).symm
  comp_commutes_diffOne T x := (K.diffOne_natural _ x).symm
  comp_commutes_diffTwo T x := (K.diffTwo_natural _ x).symm

def eMap (K : Cx C) (ℓ : D ⥤ C) (q : C ⥤ D) (S : C ⥤ C) (w : q ⋙ ℓ ⟶ S) (ε : 𝟭 D ⟶ ℓ ⋙ q) :
    CxMap (K.res ℓ) ((K.res S).res ℓ) where
  G := 𝟭 D
  a0 T := K.M0.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  a1 T := K.M1.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  a2 T := K.M2.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  a3 T := K.M3.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  compDegreeZero_natural {T T'} φ x := by
    have h1 := ε.naturality φ
    have h2 := w.naturality (ℓ.map φ)
    simp only [Functor.comp_map, Functor.id_map] at h1 h2
    change K.M0.map _ (K.M0.map (ℓ.map φ) x) = K.M0.map (S.map (ℓ.map φ)) (K.M0.map _ x)
    rw [← K.M0.map_comp, ← K.M0.map_comp]
    congr 1
    rw [← Category.assoc, ← ℓ.map_comp, h1, ℓ.map_comp, Category.assoc, h2, Category.assoc]
  compDegreeOne_natural {T T'} φ x := by
    have h1 := ε.naturality φ
    have h2 := w.naturality (ℓ.map φ)
    simp only [Functor.comp_map, Functor.id_map] at h1 h2
    change K.M1.map _ (K.M1.map (ℓ.map φ) x) = K.M1.map (S.map (ℓ.map φ)) (K.M1.map _ x)
    rw [← K.M1.map_comp, ← K.M1.map_comp]
    congr 1
    rw [← Category.assoc, ← ℓ.map_comp, h1, ℓ.map_comp, Category.assoc, h2, Category.assoc]
  compDegreeTwo_natural {T T'} φ x := by
    have h1 := ε.naturality φ
    have h2 := w.naturality (ℓ.map φ)
    simp only [Functor.comp_map, Functor.id_map] at h1 h2
    change K.M2.map _ (K.M2.map (ℓ.map φ) x) = K.M2.map (S.map (ℓ.map φ)) (K.M2.map _ x)
    rw [← K.M2.map_comp, ← K.M2.map_comp]
    congr 1
    rw [← Category.assoc, ← ℓ.map_comp, h1, ℓ.map_comp, Category.assoc, h2, Category.assoc]
  comp_commutes_diffZero T x := (K.diffZero_natural _ x).symm
  comp_commutes_diffOne T x := (K.diffOne_natural _ x).symm
  comp_commutes_diffTwo T x := (K.diffTwo_natural _ x).symm

end GlobalTheory.CxCoh.Collapse

open GlobalTheory.CxCoh.Collapse in

theorem GlobalTheory.CxCoh.collapse_resMap_bij : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C) (ℓ : D ⥤ C)
    (q : C ⥤ D) (S : C ⥤ C) (u : 𝟭 C ⟶ S) (w : q ⋙ ℓ ⟶ S) (ε : 𝟭 D ⟶ ℓ ⋙ q), (∀ T, K.QAt (u.app T)) →
    (∀ U, K.QAt (ℓ.map (ε.app U) ≫ w.app (ℓ.obj U))) → (K.resMap ℓ).Bij := by
  intro C _ D _ K ℓ q S u w ε hu hε
  let U := uMap K S u
  let W := wMap K ℓ q S w
  let E := eMap K ℓ q S w ε
  have jU : U.Joined (K.resMap S) u := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have jW : ((K.resMap ℓ).comp W).Joined (K.resMap S) w := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have jE : E.Joined (W.comp ((K.res S).resMap ℓ)) ε :=
    ⟨fun _ x ↦ (K.M0.map_comp _ _ x).symm, fun _ x ↦ (K.M1.map_comp _ _ x).symm,
      fun _ x ↦ (K.M2.map_comp _ _ x).symm⟩
  have qU : U.QAll := hu
  have qE : E.QAll := hε
  have a0U := GlobalTheory.T.vertical_h0_bijective_h1_injective_universes.1 U qU
  have a1U := GlobalTheory.T.vertical_h1_surjective_universes.1 U qU
  have a2U := GlobalTheory.T.vertical_h2_injective_three_universe_pairs.1 U qU
  have a3U := GlobalTheory.T.vertical_h2_surjective_universes.1 U qU
  have a0E := GlobalTheory.T.vertical_h0_bijective_h1_injective_universes.2.2 E qE
  have a1E := GlobalTheory.T.vertical_h1_surjective_universes.2.2 E qE
  have a2E := GlobalTheory.T.vertical_h2_injective_three_universe_pairs.2.2 E qE
  have a3E := GlobalTheory.T.vertical_h2_surjective_universes.2.2 E qE
  have oU := GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances.1 _ _ _ jU
  have oW := GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances.1 _ _ _ jW
  have oE := GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances.2.2 _ _ _ jE
  have tU := GlobalTheory.T.joinedMapsAgreeCohomologyTwo_instances.1 _ _ _ jU
  have tW := GlobalTheory.T.joinedMapsAgreeCohomologyTwo_instances.1 _ _ _ jW
  have tE := GlobalTheory.T.joinedMapsAgreeCohomologyTwo_instances.2.2 _ _ _ jE
  refine ⟨bij_of_two _ W.h0 ((K.res S).resMap ℓ).h0 U.h0 E.h0 (fun x ↦ ?_) (fun y ↦ ?_) a0U.1 a0E.1,
    bij_of_two _ W.h1 ((K.res S).resMap ℓ).h1 U.h1 E.h1 (fun x ↦ ?_) (fun y ↦ ?_) ⟨a0U.2, a1U⟩ ⟨a0E.2, a1E⟩,
    bij_of_two _ W.h2 ((K.res S).resMap ℓ).h2 U.h2 E.h2 (fun x ↦ ?_) (fun y ↦ ?_) ⟨a2U, a3U⟩ ⟨a2E, a3E⟩⟩
  · rw [oU.1, ← oW.1, CxMap.cohomZero_pullback_comp]
  · rw [oE.1, CxMap.cohomZero_pullback_comp]
  · rw [oU.2, ← oW.2, CxMap.cohomOne_pullback_comp]
  · rw [oE.2, CxMap.cohomOne_pullback_comp]
  · rw [tU, ← tW, CxMap.cohomTwo_pullback_comp]
  · rw [tE, CxMap.cohomTwo_pullback_comp]
