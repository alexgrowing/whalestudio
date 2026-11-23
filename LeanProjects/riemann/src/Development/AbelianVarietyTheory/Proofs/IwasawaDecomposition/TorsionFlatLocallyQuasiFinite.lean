import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTensorInjectiveOfFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTorsionSemiAbelian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreFlatGen

open FibreFlat FiniteFibreFlat MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in

theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Y ⟶ S) (h1 : Flat (f ≫ g))
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) : Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S with ih
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    haveI := isLocallyNoetherian_of_isOpenImmersion (pullback.fst g u)
    haveI := isLocallyNoetherian_of_isOpenImmersion (pullback.fst f (pullback.fst g u))
    refine ih (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1)
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y with ih
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    haveI := isLocallyNoetherian_of_isOpenImmersion (Y.affineCover.f i)
    haveI := isLocallyNoetherian_of_isOpenImmersion (pullback.fst f (Y.affineCover.f i))
    exact ih (pullback.snd f (Y.affineCover.f i)) (Y.affineCover.f i ≫ g)
      (by rw [e]; infer_instance) (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X with ih
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    haveI := isLocallyNoetherian_of_isOpenImmersion (X.affineCover.f i)
    exact ih (X.affineCover.f i ≫ f) (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1
  rw [Flat.SpecMap_iff] at h1 ⊢
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : IsNoetherianRing A := (isLocallyNoetherian_Spec (R := A)).1 inferInstance
  haveI : IsNoetherianRing B := (isLocallyNoetherian_Spec (R := B)).1 inferInstance
  refine flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

theorem flat_and_locallyQuasiFinite_torsion : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 → Flat (torsion G q).hom ∧ LocallyQuasiFinite (torsion G q).hom := by
  intro S _ G _ hG q hq
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have hm := MulEtaleDvr.isMonHom_mulN G q
  have : LocallyOfFiniteType ((mulN G q).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (mulN G q).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((mulN G q).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (mulN G q).left := QuasiCompact.of_comp _ G.hom
  have hq' : LocallyQuasiFinite (mulN G q).left :=
    locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      have h₀ := finite_torsion_semiAbelian K ((Over.pullback t).obj G)
        (IsSemiAbelian.pullback t G hG) q (Nat.pos_of_ne_zero hq)
      have h₁ := FewZeros.finite_torsion_of_mulEquiv
        (TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp K))) t (Category.id_comp t)) q h₀
      simp only [MulUnramified.comp_mulN]
      exact h₁
  have hf : Flat (mulN G q).left := by
    have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
    refine flat_of_flatOver_fields _ G.hom (by rw [Over.w]; infer_instance) fun k _ t => ?_
    exact flatOver_of_pullback _ t (IntDiv.flat_fibre G (mulN G q) k t)
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) (MulEtaleDvr.isPullback_torsion G q) hf,
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (MulEtaleDvr.isPullback_torsion G q) hq'⟩

end GlobalTheory.FibreFlatGen
