import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianGenericIsoExtendsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.DvrExtension

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem spMap_genMap_comp (p : Cpt ξ) : spMap (genMap ξ p) ≫ X.fromSpecStalk p.1 = ξ := by
  have h : spMap (genMap ξ p) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes p.2) := by
    rw [← Spec.map_comp]
    rfl
  have h₁ : Spec.map (X.presheaf.stalkSpecializes p.2) ≫ X.fromSpecStalk p.1 = X.fromSpecStalk (genPt ξ) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk p.2
  rw [h, Category.assoc]
  exact (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) h₁).trans
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

theorem isFractionRing_genMap (h : IsCptGen ξ) (p : Cpt ξ) :
    letI := (genMap ξ p).toAlgebra
    IsFractionRing (X.presheaf.stalk p.1) Ω := by
  letI := (genMap ξ p).toAlgebra
  haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (h.inj p)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩, e⟩ := RegAtRing.exists_div h p z
  exact ⟨a, b, e⟩

theorem spec_dualMap_alg {R R' : Type} [CommRing R] [CommRing R'] (k : R →+* R') :
    Spec.map (CommRingCat.ofHom (dualMap k)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫ Spec.map (CommRingCat.ofHom k) := by
  have e : (dualMap k).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp k := by
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]

section Move

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {k : R →+* Ω} {G G' : Over X} [GrpObj G] [GrpObj G']
  {GΩ : Over (Sp Ω)} [GrpObj GΩ] {φ : GΩ.left ⟶ G.left} {φ' : GΩ.left ⟶ G'.left}
  {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} {ψ' : G₀.left ⟶ G'.left} {κ : GΩ.left ⟶ G₀.left}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem tangent_transport_dvr (hψ : IsGrpPullback G₀ G x ψ) (hψ' : IsGrpPullback G₀ G' x ψ')
    (hκ : κ ≫ G₀.hom = GΩ.hom ≫ spMap k) (e₁ : κ ≫ ψ = φ) (e₂ : κ ≫ ψ' = φ')
    (M : LieModel G ξ E) (M' : LieModel G' ξ E) (e : E)
    (tie : ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left)
    (y : Sp R ⟶ X) (hy : 𝟙 _ ≫ x = y) (v : epsAt y ⟶ G) (hv : IsTanAt G y v)
    (hve : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left) :
    ∃ v' : epsAt y ⟶ G', IsTanAt G' y v' ∧
      (M'.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v'.left := by
  subst hy
  obtain ⟨w, hw, hw'⟩ := tie
  let v₀ : epsAt (𝟙 (Sp R)) ⟶ G₀ := LieMove.liftEps hψ v
  have hv₀ : v₀.left ≫ ψ = v.left := LieMove.liftEps_left hψ v
  have t₀ : IsTanAt G₀ (𝟙 _) v₀ := (LieMove.tan_iff hψ v₀).2 (by
    rw [show LieMove.pushEps hψ v₀ = v from LieMove.push_lift hψ v]; exact hv)
  have key : Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v₀.left = w.left ≫ κ := by
    refine hψ.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hv₀, e₁, hw, hve]
    · have a := Over.w v₀
      have b := Over.w w
      dsimp at a b
      rw [Category.assoc, Category.assoc, a, hκ, ← Category.assoc (Over.Hom.left w), b]
      simp only [Category.comp_id]
      exact spec_dualMap_alg k
  refine ⟨LieMove.pushEps hψ' v₀, (LieMove.tan_iff hψ' v₀).1 t₀, ?_⟩
  rw [LieMove.pushEps_left, ← Category.assoc, key, Category.assoc, e₂, hw']

theorem tan_move_of_dvr [IsDomain R] [IsDiscreteValuationRing R]
    (hk : letI := k.toAlgebra; IsFractionRing R Ω) (hx : spMap k ≫ x = ξ) (hG : IsSemiAbelian G)
    (hG' : IsSemiAbelian G') (hφ : IsGrpPullback GΩ G ξ φ) (hφ' : IsGrpPullback GΩ G' ξ φ')
    (M : LieModel G ξ E) (M' : LieModel G' ξ E) (e : E)
    (tie : ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left)
    (v : epsAt x ⟶ G) (hv : IsTanAt G x v)
    (hve : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left) :
    ∃ v' : epsAt x ⟶ G', IsTanAt G' x v' ∧
      (M'.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v'.left := by
  subst hx
  letI := k.toAlgebra
  haveI : IsFractionRing R Ω := hk
  obtain ⟨G₀, _, ψ, ψ', κ, hψ, hψ', hκ, e₁, e₂⟩ := GlobalTheory.T.semiabelian_generic_iso_extends R Ω X X x x G G' GΩ φ φ' hG hG' hφ hφ'
  exact tangent_transport_dvr hψ hψ' hκ.1.w e₁ e₂ M M' e tie x (Category.id_comp x) v hv hve

theorem extends_move (hξ : IsCptGen ξ) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hφ : IsGrpPullback GΩ G ξ φ) (hφ' : IsGrpPullback GΩ G' ξ φ')
    (M : LieModel G ξ E) (M' : LieModel G' ξ E)
    (tie : ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left)
    (p : Cpt ξ) [IsDomain (X.presheaf.stalk p.1)] [IsDiscreteValuationRing (X.presheaf.stalk p.1)]
    (e : E) (h : ∃ v, M.Extends p e v) : ∃ v, M'.Extends p e v := by
  obtain ⟨v, hv, hve⟩ := h
  exact tan_move_of_dvr (isFractionRing_genMap hξ p) (spMap_genMap_comp p) hG hG' hφ hφ' M M' e (tie e) v hv hve

end Move

theorem lat_eq_of_dvr : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (M' : LieModel G' ξ E), (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left) → ∀ p : Cpt ξ, (∃ _ : IsDomain (X.presheaf.stalk p.1), IsDiscreteValuationRing (X.presheaf.stalk p.1)) → M.lat p = M'.lat p := by
  intro X Ω _ ξ hξ G G' _ _ GΩ _ φ φ' hG hG' hφ hφ' E _ _ M M' tie p hp
  obtain ⟨_, _⟩ := hp
  have e : {e | ∃ v, M.Extends p e v} = {e | ∃ v, M'.Extends p e v} := Set.ext fun e =>
    ⟨extends_move hξ hG hG' hφ hφ' M M' tie p e,
      extends_move hξ hG' hG hφ' hφ M' M (fun e => by
        obtain ⟨v, a, b⟩ := tie e
        exact ⟨v, b, a⟩) p e⟩
  simp only [LieModel.lat]
  rw [e]

end GlobalTheory.CompanionTheory.Ar.DvrExtension
