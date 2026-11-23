import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisRestrictFinerOpensStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturalityStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

variable {R₀ : Type} [CommRing R₀] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}
  {C D : Type} [Category.{0} C] [Category.{0} D]

theorem opOf_le_of_natTrans (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (θ : H ⋙ G ⟶ K) (T : D) :
    opOf K T ≤ opOf G (H.obj T) := leOfHom (θ.app T).unop

def natCoef (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (θ : H ⋙ G ⟶ K) :
    CoefMap (RingHom.id R₀) (G ⋙ OAff s₀) (K ⋙ OAff s₀) where
  G := H
  α T := (mp (OAff s₀) (θ.app T)).toRingHom
  naturality {T T'} φ b := by
    change mp (OAff s₀) (θ.app T') (mp (OAff s₀) ((H ⋙ G).map φ) b) = mp (OAff s₀) (K.map φ) (mp (OAff s₀) (θ.app T) b)
    rw [← mp_comp, ← mp_comp, θ.naturality φ]
  smul T r b := by
    change mp (OAff s₀) (θ.app T) (r • b) = r • mp (OAff s₀) (θ.app T) b
    exact map_smul _ r b

theorem obAt_refine : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁)
    (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀)))
    (C D : Type) [Category.{0} C] [Category.{0} D] (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C)
    (_ : H ⋙ G ⟶ K), ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) →
      ObAt S α L K ((extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L c C D _ _ G K H θ h
  obtain ⟨u, hf, ho⟩ := h
  refine ⟨fun T T' a ↦ res (opOf_le_of_natTrans G K H θ T') (u _ _ (H.map a)), ?_, ?_⟩
  · exact GlobalTheory.T.isLineBundleFrameOnBasis_restrict_finer_opens X₀ C (opOf G) (opOf_le G) L u D (opOf K) (opOf_le K) H (opOf_le_of_natTrans G K H θ) hf
  · have key := GlobalTheory.T.unitCocycleLiftObstruction_pullback_naturality R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) D (K ⋙ OAff s₀)
      ((ofSys S).restrict K) (natCoef (s₀ := s₀) G K H θ) (fun T ↦ mp S.F (θ.app T)) u
      (fun T T' a ↦ res (opOf_le_of_natTrans G K H θ T') (u _ _ (H.map a)))
      ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c)
      (fun T b ↦ S.nat (θ.app T) b)
      (fun T T' a b ↦ by
        change mp S.F (K.map a) (mp S.F (θ.app T) b) = mp S.F (θ.app T') (mp S.F ((H ⋙ G).map a) b)
        exact (mp_comp S.F _ _ b).symm.trans
          ((congrArg (fun f ↦ mp S.F f b) (θ.naturality a).symm).trans (mp_comp S.F _ _ b)))
      (fun T T' a ↦ rfl) ho
    have hc : (extMap R₁ (natCoef (s₀ := s₀) G K H θ)).pull2 ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) =
        (extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c := by
      rw [← CoefMap.pullCohomologyTwo_comp]
      refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ (fun T b ↦ ?_) c
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [← hc]
    exact key

end GlobalTheory.LBObs
