import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabTors
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThetaConj

def conjHom {R : Type} [CommRing R] [IsDomain R] (σ : Kb R →ₐ[FractionRing R] Kb R) :
    TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact σ.commutes a)

end GlobalTheory.ThetaConj

open GlobalTheory.ThetaConj GlobalTheory.ThetaCoord in

theorem GlobalTheory.isThetaPt_conj : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (k : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (I : Type) (x x' : I → (TFK (R := R) (Kb R) ⟶ A.A)) (v : I → Kb R), (∀ i, (x' i).left = spMap σ.toRingHom ≫ (x i).left) → IsThetaPt A k x (fun i => GlobalTheory.Ex.fnOf (v i)) → IsThetaPt A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
  intro R _ _ A k σ I x x' v hx H
  have hs : Subsingleton (TFK (R := R) (Kb R)).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (Kb R)))
  have hn : Nonempty (TFK (R := R) (Kb R)).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Kb R)))
  let e : Kb R ≃ₐ[FractionRing R] Kb R :=
    AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hi : conjHom σ ≫ conjHom e.symm.toAlgHom = 𝟙 _ := by
    refine Over.OverMorphism.ext ?_
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_id _))
    ext a
    exact e.apply_symm_apply a
  have Q := isThetaPtOver_pull A (isThetaPtOver_of_subsingleton A H) _ _ hi
  have Q' : IsThetaPtOver A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
    convert Q using 2 with a a
    · exact Over.OverMorphism.ext (hx a)
    · exact congrArg (fun q => q.hom (v a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ.toRingHom))
  refine ⟨H.1, H.2.1, fun p => ⟨⊤, trivial, ?_⟩⟩
  let j : TFK (R := R) (Kb R) ⟶ overRes (T := TFK (R := R) (Kb R)) ⊤ :=
    Over.homMk (TFK (R := R) (Kb R)).left.topIso.inv (by
      change _ ≫ Scheme.Opens.ι ⊤ ≫ _ = _
      rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  exact isThetaPtOver_pull A Q' (overResι ⊤) j
    (Over.OverMorphism.ext (TFK (R := R) (Kb R)).left.topIso.hom_inv_id)

end
