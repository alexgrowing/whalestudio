import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.FieldCompat

open GlobalTheory.CechKS GlobalTheory.LogKSBal

theorem isTr_comp {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G]
    {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ G.left) (hm : IsGrpPullback A G (spMap x₀) m)
    (w : TanM (𝟙 (Sp R)) G) (v : epsR K ⟶ A)
    (hv : v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left) {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (y : Sp (DualNumber B) ⟶ A.left) (hy : IsTransl φ x v y) :
    IsTr G (φ.comp x₀) (x ≫ m) w (y ≫ m) := by
  obtain ⟨x₁, v₁, a, b, rfl⟩ := hy
  have dc : (dualMap φ).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) = dualMap (φ.comp x₀) :=
    RingHom.ext fun c ↦ by ext <;> simp [dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  obtain ⟨p, q, h₁, h₂, h₃⟩ := exists_mul_of_isGrpPullback hm _ x₁ v₁
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ G.hom) (by
      change _ = spMap ((algebraMap B (DualNumber B)).comp φ) ≫ spMap x₀
      rw [Category.assoc, hm.1.w, ← Category.assoc x, hx, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp'])
  refine ⟨p, q, ?_, ?_, h₃⟩
  · rw [h₁, a]; exact Category.assoc _ _ _
  · rw [h₂, b, ← dc, ← GlobalTheory.LogKSLoc.spMap_comp' (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) (dualMap φ)]
    refine (Category.assoc _ _ _).trans ?_
    rw [hv]
    exact (Category.assoc (spMap (dualMap φ)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀)) _).symm

theorem invField_baseChange : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left), IsGrpPullback A G (spMap x₀) m → ∀ (w : TanM (𝟙 (Sp R)) G) (e : Fld G.left), IsInv G w e → ∀ (v : epsR K ⟶ A), IsTangent v → v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left → ∀ (dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), GlobalTheory.KS.IsInvDer v dd → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), dd (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e O f) (m ⁻¹ᵁ O) := by
  intro R _ K _ x₀ G _ _ A _ _ m hm w e he v hvt hv dd hdd O f
  refine ext_valR _ _ fun B _ y hy => ?_
  have hb : y ≫ A.hom = spMap (Spec.preimage (y ≫ A.hom)).hom := (Spec.map_preimage _).symm
  generalize (Spec.preimage (y ≫ A.hom)).hom = β at hb
  obtain ⟨y', hy'⟩ := exists_isTransl β y hb v
  have hO : ⊤ ≤ y' ⁻¹ᵁ (m ⁻¹ᵁ O) := le_preimage_of_red (hy'.red hvt) hy
  rw [← snd_valR_transl hvt hdd hy' hy, CoeffWt.valR_app _ _ _ hO, valR_pbT y m le_rfl hy]
  refine he.2 B (β.comp x₀) (y ≫ m) (y' ≫ m) O f ?_ hy (isTr_comp x₀ m hm w v hv β y hb y' hy')
  rw [Category.assoc, hm.1.w, ← Category.assoc, hb, GlobalTheory.LogKSLoc.spMap_comp']

end GlobalTheory.Heat.FieldCompat
