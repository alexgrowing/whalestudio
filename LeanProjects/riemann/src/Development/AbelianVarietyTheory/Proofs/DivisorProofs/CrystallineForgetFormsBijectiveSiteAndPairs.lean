import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalFirstNeighbourhoodRetractionFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientsAcyclicOfTwoSectionsRetractionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH1BijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH2BijectiveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem fnMap_pullbackBijective12_of_acyclic {C : Type 1} [Category.{0} C] (K : Cx C)
    (h1 : K.M1.Ac0 ∧ K.M1.Ac1 ∧ K.M1.Ac2) (h2 : K.M2.Ac0 ∧ K.M2.Ac1 ∧ K.M2.Ac2) (h3 : K.M3.Ac0 ∧ K.M3.Ac1 ∧ K.M3.Ac2) :
    K.fnMap.PullbackBijectiveDegreesOneTwo :=
  And.intro (GlobalTheory.T.forget_positive_h1_bijective C K h1.1 h1.2.1 h2.1) (GlobalTheory.T.forget_positive_h2_bijective C K h1.2.1 h1.2.2 h2.1 h2.2.1 h3.1)

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  {Y : Scheme.{0}} {i : X ⟶ Y}

theorem top_le_preimage_of_hom {T T' : Thick κ t} (f : T ⟶ T') (U : Y.Opens) (h : ⊤ ≤ (T.x ≫ i) ⁻¹ᵁ U) :
    ⊤ ≤ (T'.x ≫ i) ⁻¹ᵁ U := by
  intro p _
  rw [← f.pt, Category.assoc]
  exact h (Set.mem_univ ((spMap f.φ₀).base p))

variable (κ t i)

@[simps] def liftE (S : Thick κ t ⥤ Thick κ t) (u : 𝟭 _ ⟶ S) : EE κ t i ⥤ EE κ t i where
  obj a := ⟨⟨S.obj a.obj.T, a.obj.U, a.obj.hU, top_le_preimage_of_hom (u.app a.obj.T) a.obj.U a.obj.mem⟩, a.property⟩
  map f := ⟨⟨S.map f.hom.1, f.hom.2⟩⟩
  map_id a := ObjectProperty.hom_ext _ (Subtype.ext (S.map_id a.obj.T))
  map_comp f g := ObjectProperty.hom_ext _ (Subtype.ext (S.map_comp f.hom.1 g.hom.1))

def liftT (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S) : 𝟭 (EE κ t i) ⟶ liftE κ t i S u where
  app a := ⟨⟨v.app a.obj.T, le_rfl⟩⟩
  naturality a b f := ObjectProperty.hom_ext _ (Subtype.ext (v.naturality f.hom.1))

variable {κ t i}

theorem acyc_res_pE (M : Coef (Thick κ t)) (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S)
    (r : ∀ T, M.obj (S.obj T) →+ M.obj T)
    (h : (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x)) ∧
      (∀ T x, r T (M.map (u.app T) x) = 0) ∧ (∀ T x, r T (M.map (v.app T) x) = x)) :
    (M.res (pE κ t i)).Ac0 ∧ (M.res (pE κ t i)).Ac1 ∧ (M.res (pE κ t i)).Ac2 :=
  GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ (M.res (pE κ t i)) (liftE κ t i S u) (liftT κ t i S u u) (liftT κ t i S u v) (fun a ↦ r a.obj.T)
    (fun a b f x ↦ h.1 a.obj.T b.obj.T f.hom.1 x) (fun a x ↦ h.2.1 a.obj.T x) (fun a x ↦ h.2.2 a.obj.T x)

theorem crystalline_forget_forms_bijective_site_and_pairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (KK κ t).fnMap.PullbackBijectiveDegreesOneTwo ∧ ((KK κ t).res (pE κ t i)).fnMap.PullbackBijectiveDegreesOneTwo := by
  intro R _ I κ X t Y i
  obtain ⟨S, u, v, r1, r2, r3, h1, h2, h3a, h3b, h3c⟩ := GlobalTheory.T.exists_diagonal_firstNeighbourhood_retraction_forms R I κ X t
  have h3 := And.intro h3a (And.intro h3b h3c)
  exact ⟨fnMap_pullbackBijective12_of_acyclic _ (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r1 h1.1 h1.2.1 h1.2.2)
      (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r2 h2.1 h2.2.1 h2.2.2) (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r3 h3a h3b h3c),
    fnMap_pullbackBijective12_of_acyclic _ (acyc_res_pE (i := i) _ S u v r1 h1) (acyc_res_pE (i := i) _ S u v r2 h2)
      (acyc_res_pE (i := i) _ S u v r3 h3)⟩

end GlobalTheory.PDForm
