import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformizationLinear
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.NotExistsEvenTwistSymOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsEllipticCurveTwoAdic
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoData
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnifDvrCompare
open GlobalTheory.UU GlobalTheory.LN GlobalTheory.IndefiniteRowSideFullHecke.UniformizationLinear

theorem exists_point_of_fixed {F F' : Type} [Field F] [Field F'] [Algebra F F'] [IsGalois F F'] {X : Scheme.{0}}
    (x' : Sp F' ⟶ X) (h : ∀ σ : Gal(F'/F), spMap (σ : F' →+* F') ≫ x' = x') :
    ∃ x : Sp F ⟶ X, spMap (algebraMap F F') ≫ x = x' := by
  obtain ⟨⟨y, f⟩, rfl⟩ := (Scheme.SpecToEquivOfField F' X).symm.surjective x'
  have e : (Scheme.SpecToEquivOfField F' X).symm ⟨y, f⟩ = Spec.map f ≫ X.fromSpecResidueField y := rfl
  rw [e] at h ⊢
  have hf : ∀ a, f.hom a ∈ (algebraMap F F').range := fun a => by
    refine IntermediateField.mem_bot.1 ((InfiniteGalois.mem_bot_iff_fixed _).2 fun σ => ?_)
    have := h σ
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp] at this
    exact congrArg (fun q => q.hom a) (Spec.map_injective this)
  choose g hg using hf
  have inj := (algebraMap F F').injective
  let g' : X.residueField y →+* F :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun a b => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [hg, map_add, map_add, hg, hg]) }
  refine ⟨Spec.map (CommRingCat.ofHom g') ≫ X.fromSpecResidueField y, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext hg)

section Totality

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

end Totality

section HidaSetting

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

end HidaSetting

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Triples

def PelOver (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp R)) (D : DegData R I)
    (A : PolAV (Sp (FractionRing R))) (U : Unif I D A t.G), U.LG = t.PP →
    ∃ P : PELUnif I t, P.D = D ∧ P.A = A ∧ HEq P.U U ∧ P.TorsionIso

end GlobalTheory.UnifDvrCompare
end
