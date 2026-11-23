import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsAddEquivOfSplitTorusIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusEndChar

theorem main : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (f : G ⟶ G), IsMonHom f → letI := E.addCommGroup; ∃! ρ : E.X →+ E.X, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ f ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ χ) := by
  intro k _ G _ _ E f hf
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  haveI : IsMonHom E.q := E.q_hom
  haveI : IsMonHom E.i := E.i_hom
  haveI : IsProper E.B.hom := E.isAbelian.proper
  haveI : ConnectedSpace (Sp k) := by
    have : PreconnectedSpace (PrimeSpectrum k) := by
      refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint k) fun y _ =>
        ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
      exact (IsLocalRing.specializes_closedPoint y).mem_closure
    exact (⟨inferInstance⟩ : ConnectedSpace (PrimeSpectrum k))
  have hk : E.i ≫ f ≫ E.q = toUnit _ ≫ η[E.B] :=
    splitTorus_hom_proper_trivial_local k E.X E.B (E.i ≫ f ≫ E.q) inferInstance
  let τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X :=
    E.isKernel.lift (E.i ≫ f) (toUnit _) (by rw [Category.assoc, hk])
  have hτ : τ ≫ E.i = E.i ≫ f := E.isKernel.lift_fst _ _ _
  have hmono : Mono E.i := E.isKernel.mono_fst_of_mono
  have hτm : IsMonHom τ := by
    constructor
    · rw [← cancel_mono E.i, Category.assoc, hτ, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono E.i, Category.assoc, Category.assoc, hτ, IsMonHom.mul_hom_assoc (f := E.i),
        IsMonHom.mul_hom (f := f), IsMonHom.mul_hom (f := E.i), tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hτ]
  obtain ⟨ρ, hρ⟩ := SplitTorusHom.exists_addMonoidHom (S := Sp k) τ
  refine ⟨ρ, ⟨τ, hτ, fun χ => Units.ext ?_⟩, ?_⟩
  · rw [chV_val, hρ]
  · rintro ρ' ⟨τ', hτ', hρ'⟩
    have hττ : τ' = τ := by rw [← cancel_mono E.i, hτ', hτ]
    subst hττ
    ext χ
    apply SplitTorusHom.charUnit_injective (S := Sp k)
    rw [← hρ', chV_val, hρ]

end GlobalTheory.TorusEndChar
