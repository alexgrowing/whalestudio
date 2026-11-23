import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyStructureSheafCohomologyModelOfQuasiIsoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_finite_projective_model : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0})
    (s : X ⟶ Sp R), IsProper s → Flat s → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ),
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ (∃ n, ∀ p, n < p → IsZero (K.X p)) ∧
      Nonempty (Model s K) := by
  intro R _ _ X s hP hF
  haveI := hP
  haveI := hF
  letI := algebraΓOfHom s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have := isAffineHom_diagonal_of_isSeparated s
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := GlobalTheory.isAffineOpen_finset_biInf hD
  have hM : (LB.triv X).IsLB := LB.isLB_triv X
  have := Twist.isFiniteQC_twist (F := structureModule X) hM
  obtain ⟨K, φ, h1, h2, -, h4, -, -, h7⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) m
      (fun p hp => GlobalTheory.AbLaw.isZero_cechLB_X s (LB.triv X) _ (by rw [Fintype.card_fin]; exact hp.le))
      (GlobalTheory.AbLaw.flat_cechLB_X s hM hD') (fun n => by
        obtain ⟨e⟩ := GlobalTheory.FieldChangeInter.nonempty_coh_equiv s hM hc hD' n
        have := GlobalTheory.ProperFinite.finite_coh_of_isProper s (twist (structureModule X) (LB.triv X)) n
        exact Module.Finite.equiv e.symm)
  have hsep : IsSeparated s := inferInstance
  have hDa : ∀ i, IsAffineOpen (D i) := fun i => hD i
  obtain ⟨MC⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology R X s (Fin m) D hsep hDa hc
  exact ⟨K, fun p => ⟨h2 p, h4 p⟩, ⟨m, h1⟩, GlobalTheory.T.nonempty_structureSheafCohomologyModel_of_quasiIso R X s K _ φ (fun S _ _ => h7 S) MC⟩

end GlobalTheory.AbCoh
