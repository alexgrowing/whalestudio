import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormUnr

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

private theorem valued_le_one {F : Type} [Field F] [NumberField F] (v : Pl F) {x : v.adicCompletion F}
    (h : x ∈ (ValuativeRel.valuation (v.adicCompletion F)).integer) : Valued.v x ≤ 1 := by
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one.1
    ((Valuation.mem_integer_iff _ _).1 h)

private theorem isUnitAt_det {F : Type} [Field F] [NumberField F] (v : Pl F) (n : ℕ)
    {g : GL (Fin n) (v.adicCompletion F)} (hg : g ∈ GLnLocal.integralGL (v.adicCompletion F) n) :
    IsUnitAt v (Matrix.GeneralLinearGroup.det g) := by
  obtain ⟨u, rfl⟩ := hg
  have e : ((Matrix.GeneralLinearGroup.det (GLnLocal.integralGLHom (v.adicCompletion F) n u) :
      (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      ((Matrix.GeneralLinearGroup.det u).val : v.adicCompletion F) := by
    show ((RingHom.mapMatrix (ValuativeRel.valuation (v.adicCompletion F)).integer.subtype)
      (u : Matrix (Fin n) (Fin n) _)).det = _
    rw [← RingHom.map_det]
    rfl
  change Valued.v _ = 1
  rw [e]
  generalize Matrix.GeneralLinearGroup.det u = d
  have h1 := valued_le_one v d.val.2
  have h2 := valued_le_one v (d⁻¹).val.2
  have h3 : Valued.v (d.val : v.adicCompletion F) * Valued.v ((d⁻¹).val : v.adicCompletion F) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]
    simp
  exact le_antisymm h1 (h3 ▸ mul_le_of_le_one_right' h2)

theorem UpperTheory.Gal.InertialTypesAlt.G.normInt :
    UpperTheory.Gal.InertialTypesAlt.G.NormInt := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n _ v hv g hg η hη
  exact UpperTheory.ConvolutionTheory.Sph.normUnr F E η hη v hv _ (isUnitAt_det v n hg)
