import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricBalancedGeneratorPsiZeroLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPosHermOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UBaseData

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t : SAB H (Sp W)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∃ g, SmoothOfRelativeDimension g t.G.hom) → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ t.G)), (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ t.act.act a) → ∃ (D : DegPre W) (_ : Module (𝓞 E) D.X) (oa : letI := H.starRing; D.OAct (𝓞 E)) (φB : t.G.left ⟶ D.P.A.left) (e : X ≃ₗ[𝓞 E] D.X), D.PsiEven ∧ D.TauBimult ∧ (∀ y, PsiUnitOn D y Set.univ) ∧ (letI := H.starRing; TraceFormTwistIso D oa H.w0) ∧ IsAbPart t D oa φB ∧ ∀ y, (x₀ y).left ≫ φB = (D.c (e y)).left := by
  intro E _ _ _ H W _ _ _ t hp hA hK ⟨g, hg⟩ X _ _ _ _ x₀ hadd hlin
  letI := H.starRing
  let P := GlobalTheory.GenericPol.toPolAV t g hg hp hA hK
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ t.PP).1 t.sym
  have hψ0 : ∀ y : X, ∃ ψ : LB.Gen (LB.LinComb P.L (K := PUnit) (fun _ => ptK (x₀ y)) (fun _ => -1)), ψ.IsGen :=
    fun y => ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := FractionRing W) P.L P.isLB _ _
  choose ψ hψ using hψ0
  let D₀ : DegPre W :=
    { P := P, rig := t.PP.rig, rig_gen := t.PP.rigGen, cub := t.cub, sym := sym, sym_gen := hsym, sym_rig := hsym',
      X := X, c := x₀, c_add := hadd, psi := ψ, psi_gen := hψ }
  letI : Module (𝓞 E) D₀.X := ‹Module (𝓞 E) X›
  haveI : Module.Projective (𝓞 E) D₀.X := GlobalTheory.PointStepCompare.projective_of_free E (X := X)
  haveI : Module.Finite (𝓞 E) D₀.X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  have := t.act.hom H.w0
  let onB : D₀.P.OAct (𝓞 E) := ⟨t.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj t⟩
  obtain ⟨u, hu, hu0⟩ := GlobalTheory.ArcCM.CxFibre.exists_primGen t.PP (t.act.act H.w0) t.prim
  obtain ⟨ψ', hψ', oa, hoa, he, hb, hw, hU⟩ := GlobalTheory.UTau0.exists_symmetric_balanced_generator_psi_zero_localRing W D₀ (𝓞 E) onB hlin H.w0
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one H) ⟨u, hu, hu0⟩
  refine ⟨{ D₀ with psi := ψ', psi_gen := hψ' }, ‹Module (𝓞 E) X›, oa, 𝟙 _, LinearEquiv.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact he
  · exact hb
  · exact hU
  · exact hw
  · refine ⟨GlobalTheory.PolDeg.Wit.grpPullback_id t.G, fun a => ?_, GlobalTheory.PolDeg.Wit.idPull _, GlobalTheory.PolDeg.Wit.idPull_isGen t.PP.isLB⟩
    rw [hoa]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · intro y
    exact Category.comp_id _

end GlobalTheory.UBaseData
