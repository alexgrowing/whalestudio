import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

noncomputable section

namespace GlobalTheory.ThetaFibreScalar

theorem famφB_zero {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) :
    D.famφB 0 = ![𝟙 _, 𝟙 _, (toUnit D.P.A ≫ η[D.P.A]).left, (toUnit D.P.A ≫ η[D.P.A]).left] := by
  have h0 := GlobalTheory.Mum.degPre_c_zero D
  have e1 : toUnit D.P.A ≫ D.c 0 = toUnit D.P.A ≫ η[D.P.A] := by
    rw [h0, comp_one, Hom.one_def]
  have e2 : padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0) = 𝟙 D.P.A := by
    rw [h0, comp_one, padd, ← Hom.mul_def, _root_.mul_one]
  have e2' : padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ η[D.P.A]) = 𝟙 D.P.A := by rw [← e1]; exact e2
  funext i
  fin_cases i <;> simp [DegPre.famφB, e1, e2']

theorem thetaFibre_scalar : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (K : Type) [Field K] (ev : V₁ →+* K) (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), ∃ Λ : K, ∀ (Z : Scheme) (r : Z ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left) (z : Z) J, Good D.P.L z J → sval th r z J = gs (r ≫ (fst (Over.mk (spMap ev)) D.P.A).left) z ⊤ (GlobalTheory.Ex.fnOf Λ) * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J := by
  intro V₁ _ _ D θ hθ K _ ev th
  have hF : FormEq (fun _ : Fin 1 => (snd (Over.mk (spMap ev)) D.P.A).left) (fun _ => ((1 : ℕ) : ℤ))
      (fun i => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 i) (DegPre.famε 1) := by
    intro U _ h
    rw [famφB_zero]
    simp [Fin.prod_univ_four, DegPre.famε]
  obtain ⟨th', hth'⟩ := exists_sec D.P.isLB hF th
  obtain ⟨r, hr, -⟩ := hθ K ev (pullTo D ev θ) (isPullSecLC_pullTo D ev θ) th'
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (r 0), fun Z rr z J hJ => ?_⟩
  refine (hth' Z rr z J hJ).symm.trans ?_
  have hm := hJ.mem (fun i => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 i) rr
  have h2 := sval_of (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J
      (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k)) (fun k => by rw [Category.assoc])
  erw [h2]
  rw [sval]
  erw [hr]
  rw [Fin.sum_univ_one]
  erw [gs_mul _ _ _ hm]
  congr 1
  · erw [gs_res rr z le_top hm]
    have := gs_pull rr (fst (Over.mk (spMap ev)) D.P.A).left z ⊤ trivial (r 0)
    refine this.trans ?_
    congr 1
    simp [GlobalTheory.Ex.fnOf]
  · have hle := wchart_comp_le D.P.L (D.famφB 0) (snd (Over.mk (spMap ev)) D.P.A).left
      (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k))
    erw [isPullSecLC_pullTo D ev θ, gs_res rr z hle hm]
    exact gs_pull rr (snd (Over.mk (spMap ev)) D.P.A).left z
      (LB.wchart D.P.L (D.famφB 0) (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k))) (hle hm)
      (θ.f (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k)))

end GlobalTheory.ThetaFibreScalar
