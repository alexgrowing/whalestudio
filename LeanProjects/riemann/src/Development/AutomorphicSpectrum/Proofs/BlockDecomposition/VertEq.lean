import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureOfCoheightField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepClassDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.O1ClassPullbackNaturalityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericPointNonvanishingCoordinateSectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateDivisorMultiplicitySumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharacteristicDimensionZeroStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.Vert

theorem key (p : ℕ) [Fact p.Prime] {m : ℕ} {n : Fin (m + 1) → ℕ} (a : Fin (m + 1) → ℤ) (d : ℕ) :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] [Algebra (ZMod p) Γ(Z, ⊤)],
      topologicalKrullDim Z = d → ∀ (L : LB Z) (hL : L.IsLB),
      cls L hL = ∑ k, a k • cls (pullO (f ≫ prB n k) 1) (isLB_pullO _ 1) →
      topSelfIntersection (ZMod p) L d = geoNum d (ptIdeal (f (genericPoint Z))) (fun _ => a) := by
  induction d with
  | zero =>
    intro Z _ f _ _ hd L hL _
    rw [topSelf_zero]
    exact GlobalTheory.T.euler_characteristic_dimension_zero m n Z f p hd _
  | succ d ih =>
    intro Z _ f _ _ hd L hL hc
    have hp : IsProjOver (strHom (ZMod p) Z) :=
      VertProj.isProjOver_strHom_zmod ℤ _ (mpStr ℤ m n) _ (isArithVar_mpStr m n) Z f p
    have hf := algebraMap_eq_strHom (ZMod p) Z
    have : AlgebraicGeometry.IsNoetherian Z := isNoetherian_of_isProjOver hp
    have hDV := diffVanish_chiPic_of_isProjOver hf (structureModule Z) hp (d := d + 1)
      (by rw [QCoh.suppDim_structureModule, hd])
    have red : ∀ w : Z, Order.coheight w = 1 →
        interNumRed (ZMod p) (⟨closure {w}, isClosed_closure⟩ : Closeds Z) (fun _ : Fin d => L) =
          geoNum d (ptIdeal (f w)) (fun _ => a) := by
      intro w hw
      let C : Closeds Z := ⟨closure {w}, isClosed_closure⟩
      have hirr : IsIrreducible (C : Set Z) := isIrreducible_singleton.closure
      haveI := isIntegral_red hirr
      letI : Algebra (ZMod p) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) :=
        algebraΓOfHom (redι C ≫ strHom (ZMod p) Z)
      have hfZ : ∀ r : ZMod p, (redι C).appTop (algebraMap (ZMod p) Γ(Z, ⊤) r) =
          algebraMap (ZMod p) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) r := fun r => by
        rw [hf r]; rfl
      have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme = d := by
        rw [topologicalKrullDim_red]
        exact VdmRec.CutSec.dim_closure_of_coheight (isArithVar_mpStr m n) f hd hw
      have hcl : cls (L.pull (redι C)) (pull_isLB hL _) =
          ∑ k, a k • cls (pullO ((redι C ≫ f) ≫ prB n k) 1) (isLB_pullO _ 1) := by
        rw [cls_pull hL, hc, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, Category.assoc, GlobalTheory.T.cls_pullO_one_comp_eq_pull (redι C) (f ≫ prB n k)]
      have e := ih _ (redι C ≫ f) hdim _ (pull_isLB hL _) hcl
      rw [interNumRed_def, interNumSub_def, interNumOn_def,
        interNum_pushforward_of_isClosedImmersion hfZ _ (fun _ => hL)]
      rw [topSelf_def] at e
      refine e.trans ?_
      rw [Scheme.Hom.comp_apply, PullVanish.redι_genericPoint w]
    have hrel := (isMultiProjPrime_ptIdeal m n (f (genericPoint Z))).2.2
    have e := hDV.interNum_update_of_cls_eq_sum (ι := Fin (d + 1)) (L := fun _ => L) (by simp) (fun _ => hL) 0
      (Finset.univ) (P := fun k => pullO (f ≫ prB n k) 1) (fun k => isLB_pullO _ 1) a hL hc
    have upd : ∀ N : LB Z, Function.update (fun _ : Fin (d + 1) => L) 0 N = Fin.cons N (fun _ : Fin d => L) := by
      intro N
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp [Function.update_of_ne (Fin.succ_ne_zero i)]
    simp only [upd] at e
    have e0 : (Fin.cons L (fun _ : Fin d => L) : Fin (d + 1) → LB Z) = fun _ => L := by
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
    rw [e0] at e
    rw [topSelf_def, e, geoNum, dif_pos hrel]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine congrArg (a k * ·) ?_
    have hl := (hrel k).choose_spec
    have hs := GlobalTheory.T.generic_point_nonvanishing_coordinate_section m n Z f k _ hl
    rw [GlobalTheory.CompanionTheory.Ar.IntersectionMultiplicitySection.interNum_cons_eq_finsum_mult (ZMod p) Z hp d (by rw [hd]) _ (isLB_pullO _ 1)
      (fun _ => L) (fun _ => hL) _ hs]
    refine Eq.trans (finsum_congr fun w => ?_) (GlobalTheory.T.coordinate_divisor_multiplicity_sum m n Z f k _ hs (fun W => geoNum d W (fun _ => a)))
    by_cases hw : (divOfSec (isLB_pullO _ 1) _ hs).mult w = 0
    · rw [hw, zero_mul, zero_mul]
    · rw [red w (CartierDiv.coheight_eq_one_of_mult_ne_zero hw)]

theorem vertEq : VertEq := by
  intro m n M A hA X i _ Z _ j _ p _ _ d hd
  refine key p A.a d Z (j ≫ i) hd _ (pull_isLB (pull_isLB M.isLB _) _) ?_
  rw [cls_pull (pull_isLB M.isLB _), cls_pull M.isLB, GlobalTheory.T.hermRep_class_decomposition m n M A hA, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, map_zsmul, Category.assoc, GlobalTheory.T.cls_pullO_one_comp_eq_pull, GlobalTheory.T.cls_pullO_one_comp_eq_pull]

end GlobalTheory.CompanionTheory.MixZ.Vert
