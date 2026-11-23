import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFiberIsAlgebraicResidueFieldOfLftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureEqOfIsAlgebraicResidueStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefDescent

theorem exists_algebraic_point : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧ (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) :=
  GlobalTheory.T.exists_mem_fiber_isAlgebraic_residueField_of_lft

theorem dim_closure_eq_of_isAlgebraic : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y), (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) → topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) :=
  GlobalTheory.T.topologicalKrullDim_closure_eq_of_isAlgebraic_residue

theorem exists_curve_over : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F),
    π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    topologicalKrullDim (Z : Set X) = 1 → ∃ C : Closeds Y, IsIrreducible (C : Set Y) ∧
      topologicalKrullDim (C : Set Y) = 1 ∧ π '' (C : Set Y) = (Z : Set X) := by
  intro F _ Y X π sX p hπ hX hY hs Z hZi hZd
  obtain ⟨hPX, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX
  obtain ⟨hPY, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hY
  subst hπ
  have : IsProper π := IsProper.of_comp π sX
  obtain ⟨η, hη⟩ := QuasiSober.sober hZi Z.isClosed
  obtain ⟨y₀, hy₀⟩ := π.surjective η
  obtain ⟨y, hy, halg⟩ := exists_algebraic_point Y X π y₀
  have hd := dim_closure_eq_of_isAlgebraic F Y X π sX y halg
  rw [hy, hy₀, hη.def] at hd
  refine ⟨Closeds.closure {y}, isIrreducible_singleton.closure, ?_, ?_⟩
  · exact hd.trans hZd
  · change π '' closure {y} = Z
    rw [← π.isClosedMap.closure_image_eq_of_continuous π.continuous, Set.image_singleton, hy, hy₀, hη.def]

theorem isNef_of_pull : ∀ (F : Type) [Field F] [NumberField F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F) (L : LB X) (hL : L.IsLB) (L' : LB Y) (hL' : L'.IsLB), π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → CechPic.pull π (cls L hL) = cls L' hL' → (letI := algebraΓOfHom p; IsNef F L') → (letI := algebraΓOfHom sX; IsNef F L) := by
  intro F _ _ Y X π sX p L hL L' hL' hπ hX hY hs hcl hnef
  letI := algebraΓOfHom sX
  letI := algebraΓOfHom p
  have hnef' : IsNef F L' := hnef
  obtain ⟨hPX, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX
  obtain ⟨hPY, A', hA'⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hY
  have : IsProper (strHom F X) := by rwa [strHom_eq (f := sX) fun _ => rfl]
  have : IsProper (strHom F Y) := by rwa [strHom_eq (f := p) fun _ => rfl]
  refine ⟨hL, fun Z hZ => ?_⟩
  obtain ⟨C, hCi, hCd, hCZ⟩ := exists_curve_over F Y X π sX p hπ hX hY hs Z hZ.1 hZ.2
  have hC : IsCompleteCurve F C := (isCompleteCurve_iff (f := p) (fun _ => rfl)).2 ⟨hCi, hCd⟩
  by_contra hneg
  push_neg at hneg
  have hM := isLB_dual hL
  have hMpos : 0 < interNumRed F Z ![dual L] := by rw [hZ.interNumRed_dual hA hL]; linarith
  obtain ⟨r, hr, s, hs0⟩ := PosBaseChange.exists_hasNonzeroSec (k := F) hA hM hZ.1 hZ.2.le fun _ => hMpos
  have hr' := isLB_lbPow hM r
  have hZc : Closeds.closure (π '' (C : Set Y)) = Z := by
    ext1
    simp only [Closeds.coe_closure, hCZ, Z.isClosed.closure_eq]
  obtain ⟨φ, hφ⟩ : ∃ φ, φ ≫ redι Z = redι C ≫ π := ⟨IsClosedImmersion.lift (redι Z) (redι C ≫ π) (by
    rw [← hZc, Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_vanishingIdeal]), IsClosedImmersion.lift_fac _ _ _⟩
  have hsφ : Function.Surjective φ := fun z => by
    obtain ⟨y, hy, e⟩ := hCZ.ge ((range_redι Z).le ⟨z, rfl⟩)
    obtain ⟨y, rfl⟩ := (range_redι C).ge hy
    exact ⟨y, (redι Z).isClosedEmbedding.injective ((congrArg (fun q => q y) hφ).trans e)⟩
  have := isIntegral_red hC.1
  have := isIntegral_red hZ.1

  obtain ⟨z, hz⟩ : ∃ z, z ∉ nonzeroLocus s := by
    by_contra! h
    obtain ⟨t, ht⟩ := exists_isGen_of_nonzeroLocus_eq_top s (top_unique fun z _ => h z)
    have e0 := (cls_eq_zero_iff (LB.isLB_pull hr' (redι Z))).2 ⟨t, ht⟩
    have h1 : interNumRed F Z ![lbPow (dual L) r] = 0 := by
      letI := algebraΓAlong F (redι Z)
      rw [interNumRed_one_eq hr']
      exact interNum_eq_zero_of_cls_eq_zero F _ (isLB_vecOne (LB.isLB_pull hr' _)) 0 e0
    rw [hZ.interNumRed_lbPow hA hM] at h1
    have : (0 : ℤ) < r := by exact_mod_cast hr
    nlinarith
  letI := algebraΓAlong F (redι C)
  have := hC.isProper_strHom
  obtain ⟨x, hx⟩ := hsφ (genericPoint _)
  have hx' : x ∈ nonzeroLocus (secPull s φ) := (nonzeroLocus_secPull s φ).ge (by
    change φ x ∈ nonzeroLocus s
    rw [hx]; exact (sec_ne_zero_iff s).1 hs0)
  obtain ⟨c, hc⟩ := hsφ z
  have h0 := (interNum_one_nonneg_of_sec (k := F) (hA'.pull_of_isClosedImmersion (redι C))
      ((topologicalKrullDim_red C).trans hCd) (LB.isLB_pull (LB.isLB_pull hr' _) φ) (secPull s φ)
      ((sec_ne_zero_iff _).1 (sec_ne_zero_of_mem hx'))).2 (fun htop => hz (by
        have := (nonzeroLocus_secPull s φ).le (htop.ge (show c ∈ (⊤ : Opens _) from trivial))
        rw [← hc]; exact this))
  have hD' := isLB_dual hL'
  have hP' := isLB_lbPow hD' r
  have h1 : interNumRed F C ![lbPow (dual L') r] =
      interNum F (structureModule _) ![((lbPow (dual L) r).pull (redι Z)).pull φ] := by
    rw [interNumRed_one_eq hP']
    refine interNum_congr_cls F _ (isLB_vecOne (LB.isLB_pull hP' _))
      (isLB_vecOne (LB.isLB_pull (LB.isLB_pull hr' _) φ)) fun i => ?_
    fin_cases i
    change pull (redι C) (cls _ hP') = pull φ (pull (redι Z) (cls _ hr'))
    rw [← pull_comp, hφ, pull_comp, cls_lbPow hD', cls_lbPow hM, cls_dual hL', cls_dual hL, ← hcl]
    simp only [map_nsmul, map_neg]
  rw [← h1, hC.interNumRed_lbPow hA' hD', hC.interNumRed_dual hA' hL'] at h0
  have h2 := hnef'.2 C hC
  have : (0 : ℤ) ≤ r := by positivity
  nlinarith

end GlobalTheory.NefDescent
