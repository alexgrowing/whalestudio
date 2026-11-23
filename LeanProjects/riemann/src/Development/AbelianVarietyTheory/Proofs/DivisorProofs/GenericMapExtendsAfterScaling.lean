import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ToAbSheafPreservesFiniteLimits

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.ClearDenom

theorem exists_smul_eq_genRes_map : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O)
    (E E' : Z.X.Modules) (n m : ℕ), GlobalTheory.VB.IsVB E n → GlobalTheory.VB.IsVB E' m → ∀ (a : Z.genRes.obj E ⟶ Z.genRes.obj E'),
    ∃ (g : O) (u : E ⟶ E'), g ≠ 0 ∧ Z.genRes.map u = a ≫ Z.genRes.map (smulHom E' (Z.const g)) := by
  intro O _ _ _ Z E E' n m hE hE' a
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let e := Scheme.Modules.restrictFunctorIsoPullback Z.gen.ι
  let b : (Scheme.Modules.restrictFunctor Z.gen.ι).obj E ⟶ (Scheme.Modules.restrictFunctor Z.gen.ι).obj E' :=
    e.hom.app E ≫ a ≫ e.inv.app E'
  let σ : Γ(VB.homMod E E', Z.gen) := PtNorm.homOfRestrict b
  haveI : IsFiniteQC E' := hE'.isFiniteQC
  haveI : IsFiniteQC (VB.homMod E E') := PtNorm.isFiniteQC_homMod hE
  obtain ⟨k, t, ht⟩ := GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (VB.homMod E E') (U := ⊤)
    (isCompact_univ) (isQuasiSeparated_univ) (Z.const ϖ) le_top
    (Z.gen_eq_basicOpen hϖ.ne_zero hϖ.not_isUnit) σ
  refine ⟨ϖ ^ k, VB.homGlobalEquiv E E' t, pow_ne_zero _ hϖ.ne_zero, ?_⟩
  set u := VB.homGlobalEquiv E E' t with hu
  have key : (Scheme.Modules.restrictFunctor Z.gen.ι).map u =
      b ≫ (Scheme.Modules.restrictFunctor Z.gen.ι).map (smulHom E' (Z.const (ϖ ^ k))) := by
    ext T x
    have hW : Z.gen.ι ''ᵁ T ≤ Z.gen := Z.gen.ι.image_le_opensRange T |>.trans Z.gen.opensRange_ι.le
    change u.app (Z.gen.ι ''ᵁ T) x = (smulHom E' (Z.const (ϖ ^ k))).app (Z.gen.ι ''ᵁ T) (b.app T x)
    change VB.homApp t le_top x = _
    erw [smulHom_app_apply]
    have h2 : VB.homApp t le_top x = VB.homApp ((ConcreteCategory.hom (Z.X.presheaf.map (homOfLE (le_top : Z.gen ≤ ⊤)).op)) (Z.const ϖ) ^ k • σ) hW x := by
      rw [ht]; rfl
    rw [h2, VB.homApp_smul]
    show resG Z.X hW (_ ^ k) • VB.homApp σ hW x = _
    erw [PtNorm.homApp_homOfRestrict_image]
    congr 1
    rw [map_pow, Vert.Model.const, Vert.Model.const, map_pow, map_pow]
    congr 1
    exact resG_resG (le_top : Z.gen ≤ ⊤) hW (Z.const ϖ)
  have hn := e.hom.naturality u
  have hs := e.hom.naturality (smulHom E' (Z.const (ϖ ^ k)))
  rw [← cancel_epi (e.hom.app E)]
  change e.hom.app E ≫ (Scheme.Modules.pullback Z.gen.ι).map u =
    e.hom.app E ≫ a ≫ (Scheme.Modules.pullback Z.gen.ι).map (smulHom E' (Z.const (ϖ ^ k)))
  rw [← hn, key, Category.assoc, hs]
  simp only [b, Category.assoc, Iso.inv_hom_id_app_assoc]

end GlobalTheory.ClearDenom
