import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRham
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HdRFibre

set_option maxHeartbeats 1000000 in

theorem fibre_baseChange : ∀ (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [CommRing O] (a : OAct O A₀), ∃ f : HdR A₀ →ₛₗ[algebraMap C₀ (IsLocalRing.ResidueField C₀)] HdR ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀), Function.Surjective f ∧ (∀ h, f h = 0 → h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))) ∧ ∀ (x : O) (h : HdR A₀), f (act (dp0 C₀) (𝟙 _) a x h) = act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a) x (f h) := by
  intro C₀ _ _ A₀ _ _ hA O _ a
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ A₀ hA
  obtain ⟨hFree, -, hBC, -, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hh := isGrpPullback_pullback A₀ (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))
  have hbc := (hBC C₀ A₀ g hA hg (IsLocalRing.ResidueField C₀) _ _ hh).1
  obtain ⟨hfin, hproj, -⟩ := hFree.prim hA hg
  haveI := Module.finitePresentation_of_projective C₀ (primDR A₀)
  haveI : Module.Free C₀ (primDR A₀) := Module.free_of_flat_of_isLocalRing
  refine ⟨hbc.bcMap, ?_, ?_, ?_⟩
  · intro h'
    let l : primDR A₀ →ₗ[C₀] IsLocalRing.ResidueField C₀ :=
      { toFun c := h' ((Published.AbelianDeRham.bcMor hh).pull c)
        map_add' c d := by rw [map_add, map_add]
        map_smul' r c := by
          rw [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
    obtain ⟨hh', hhl⟩ := Module.projective_lifting_property (Algebra.linearMap C₀ (IsLocalRing.ResidueField C₀)) l
      IsLocalRing.residue_surjective
    exact ⟨hh', hbc.corr_iff.1 fun c ↦ (LinearMap.congr_fun hhl c).symm⟩
  · intro x hx
    have hc := hbc.corr_iff.2 hx
    refine GlobalTheory.CrysFree.mem_smul_top_of_forall _ x fun c ↦ ?_
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (hc c).symm.trans (LinearMap.zero_apply _)
  · intro x h
    haveI := a.hom x
    haveI := (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a).hom x
    refine hbc.corr_iff.1 ?_
    exact GrpMor.Corr.push (m := Published.AbelianDeRham.bcMor hh) (Published.AbelianDeRham.bcMor hh)
      (a.act x) ((OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a).act x)
      (pullback.lift_fst _ _ _).symm (hbc.corr_iff.2 rfl)

end GlobalTheory.HdRFibre
