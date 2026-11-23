import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCanForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCotValEqTanVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfRangeSupSmulTopEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelBijectiveOfPowEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToOmegaSpanModMaximalStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

set_option maxHeartbeats 1000000 in

theorem isLieImage_iff_lieCorr : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (E : primDR A ≃ₗ[R] G.RigExt), (∀ c, IsCan t c (E c)) → ∀ (h : HdR A) (v : epsR R ⟶ A), IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie (E.symm.dualMap h)) v := by
  intro hHdR p _ R _ hnil A _ g hA hsm G t E hE h v
  obtain ⟨N, hN⟩ := hnil
  haveI := isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩

  have key : ∀ (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A) (w : G.omega),
      IsCan t ⟨_, hβ⟩ (G.rigOfOmega w) → G.lieUnivToLie (E.symm.dualMap h) w = h ⟨_, hβ⟩ := by
    intro β hβ w hw
    have e : E ⟨_, hβ⟩ = G.rigOfOmega w := isCan_unique R A p G t _ hA _ _ (hE _) hw
    change (E.symm.dualMap h) (G.rigOfOmega w) = _
    rw [LinearEquiv.dualMap_apply, ← e, LinearEquiv.symm_apply_apply]
  constructor
  · rintro ⟨hv, hh⟩
    obtain ⟨x', hx', -⟩ := t.existsUnique_lieCorr hv
    obtain ⟨ψ, hψ⟩ := T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t
    haveI : Module.Finite R G.omega := .equiv (LinearEquiv.ofBijective _
      (PDivGroup.omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl)).symm
    have hs := surjective_of_range_sup_smul_top_eq_top R _ _ ψ
      (T.primitive_hodge_to_omega_span_mod_maximal hHdR p R N hN A g hA hsm G t ψ hψ)
    suffices e : x' = G.lieUnivToLie (E.symm.dualMap h) by rw [← e]; exact hx'
    refine LinearMap.ext fun w => ?_
    obtain ⟨c, rfl⟩ := hs w
    obtain ⟨c, hF⟩ := c
    have hF' := hF
    change c.1 ∈ F1 _ at hF'
    rw [hodgeFiltration_eq_range] at hF'
    obtain ⟨c, hc⟩ := c
    obtain ⟨β, rfl⟩ := hF'
    obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hc
    have hw : ψ ⟨_, hF⟩ = w :=
      PDivGroup.rigOfOmega_injective_of_pow p R N hN G (isCan_unique R A p G t _ hA _ _ (hψ _) hw2)
    rw [key β hc _ (hψ ⟨_, hF⟩), hw, lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 x' v hx', hh β hc]
  · intro hx
    refine ⟨hx.1, fun β hβ => ?_⟩
    obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hβ
    rw [← key β hβ w hw2]
    exact lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 _ v hx

end GlobalTheory.PtExt
