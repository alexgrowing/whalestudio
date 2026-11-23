import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroUniformisedModelDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsIntegralUnitMemberUniformisedTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.CmpUnif

theorem thList_smul {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {ρ : LB.Gen (L.pull (eSec G))} (hL : L.IsLB) {m : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x}
    {a : K} (hθ : SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ) {N : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {c : Fin N → K} (h : ThList G L ρ m x θ pt c) :
    ThList G L ρ m x θ' pt (fun b => a * c b) := by
  have hfn : ∀ u v : K, GlobalTheory.ZH.fn (u * v) = GlobalTheory.ZH.fn u * GlobalTheory.ZH.fn v := fun u v => map_mul _ u v
  refine ⟨h.1, fun b => ?_, h.2.2⟩
  rw [hfn]
  exact ThG.smul hL hθ (h.2.1 b)

theorem cmp_unif : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (_ : Unif (IsLocalRing.maximalIdeal W) D A G) (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing W →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : W) → Odd m' → 3 ≤ m' → IsUnit (m' : W) → (letI := A.isAb.comm; HasTh₂ A.A A.L ρ m m' (spMap io) d d') → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d' b / a) := by
  intro W _ _ _ _ hW D A G _ _ hG U ρ hρ K _ _ io m m' N N' d d' hm hm3 hmu hm' hm3' hmu' hd
  letI := A.isAb.comm
  obtain ⟨-, -, w, hp, -, hw, -⟩ := GlobalTheory.Ex.GenericFibre.exists_isoData W _ D A G U.toUnifPre
  have h₁ := (GlobalTheory.UMin.ThMove.hasTh₂_move _ G U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen _ A.A A.L ρ (jK W) _ A.isLB hρ hp
    ⟨w, hw⟩ m m' N N' K (spMap io) d d').1 hd
  set i : W →+* K := io.comp (algebraMap W (FractionRing W)) with hi
  have hinj : Function.Injective i := io.injective.comp (IsFractionRing.injective W (FractionRing W))
  have ex : spMap io ≫ jK W = spMap i ≫ 𝟙 (Sp W) := by
    rw [Category.comp_id, hi, ← Spec.map_comp]; rfl
  rw [ex] at h₁
  obtain ⟨θ, pt, pt', hθ, hl, hl'⟩ := h₁
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_section_nonzero_uniformised_model_dvr W hW D A G hG U
  obtain ⟨r, hr⟩ := (isGenSec_iff θ).1 hθ (SecM.ofSec G (SecAt.pull G U.LG.L σ i))
  obtain ⟨u, rfl⟩ := (fnR (spMap i ≫ 𝟙 (Sp W))).surjective r
  have hP := GlobalTheory.T.theta_constants_integral_unit_member_uniformised_trait W hW D A G hG U σ hσ m N hm hm3 hmu K i pt _ hinj (thList_smul U.LG.isLB (a := u) hr hl)
  have hP' := GlobalTheory.T.theta_constants_integral_unit_member_uniformised_trait W hW D A G hG U σ hσ m' N' hm' hm3' hmu' K i pt' _ hinj
    (thList_smul U.LG.isLB (a := u) hr hl')
  have hu : u ≠ 0 := by
    obtain ⟨-, b, hb, -⟩ := hP
    exact left_ne_zero_of_mul hb
  refine ⟨u⁻¹, inv_ne_zero hu, ?_, ?_⟩
  · simpa only [div_inv_eq_mul, _root_.mul_comm] using hP
  · simpa only [div_inv_eq_mul, _root_.mul_comm] using hP'

end GlobalTheory.SiegTh.CmpUnif
end
