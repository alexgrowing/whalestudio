import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodParameterFirstSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.StartCusp

open Formalism.IndefR.Mult Matrix Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

variable {D : D7}

theorem hasTypeAll_const_mul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {Lie Gs : Set (Mx n)} {f : Mx n → ℂ} (c : ℂ) (h : HasTypeAll Lie Gs σ f) :
    HasTypeAll Lie Gs σ fun g => c * f g := by
  obtain ⟨v, h1, ℓ, hℓ, ⟨S, C, hS, h2, h3, B, hB, hc⟩, h4⟩ := hasTypeAll_iff.1 h
  refine hasTypeAll_iff.2 ⟨v, h1, fun i => c • ℓ i, fun i => GlobalTheory.MultMem.sobCont_smul c (hℓ i),
    ⟨S, fun i => ‖c‖ * C i, hS, fun i w hw => ?_, fun S' hS' => ?_, B, hB, hc⟩, fun g hg => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 i w hw) (norm_nonneg c)
  · simpa only [mul_assoc] using (h3 S' hS').mul_left ‖c‖
  · simpa only [LinearMap.smul_apply, smul_eq_mul] using (h4 g hg).mul_left c

def TypedBy (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  ∀ x, HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹))
    fun g => φ (x * atTau θ V τ g)

theorem isTypeAt_of_typedBy (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {φ : GA D V → ℂ} (h : TypedBy θ M τ φ) : IsTypeAt θ V τ (S τ) φ :=
  ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, M.ds τ, M.fr_unit τ, M.fr_gram τ, fun x => hasTypeAll_iff.1 (h x)⟩

theorem typedBy_value (θ : InfFam D) (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {Sp : D.what₂.Tau → SPar}
    (M : DSModel V Sp) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec)
    (τ : D.what₂.Tau) : TypedBy θ M τ (T v) := by
  have hD := M.ds τ
  haveI : CompleteSpace (M.H τ) := hD.1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hHC hD
  intro x
  obtain ⟨ℓ, hℓ, hℓv⟩ := hT.cont τ v x
  have hu : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v τ : M.H τ) :=
    GlobalTheory.SmVecModel.smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) ((GlobalTheory.SmVecModel.mem_sm_iff M τ _).1 (v τ).2)
  refine GlobalTheory.CuspValueType.hasTypeAll_single hσ (M.fr_unit τ) (M.fr_gram τ) hu hℓ fun g hg => ?_
  have h1 := hT.equiv τ g hg v ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩ rfl
  have h2 := hℓv ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩
  show ℓ (M.rep τ g (v τ)) = _
  rw [h2, h1]
  rfl

theorem star_lift_isTypeAt (θ : InfFam D) (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) (z : SmT M)
    (τ : D.what₂.Tau) : IsTypeAt θ V τ (dualPar (S τ)) fun g => star (PiTensorProduct.lift T z g) := by
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M
  obtain ⟨hsm, hmult⟩ := GlobalTheory.ConjMult.conj_mult θ M M' c hc
  obtain ⟨T', hT'm, hT'⟩ := hmult J χ T hT
  have hT'' := (GlobalTheory.MultMem.mem_mult_iff D θ V _ M' J _ T').1 hT'm
  refine isTypeAt_of_typedBy θ M' τ ?_
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    let f' : M'.Vec := fun ρ => ⟨(c ρ).symm (f ρ), (hsm ρ _).2 (by simp)⟩
    have e : (fun g => star (PiTensorProduct.lift T (r • PiTensorProduct.tprod ℂ f) g)) = fun g => star r * T' f' g := by
      funext g
      rw [hT' f' f (fun ρ => by simp [f']) g, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, star_mul']
    rw [e]
    intro x
    exact hasTypeAll_const_mul (star r) (typedBy_value θ hHC M' hT'' f' τ x)
  | add a b ha hb =>
    intro x
    have e : (fun g => star (PiTensorProduct.lift T (a + b) (x * atTau θ V τ g))) =
        fun g => star (PiTensorProduct.lift T a (x * atTau θ V τ g)) + star (PiTensorProduct.lift T b (x * atTau θ V τ g)) := by
      funext g
      rw [map_add, Pi.add_apply, star_add]
    rw [e]
    exact (ha x).add (hb x)

end GlobalTheory.StartCusp

namespace GlobalTheory.StartCusp

open Formalism.IndefR.Mult

variable {D : D7}

theorem isCuspFun_lift {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (z : SmT M) : IsCuspFun V (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)
  | add a b ha hb =>
    rw [map_add]
    exact GlobalTheory.MultMem.isCuspFun_add (GlobalTheory.EndCusp.isAutFunSm_lift hT a).toIsAutFun
      (GlobalTheory.EndCusp.isAutFunSm_lift hT b).toIsAutFun ha hb

set_option maxHeartbeats 1000000 in

theorem lift_isCuspListed : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), IsCuspListed (G := ch.G) ch.W.θ (.grid 0 0) (ch.cv.lift t y) := by
  intro hP _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  intro t y
  have hθ : ch.W.θ = R.θ := hch.toIsBase.weil.θ
  have hT := GlobalTheory.ProjectedLift.thDn_mem R t y
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D R.θ _ _ (R.MY 0) _ _ _).1 hT
  have hu : ch.cv.lift t y = PiTensorProduct.lift (PiTensorProduct.lift.symm (R.thDn t y)) ch.cv.w := by
    rw [LinearEquiv.apply_symm_apply, ch.cv.thDn_w hS.core.chain]
  rw [hθ, hu]
  refine ⟨GlobalTheory.EndCusp.isAutFunSm_lift hT' _, isCuspFun_lift hT' _, fun τ => ?_⟩
  have h := star_lift_isTypeAt R.θ hP.harishChandraModules (R.MY 0) hT ch.cv.w τ
  rw [show Node.par D ch.sc.cGap (.grid 0 0) τ = (Ptw D).Dpar 0 τ from parV_zero D _ (Nat.zero_le _) τ]
  simp only [parB, dualPar_dualPar, Nat.zero_min] at h
  exact h

end GlobalTheory.StartCusp
