import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntriesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTopStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoundedFunctionalThetaEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterAnnihilatorCompactBoxStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleSumWeightedBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf.DoubleSum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem enorm_integral_le {α β : Type} [MeasurableSpace α] {μ : Measure α} {𝓕 : Set α} (h : μ 𝓕 = 1) (u : α → ℂ)
    (hu : ∀ a, ‖u a‖ = 1) (p : α → β) (f : β → ℂ) : ‖∫ a in 𝓕, u a * f (p a) ∂μ‖ₑ ≤ ⨆ w, ‖f w‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine (lintegral_mono (g := fun _ => ⨆ w, ‖f w‖ₑ) fun a => ?_).trans ?_
  · beta_reduce
    rw [enorm_mul, ← ofReal_norm (u a), hu, ENNReal.ofReal_one, one_mul]
    exact le_iSup (fun w => ‖f w‖ₑ) _
  · rw [setLIntegral_const, h, mul_one]

theorem rearrange (C₁ C₂ : ℝ≥0) (p s M : ℝ≥0∞) (hM : M ≠ ⊤) :
    p * ((C₁ + C₂) * s) * M = ((C₁ + C₂) * M.toNNReal : ℝ≥0) * p * s := by
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hM, ENNReal.coe_add]
  ring

section Source

variable {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)

theorem enorm_mixS_le (hψ : IsStdChar D ψ (-1)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) (w : WO S₀ T) :
    ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ ≤ ⨆ w, ‖f w‖ₑ := by
  simp only [HypDec.mixS, HypDec.integrandS_eq]
  exact enorm_integral_le v.covol.2.2 _ (fun _ => hψ.1.2.1 _) _ f

theorem mixS_add (hψ : IsStdChar D ψ (-1)) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (x : Mx D T.rank ρ) : d.mixS T ψ v.μ v.𝓕 (f + g) x = d.mixS T ψ v.μ v.𝓕 f x + d.mixS T ψ v.μ v.𝓕 g x := by
  funext w
  have h1 := d.integrableOn_mixS hψ.1.1 v.covol hf x w
  have h2 := d.integrableOn_mixS hψ.1.1 v.covol hg x w
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
  exact integral_add h1 h2

theorem mixS_smul (c : ℂ) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    d.mixS T ψ v.μ v.𝓕 (c • f) x = c • d.mixS T ψ v.μ v.𝓕 f x := by
  funext w
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

variable (T) in

def dualPt (ρ : ℕ) : Mx D ρ T.rank →+ Mx D T.rank ρ where
  toFun b := adj (incA D D.host.xi0⁻¹ • (b ⬝ giA T))
  map_zero' := by rw [Matrix.zero_mul, smul_zero, adj_zero]
  map_add' _ _ := by rw [Matrix.add_mul, smul_add, adj_add]

theorem continuous_dualPt : Continuous (dualPt T ρ) := by
  have h : Continuous fun b : Mx D ρ T.rank => (b ⬝ giA T : Mx D ρ T.rank) := continuous_id.matrix_mul continuous_const
  exact continuous_adj.comp (f := fun b : Mx D ρ T.rank => incA D D.host.xi0⁻¹ • (b ⬝ giA T : Mx D ρ T.rank))
    (continuous_matrix fun i j => continuous_const.mul (h.matrix_elem i j))

theorem infPart_cA {a : AE D} (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  have e : ∀ z : AE D, infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]
  rw [e, h, map_zero]

theorem dualPt_fin {b : Mx D ρ T.rank} (hb : b.map (infPart D) = 0) : (dualPt T ρ b).map (infPart D) = 0 := by
  have h : (b ⬝ giA T).map (infPart D) = 0 := by rw [Matrix.map_mul, hb, Matrix.zero_mul]
  funext i j
  refine infPart_cA (a := incA D D.host.xi0⁻¹ * (b ⬝ giA T) j i) ?_
  rw [map_mul, show infPart D ((b ⬝ giA T) j i) = 0 from congrFun (congrFun h j) i, mul_zero]

theorem symplO_dualPt (x : Mx D T.rank ρ) (b : Mx D ρ T.rank) :
    symplO S T (d.extX T x) (d.extY T (dualPt T ρ b)) = Algebra.trace (AF D.host.F) (AE D) (x ⬝ b).trace := by
  have h := d.hO_ext T x 0 0 (dualPt T ρ b) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS]
  congr 1
  rw [show dualPt T ρ b = adj (incA D D.host.xi0⁻¹ • (b ⬝ giA T)) from rfl, adj_adj, Matrix.smul_mul, trace_smul, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, Matrix.mul_assoc, giA_gA_cancel, trace_mul_comm]

end Source

section Target

variable {S T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (v : VolM D σ S.rank)

theorem enorm_mixT_le (hψ : IsStdChar D ψ (-1)) (f : WO S T → ℂ) (y : Mx D S.rank σ) (w : WO S T₀) :
    ‖d.mixT S ψ v.μ v.𝓕 f y w‖ₑ ≤ ⨆ w, ‖f w‖ₑ := by
  simp only [HypDec.mixT, HypDec.integrandT_eq]
  exact enorm_integral_le v.covol.2.2 _ (fun _ => hψ.1.2.1 _) _ f

theorem mixT_add (hψ : IsStdChar D ψ (-1)) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (y : Mx D S.rank σ) : d.mixT S ψ v.μ v.𝓕 (f + g) y = d.mixT S ψ v.μ v.𝓕 f y + d.mixT S ψ v.μ v.𝓕 g y := by
  funext w
  have h1 := d.integrableOn_mixT hψ.1.1 v.covol hf y w
  have h2 := d.integrableOn_mixT hψ.1.1 v.covol hg y w
  simp only [HypDec.mixT, HypDec.integrandT_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
  exact integral_add h1 h2

theorem mixT_smul (c : ℂ) (f : WO S T → ℂ) (y : Mx D S.rank σ) :
    d.mixT S ψ v.μ v.𝓕 (c • f) y = c • d.mixT S ψ v.μ v.𝓕 f y := by
  funext w
  simp only [HypDec.mixT, HypDec.integrandT_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

end Target

section Double

variable {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec T T₀ σ) (v : VolM D T.rank ρ)
  (v' : VolM D σ S₀.rank)

variable (ψ) in

def val (x : Mx D T.rank ρ) (y : Mx D S₀.rank σ) (f : WO S T → ℂ) : ℂ :=
  d'.mixT S₀ ψ v'.μ v'.𝓕 (d.mixS T ψ v.μ v.𝓕 f x) y 0

theorem val_extY (hψ : IsStdChar D ψ (-1)) (x : Mx D T.rank ρ) (y : Mx D S₀.rank σ) (b : Mx D ρ T.rank)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    val ψ d d' v v' x y (heisO ψ S T (d.extY T (dualPt T ρ b)) f) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (x ⬝ b).trace) * val ψ d d' v v' x y f := by
  rw [val, (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf).2.1, mixT_smul, symplO_dualPt]
  rfl

theorem val_incX (hψ : IsStdChar D ψ (-1)) (x : Mx D T.rank ρ) (y : Mx D S₀.rank σ) (ξ : Mx D σ S₀.rank)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    val ψ d d' v v' x y (heisO ψ S T (d.ext0 T (d'.incX S₀ ξ)) f) =
      ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * val ψ d d' v v' x y f := by
  rw [val, (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf).2.2.1,
    (GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ S₀ T T₀ σ d' v'.μ v'.𝓕 v'.covol _
      ((GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 S S₀ T ρ d v.μ v.𝓕 v.covol f hf x)).1,
    GlobalTheory.OrientedHeis.symplO_skew, d'.symplO_incX_incAdj]
  rfl

theorem ext_zero_incX_finite_part_zero {ξ : Mx D σ S₀.rank} (h : ξ.map (infPart D) = 0) :
    (d.ext0 T (d'.incX S₀ ξ)).map (infPart D) = 0 := by
  have h1 : (d'.incX S₀ ξ).map (infPart D) = 0 := by rw [HypDec.incX_apply, Matrix.map_mul, h, Matrix.mul_zero]
  rw [HypDec.matrixExtendByZero_apply, Matrix.map_mul, h1, Matrix.zero_mul]

theorem trace_nsmul {a b : ℕ} (n : ℕ) (x : Mx D a b) (z : Mx D b a) : (x ⬝ (n • z)).trace = ((n • x) ⬝ z).trace := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, Matrix.mul_add, Matrix.add_mul, trace_add, trace_add, ih]

end Double

theorem absSum₂_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (ρ σ : ℕ), ∃ k : ℕ, ∀ (S₀ T₀ : HSp D) (d : HypDec S S₀ ρ) (d' : HypDec T T₀ σ) (v : VolM D T.rank ρ) (v' : VolM D σ S₀.rank), ∀ K₀ ∈ nhds (0 : WO S T), ∃ C : ℝ≥0, ∀ n : ℕ, 0 < n → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → GlobalTheory.IndefiniteRowSideFullHecke.WordMatrixSeminorms.absSum₂ ψ d d' v.μ v.𝓕 v'.μ v'.𝓕 f ≤ C * (n : ℝ≥0∞) ^ k * supSob ψ θ k f := by
  intro D ψ hψ θ hθ S T ρ σ
  choose N hN using GlobalTheory.T.tsum_adelicMatrixSchwartzMajorant_rational_ne_top D θ hθ
  refine ⟨N T.rank ρ + N (S.rank - 2 * ρ) σ, fun S₀ T₀ d d' v v' K₀ hK₀ => ?_⟩
  have hr : S.rank - 2 * ρ = S₀.rank := by have := d.rank_add; omega
  rw [hr]
  set k := N T.rank ρ + N S₀.rank σ with hk
  have hmv := fun f hf => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 S S₀ T ρ d v.μ v.𝓕 v.covol f hf
  have c1 : Continuous fun b => d.extY T (dualPt T ρ b) := continuous_dualPt.matrix_mul continuous_const
  have c2 : Continuous fun ξ => d.ext0 T (d'.incX S₀ ξ) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨K, hK, hbox⟩ := GlobalTheory.T.character_annihilator_compact_box D ψ hψ ρ T.rank _
    (c1.continuousAt.preimage_mem_nhds (by rwa [map_zero, map_zero]))
  obtain ⟨K', hK', hbox'⟩ := GlobalTheory.T.character_annihilator_compact_box D ψ hψ σ S₀.rank _
    (c2.continuousAt.preimage_mem_nhds (by rwa [map_zero, map_zero]))
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.mixedCoordinate_decay_realEntries D ψ hψ θ hθ S S₀ T ρ d v k
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.bounded_functional_theta_estimate D ψ hψ θ hθ S T σ S₀.rank d'.jX d.p0 k
  have hM := ENNReal.mul_ne_top (hN T.rank ρ K hK) (hN S₀.rank σ K' hK')
  refine ⟨(C₁ + C₂) * ENNReal.toNNReal ((∑' x : ratMx D T.rank ρ, ENNReal.ofReal (maj θ K (N T.rank ρ) x)) *
    ∑' y : ratMx D S₀.rank σ, ENNReal.ofReal (maj θ K' (N S₀.rank σ) y)), fun n hn f hf hlev => ?_⟩
  refine (GlobalTheory.T.double_sum_weighted_bound D θ _ _ _ _ K K' (N T.rank ρ) (N S₀.rank σ) n hn ((C₁ + C₂) * supSob ψ θ k f)
    (fun x y => ‖val ψ d d' v v' x y f‖ₑ) (fun x y hne => ⟨hbox _ fun b hb hfin => ?_, hbox' _ fun ξ hξ hfin => ?_⟩)
    (fun x y => ?_) (fun x y => ?_)).trans (le_of_eq ?_)
  · have h := val_extY d d' v v' hψ x y (n • b) hf
    rw [map_nsmul, map_nsmul, hlev (d.extY T (dualPt T ρ b)) hb
      (by rw [HypDec.extY_apply, Matrix.map_mul, dualPt_fin hfin, Matrix.zero_mul]),
      trace_nsmul] at h
    exact (mul_eq_right₀ (enorm_ne_zero.1 hne)).1 h.symm
  · have h := val_incX d d' v v' hψ x y (n • ξ) hf
    rw [map_nsmul, map_nsmul, hlev (d.ext0 T (d'.incX S₀ ξ)) hξ (ext_zero_incX_finite_part_zero d d' hfin),
      trace_nsmul, AddChar.map_neg_eq_inv] at h
    exact inv_eq_one.1 ((mul_eq_right₀ (enorm_ne_zero.1 hne)).1 h.symm)
  · refine (mul_le_mul_left (enorm_mixT_le d' v' hψ _ _ _) _).trans ?_
    rw [ENNReal.iSup_mul]
    exact iSup_le fun w => (hC₁ f hf x w).trans (mul_le_mul_left le_self_add _)
  · refine (hC₂ (val ψ d d' v v' x y) y (fun f g hf hg => ?_) (fun c f _ => ?_) (fun f _ => ?_)
      (fun ξ f hf => val_incX d d' v v' hψ x y ξ hf) f hf).trans (mul_le_mul_left le_add_self _)
    · rw [val, mixS_add d v hψ hf hg, mixT_add d' v' hψ (hmv f hf x) (hmv g hg x)]
      rfl
    · rw [val, mixS_smul, mixT_smul]
      rfl
    · exact (enorm_mixT_le d' v' hψ _ _ _).trans (iSup_le fun w => enorm_mixS_le d v hψ f x w)
  · exact rearrange _ _ _ _ _ hM

end GlobalTheory.Unf.DoubleSum

end
