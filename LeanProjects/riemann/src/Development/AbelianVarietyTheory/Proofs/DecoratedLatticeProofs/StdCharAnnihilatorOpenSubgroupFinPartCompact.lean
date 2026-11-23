import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteCosetsAdelicUnitaryBoundedDenominato
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousConjA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.CondBound

open Filter Topology

variable (D : D7)

abbrev line : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

def o : Fin (line D).rank := ⟨0, Nat.one_pos⟩

theorem sum_line (f : Fin (line D).rank → AE D) : ∑ i, f i = f (o D) := Fin.sum_univ_one f

theorem hO_line (x y : WO (line D) (line D)) :
    hO (line D) (line D) x y = incA D ((line D).gram⁻¹ (o D) (o D)) * cA D (y (o D) (o D)) *
      incA D ((line D).gram (o D) (o D)) * x (o D) (o D) := by
  unfold hO
  simp only [sum_line]

abbrev latL : AddSubgroup (WO (line D) (line D)) :=
  latO (line D) (line D) (GlobalTheory.PlaceModel.latFrame (line D) : Set (Fin (line D).rank → D.host.E))
    (GlobalTheory.PlaceModel.latFrame (line D) : Set (Fin (line D).rank → D.host.E)) fun _ => True

theorem infPart_latL {u : WO (line D) (line D)} (hu : u ∈ latL D) : infPart D (u (o D) (o D)) = 0 := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hw
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    exact TensorProduct.zero_tmul _ _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_apply, RingHom.map_add, hx, hy, add_zero]
  | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem infPart_r (a : Af D.host.F) : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a)) = 0 := by
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem finPart_r (N : ℕ) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (N : Af D.host.F))) = finPart D (incA D (N : D.host.E)) := by
  rw [map_natCast, map_natCast]
  show (N : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [← map_natCast (algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)) N]
  rfl

theorem den_latL : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latL D, M • finPart D (u (o D) (o D)) ∈ intAE D := by
  have hΛ := GlobalTheory.PlaceModel.isSelfDualC_latFrame (line D)
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := line D) (T := line D) hΛ.1.fg hΛ.1.fg
  refine ⟨M, hM, fun u hu => ?_⟩
  have h2 : toEAf D ((M : AE D) * u (o D) (o D)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [RingHom.map_mul, map_natCast]; exact hden u hu (o D) (o D)
  have h3 := GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h2
  rw [RingHom.map_mul, map_natCast] at h3
  rw [nsmul_eq_mul]
  exact h3

theorem exists_compact_fin (M : ℕ) (hM : 0 < M) : ∃ K0 : Set (AE D), IsCompact K0 ∧
    ∀ z : AE D, infPart D z = 0 → M • finPart D z ∈ intAE D → z ∈ K0 := by
  obtain ⟨C, hC, hCd⟩ := GlobalTheory.SmoothForms.Cover.exists_compact_denom D M hM
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm '' ({0} ×ˢ C), (isCompact_singleton.prod hC).image hc, fun z h1 h2 => ?_⟩
  have e1 : (e z).1 = 0 := by have := (he z).1; exact this.trans h1
  have e2 : M • (e z).2 ∈ intAE D := by have := (he z).2; rw [this]; exact h2
  exact ⟨e z, Set.mk_mem_prod (Set.mem_singleton_iff.2 e1) (hCd _ e2), e.symm_apply_apply z⟩

theorem tendsto_r : Tendsto (fun n : ℕ => algebraMap (AF D.host.F) (AE D)
    (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F))) atTop (𝓝 0) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h : Tendsto (fun n : ℕ => pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) atTop (𝓝 (0 : AF D.host.F)) :=
    (tendsto_const_nhds (x := (0 : Ainf D.host.F))).prodMk_nhds
      (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele D.host.F)
  have hcont : Continuous (algebraMap (AF D.host.F) (AE D)) := by
    have hfun : (algebraMap (AF D.host.F) (AE D) : AF D.host.F → AE D) = fun t => t • (1 : AE D) := by
      funext t; exact Algebra.algebraMap_eq_smul_one t
    haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
    rw [hfun]; exact continuous_id.smul (continuous_const (y := (1 : AE D)))
  have := (hcont.tendsto 0).comp h
  rwa [map_zero] at this

theorem exists_small (C' : Set (AE D)) (hC' : IsCompact C') (U : AddSubgroup (AE D)) (hU : IsOpen (U : Set (AE D))) :
    ∃ n : ℕ, ∀ z ∈ C', algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * z ∈ U := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hev : ∀ᶠ t in 𝓝 (0 : AE D), ∀ z ∈ C', t * z ∈ U := by
    refine hC'.eventually_forall_of_forall_eventually fun z _ => ?_
    have h0 : ((0 : AE D), z).1 * ((0 : AE D), z).2 ∈ U := by rw [zero_mul]; exact U.zero_mem
    exact (continuous_mul.continuousAt (x := ((0 : AE D), z))).preimage_mem_nhds (hU.mem_nhds h0)
  exact ((tendsto_r D).eventually hev).exists

theorem isCompact_mul (c : AE D) {K : Set (AE D)} (hK : IsCompact K) : IsCompact ((fun z => c * z) '' K) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact hK.image (continuous_const.mul continuous_id)

theorem isCompact_mul_conj (c : AE D) {K : Set (AE D)} (hK : IsCompact K) :
    IsCompact ((fun z => c * cA D z) '' K) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact hK.image (continuous_const.mul (GlobalTheory.ConjAutProps.continuous_conjA D))

set_option maxHeartbeats 1000000 in

theorem annihilator_finPart_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (AE D),
    IsOpen (U : Set (AE D)) → ∃ K : Set (AE D), IsCompact K ∧ ∀ x : AE D,
      (∀ a ∈ U, infPart D a = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (x * a)) = 1) →
        ∃ k ∈ K, finPart D (x - k) = 0 := by
  intro D ψ hψ U hU
  have hΛ := GlobalTheory.PlaceModel.isSelfDualC_latFrame (line D)
  obtain ⟨M, hM, hden⟩ := den_latL D
  obtain ⟨K0, hK0c, mem0⟩ := exists_compact_fin D M hM
  have memL : ∀ u ∈ latL D, u (o D) (o D) ∈ K0 := fun u hu => mem0 _ (infPart_latL D hu) (hden u hu)
  let c0 : AE D := incA D D.host.xi0 * incA D ((line D).gram⁻¹ (o D) (o D)) * incA D ((line D).gram (o D) (o D))
  obtain ⟨n, hn⟩ := exists_small D _ (isCompact_mul_conj D c0 hK0c) U hU
  let r : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F))
  have hN : ((n.factorial : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos n).ne'
  refine ⟨(fun z => incA D ((n.factorial : ℕ) : D.host.E)⁻¹ * z) '' K0, isCompact_mul D _ hK0c, ?_⟩
  intro x hx
  let u : WO (line D) (line D) := Matrix.of fun _ _ => x * r
  have hu0 : u.map (infPart D) = 0 := by
    ext i j
    show infPart D (x * r) = 0
    rw [RingHom.map_mul, infPart_r, mul_zero]
  have huL : u ∈ latL D := by
    refine ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ (line D) (line D) _ _ hψ hΛ hΛ).1 u hu0).2 fun u' hu' => ?_
    have ha : r * (c0 * cA D (u' (o D) (o D))) ∈ U := hn _ ⟨_, memL u' hu', rfl⟩
    have hai : infPart D (r * (c0 * cA D (u' (o D) (o D)))) = 0 := by
      rw [RingHom.map_mul, infPart_r, zero_mul]
    have h := hx _ ha hai
    rw [symplO, hO_line]
    convert h using 3
    show _ = x * _
    simp only [c0, u, Matrix.of_apply]
    ring
  refine ⟨_, ⟨_, memL u huL, rfl⟩, ?_⟩
  show finPart D (x - incA D ((n.factorial : ℕ) : D.host.E)⁻¹ * (x * r)) = 0
  have h1 : finPart D (incA D ((n.factorial : ℕ) : D.host.E)⁻¹) * finPart D r = 1 := by
    rw [finPart_r, ← RingHom.map_mul, ← RingHom.map_mul, inv_mul_cancel₀ hN, map_one, map_one]
  rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, mul_left_comm, h1, mul_one, sub_self]

end GlobalTheory.CondBound
