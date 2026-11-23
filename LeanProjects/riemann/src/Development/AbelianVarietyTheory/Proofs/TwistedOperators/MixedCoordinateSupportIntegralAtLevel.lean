import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateTsumLeOfThetaLevelMultiple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntegralOfMemIntAE
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSelfDualLatticeAtPlaceIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.MixSupport

open GlobalTheory.CondBound

theorem annih_den (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (U : AddSubgroup (AE D))
    (hU : IsOpen (U : Set (AE D))) : ∃ N : ℕ, 0 < N ∧ ∀ x : AE D,
      (∀ a ∈ U, infPart D a = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (x * a)) = 1) → N • finPart D x ∈ intAE D := by
  have hΛ := GlobalTheory.PlaceModel.isSelfDualC_latFrame (line D)
  obtain ⟨M, hM, hden⟩ := den_latL D
  obtain ⟨K0, hK0c, mem0⟩ := exists_compact_fin D M hM
  have memL : ∀ u ∈ latL D, u (o D) (o D) ∈ K0 := fun u hu => mem0 _ (infPart_latL D hu) (hden u hu)
  let c0 : AE D := incA D D.host.xi0 * incA D ((line D).gram⁻¹ (o D) (o D)) * incA D ((line D).gram (o D) (o D))
  obtain ⟨n, hn⟩ := exists_small D _ (isCompact_mul_conj D c0 hK0c) U hU
  let r : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F))
  refine ⟨M * n.factorial, Nat.mul_pos hM (Nat.factorial_pos n), fun x hx => ?_⟩
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
  have h := hden u huL
  have e : finPart D (u (o D) (o D)) = n.factorial • finPart D x := by
    show finPart D (x * r) = _
    rw [RingHom.map_mul, finPart_r, map_natCast, map_natCast, nsmul_eq_mul, mul_comm]
  rw [e, ← mul_nsmul'] at h
  exact h

theorem mul_eq_zero_of_parts {D : D7} (z c : AE D) (hz : finPart D z = 0) (hc : infPart D c = 0) : z * c = 0 := by
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext ?_ ?_
  · rw [(he _).1, (he _).1]
    show infPart D (z * c) = infPart D 0
    rw [map_mul, hc, mul_zero, map_zero]
  · rw [(he _).2, (he _).2]
    show finPart D (z * c) = finPart D 0
    rw [map_mul, hz, zero_mul, map_zero]

theorem mat_den {D : D7} {m : ℕ} (A : Matrix (Fin m) (Fin m) D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i j, IsIntegral ℤ ((d : D.host.E) * A i j) := by
  choose n hn hint using fun p : Fin m × Fin m => GlobalTheory.IwaPlace.SDBound.exists_nat_mul_isIntegral (D := D) (A p.1 p.2)
  refine ⟨∏ p, n p, Finset.prod_pos fun p _ => hn p, fun i j => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_comm ((n (i, j) : ℕ) : D.host.E), mul_assoc]
  have hc : IsIntegral ℤ (((∏ p ∈ Finset.univ.erase (i, j), n p : ℕ) : D.host.E)) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := ((∏ p ∈ Finset.univ.erase (i, j), n p : ℕ) : ℤ)))
  exact hc.mul (hint (i, j))

set_option maxHeartbeats 2000000 in
open GlobalTheory.MixModel in

theorem mixS_support_integral : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      ∀ (ξ : Matrix (Fin X.rank) (Fin r) D.host.E) (x : Mx D X.rank r),
        x.map (finPart D) = (ξ.map (incA D) : Mx D X.rank r).map (finPart D) → d.mixS X ψ μ' 𝓕' Ψ x 0 ≠ 0 →
        ∀ i j, IsIntegral ℤ (((M * n : ℕ) : D.host.E) * ξ i j) := by
  intro D ψ hψ V X S₀ r d μ' 𝓕' hμ K₀ hK₀ _
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.MixSumBound.finite_points_in_nhds D X.rank V.rank K₀ hK₀
  let g : Fin X.rank → Fin r → (AE D →+ Mx D X.rank r) := fun i j =>
    { toFun := fun c => Matrix.single i j (cA D c)
      map_zero' := by simp
      map_add' := fun a b => by simp [Matrix.single_add] }
  have hg : ∀ i j, Continuous (g i j) := fun i j => by
    show Continuous fun c => Matrix.single i j (cA D c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.single_apply]
    split_ifs
    · exact GlobalTheory.AnnihBox.continuous_cA'
    · exact continuous_const
  have hf : ∀ i j, Continuous ((d.extY X).comp (g i j)) := fun i j => by
    show Continuous fun c => d.extY X (g i j c)
    simp only [HypDec.extY_apply]
    exact (hg i j).matrix_mul continuous_const
  have hg0 : ∀ i j c, infPart D c = 0 → (g i j c).map (infPart D) = 0 := fun i j c hc0 => by
    ext a b
    show infPart D (Matrix.single i j (cA D c) a b) = 0
    simp only [Matrix.single_apply]
    split_ifs
    · exact GlobalTheory.AnnihBox.infPart_cA' c hc0
    · exact map_zero _
  let U' : AddSubgroup (AE D) := ⨅ i, ⨅ j, U.comap ((d.extY X).comp (g i j))
  have hU'o : IsOpen (U' : Set (AE D)) := by
    have e : (U' : Set (AE D)) = ⋂ i, ⋂ j, ((d.extY X).comp (g i j)) ⁻¹' (U : Set (WO V X)) := by
      ext c; simp [U', AddSubgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hUo.preimage (hf i j)
  obtain ⟨N, hN, hNden⟩ := annih_den D ψ hψ U' hU'o
  obtain ⟨M₂, hM₂, hM₂i⟩ := mat_den (D := D) (D.host.xi0⁻¹ • X.gram⁻¹)
  refine ⟨M₂ * N, Nat.mul_pos hM₂ hN, fun n hn Ψ hΨ hfix ξ x hx hne i j => ?_⟩
  let v : GlobalTheory.Unf.VolM D X.rank r := ⟨μ', 𝓕', hμ⟩
  have hmix := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ V S₀ X r d v Ψ hΨ).2.1
  have hxr : (x - rat ξ).map (finPart D) = 0 := by
    rw [Matrix.map_sub _ (map_sub (finPart D))]
    exact sub_eq_zero.2 hx
  have key : ∀ k l, IsIntegral ℤ ((N : D.host.E) * ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l))) := by
    intro k l
    have hann : ∀ c ∈ U', infPart D c = 0 → ψ (Algebra.trace (AF D.host.F) (AE D)
        (incA D ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l)) * c)) = 1 := by
      intro c hc hc0
      have hcU : d.extY X (g k l c) ∈ U := AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hc k) l
      have hfin : (d.extY X (g k l c)).map (infPart D) = 0 := by
        rw [HypDec.extY_apply, Matrix.map_mul, hg0 k l c hc0, Matrix.zero_mul]
      have hfx := hfix _ (hU _ hcU hfin) hfin
      have h2 := congrFun (hmix x (n • g k l c)) 0
      rw [map_nsmul, hfx, Pi.smul_apply, smul_eq_mul] at h2
      have h3 : ψ (symplO V X (d.extX X x) (n • d.extY X (g k l c))) = 1 := by
        have hne' : d.mixS X ψ v.μ v.𝓕 Ψ x 0 ≠ 0 := hne
        exact mul_right_cancel₀ hne' (h2.symm.trans (one_mul _).symm)
      rw [← map_nsmul (d.extY X), ← map_nsmul (g k l), show g k l (n • c) = Matrix.single k l (cA D (n • c)) from rfl,
        GlobalTheory.AnnihBox.symplO_extX_extY_single] at h3
      rw [← h3]
      congr 2
      have hxc : (gA X * x) k l * c = incA D ((X.gram * ξ) k l) * c := by
        rw [← sub_eq_zero, ← sub_mul]
        refine mul_eq_zero_of_parts _ _ ?_ hc0
        have e1 : incA D ((X.gram * ξ) k l) = (gA X * rat ξ) k l := by
          rw [gA, ← rat_mul]; rfl
        rw [e1, ← Matrix.sub_apply, ← Matrix.mul_sub]
        exact congrFun (congrFun (map_mul_eq_zero_right (finPart D) (gA X) hxr) k) l
      calc incA D ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l)) * c
          = (n : AE D) * (incA D D.host.xi0 * (incA D ((X.gram * ξ) k l) * c)) := by
            simp only [map_mul, map_natCast]; ring
        _ = (n : AE D) * (incA D D.host.xi0 * ((gA X * x) k l * c)) := by rw [hxc]
        _ = incA D D.host.xi0 * (gA X * x) k l * (n • c) := by rw [nsmul_eq_mul]; ring
    have h := hNden _ hann
    have e : finPart D (incA D ((N : D.host.E) * ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l)))) =
        N • finPart D (incA D ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l))) := by
      rw [map_mul (incA D), map_mul (finPart D), map_natCast, map_natCast, nsmul_eq_mul]
    rw [← e] at h
    obtain ⟨y, hy⟩ := GlobalTheory.FinalJoin.CondTest.integral_of_mem_intAE h
    have e2 : ((N : D.host.E) * ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l))) = (y : D.host.E) := hy.symm
    rw [e2]
    convert NumberField.RingOfIntegers.isIntegral_coe y
  have hξ : ξ = X.gram⁻¹ * (X.gram * ξ) := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det X), Matrix.one_mul]
  have e : (((M₂ * N * n : ℕ)) : D.host.E) * ξ i j = ∑ k, ((M₂ : D.host.E) * (D.host.xi0⁻¹ • X.gram⁻¹) i k) *
      ((N : D.host.E) * ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k j))) := by
    conv_lhs => rw [hξ]
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
    simp only [Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  rw [e]
  exact IsIntegral.sum _ fun k _ => (hM₂i i k).mul (key k j)

end GlobalTheory.MixSupport
