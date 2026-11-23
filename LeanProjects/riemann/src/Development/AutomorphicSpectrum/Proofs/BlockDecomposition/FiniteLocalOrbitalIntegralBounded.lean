import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumQuadraticCharacterBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumFiniteAverageBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelOpenCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelsNeighbourhoodBasisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseCocycleBimultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseContinuousUnitaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBiadditiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDualDenominatorBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalCharacterKernelScalingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingOnRationalTupleFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalTupleInLatticeLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisjointTranslatesVolumeBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaConjInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaPosIndexStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec

set_option maxHeartbeats 1000000 in
theorem finite_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
    ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    ∃ (C : ℝ) (t : F), t ≠ 0 ∧ ∀ c : hermE σ n,
      ‖starLoc (Af F) σ J (psiFin F ψ) μ Q (hermIn (Af F) σ n c)‖ ≤
        C * (delta (t • c).1 : ℝ) ^ (-((M : ℝ) / 2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ hψ μ hμ Q hQ
  classical
  obtain ⟨hA1, hA2, hA3, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := hA1
  haveI : SecondCountableTopology (Af F) := hA2
  haveI : T2Space (Af F) := hA3
  obtain ⟨hT1, hT2, hT3, hT4, -, -, -, hT8, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := hT1
  haveI : SecondCountableTopology (Af F ⊗[F] E) := hT3
  haveI : T2Space (Af F ⊗[F] E) := hT4
  haveI : BorelSpace (Fin n → Fin M → Af F ⊗[F] E) := hT8 n M
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (Module.Basis (Fin d) F E) :=
    ⟨_, ⟨Module.finBasis F E⟩⟩
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.T.lattice_levels_neighbourhood_basis F E σ hCM d b n M _ (invariant_mem_nhds hQ.1 hQ.2)
  obtain ⟨hLo, hLc⟩ := GlobalTheory.T.lattice_level_open_compact F E σ hCM d b n M N hN
  set L := latN b n M N with hL
  obtain ⟨s, hs⟩ := eq_sum_cosets hQ.2 L hLo (fun x l hl => hNU hl x)
  obtain ⟨D, hD, hDc⟩ := GlobalTheory.T.trace_dual_denominator_bounded F
  obtain ⟨t₁, ht₁, htest⟩ := GlobalTheory.T.rational_character_kernel_scaling F E σ hCM d b ψ hψ N hN D hD hDc
  obtain ⟨s₂, hs₂, hrat⟩ := GlobalTheory.T.rational_tuple_in_lattice_level F E d b M J n N hN
  have hs₂F : ((s₂ : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hs₂.ne'
  refine ⟨(∑ a ∈ s, ‖Q a‖) * (μ (L : Set _)).toReal, t₁ * (s₂ : F), mul_ne_zero ht₁ hs₂F, fun c => ?_⟩
  set t : F := t₁ * (s₂ : F) with ht
  set bc := hermIn (Af F) σ n c with hbc
  obtain ⟨hp1, hp2, hp3⟩ := GlobalTheory.T.phase_continuous_unitary F E σ hCM M J n ψ hψ bc
  obtain ⟨hq1, hq2⟩ := GlobalTheory.T.pairing_biadditive F E σ M J n ψ bc
  set q := phaseB σ J (psiFin F ψ) bc with hq
  set B := pairB σ J (psiFin F ψ) bc with hB
  set S : Set (Fin n → Fin M → Af F ⊗[F] E) := {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1} with hS
  have hLfin : μ (L : Set _) ≠ ⊤ := hLc.measure_lt_top.ne
  have hSL : S ⊆ L := fun y hy => hy.1
  have hSfin : μ S ≠ ⊤ := ne_top_of_le_ne_top hLfin (measure_mono hSL)

  have hbd : ‖starLoc (Af F) σ J (psiFin F ψ) μ Q bc‖ ≤
      (∑ a ∈ s, ‖Q a‖) * √((μ (L : Set _)).toReal * (μ S).toReal) := by
    have hw := GlobalTheory.T.gauss_sum_quadratic_character_bound _ μ L hLc hLo q B hp1 hp2 (GlobalTheory.T.phase_cocycle_bimultiplicative F E σ hCM M J hJ n ψ hψ bc) hq1 hq2
    exact GlobalTheory.T.gauss_sum_finite_average_bound _ μ L hLc hLo q hp1 hp2 _ hw Q s hs

  have hSm : MeasurableSet S := by
    have e : S = (L : Set _) ∩ ⋂ l ∈ L, (B l) ⁻¹' {1} := by
      ext y
      simp [hS]
    have hcl : IsClosed S := by
      rw [e]
      have hLcl : IsClosed (L : Set (Fin n → Fin M → Af F ⊗[F] E)) := hLc.isClosed
      exact hLcl.inter (isClosed_biInter fun l _ => isClosed_singleton.preimage (hp3 l))
    exact hcl.measurableSet

  have hdiff : ∀ u ∈ S, ∀ v ∈ S, ∀ l ∈ L, B l (v - u) = 1 := by
    intro u hu v hv l hl
    have h := hq2 l u (v - u)
    rw [add_sub_cancel, hv.2 l hl, hu.2 l hl, one_mul] at h
    exact h.symm
  set c' : Matrix (Fin n) (Fin n) E := ((t • c).1).map σ with hc'
  have hδ : delta c' = delta (t • c).1 := GlobalTheory.T.delta_conj_invariant F E σ n _
  have hδ0 : delta c' ≠ 0 := GlobalTheory.T.delta_ne_zero' E n c'
  haveI hfin : Finite ((Fin n → 𝓞 E) ⧸ Kc c') := Nat.finite_of_card_ne_zero hδ0
  haveI := Fintype.ofFinite ((Fin n → 𝓞 E) ⧸ Kc c')

  have hcount : ((delta c' ^ M : ℕ) : ℝ≥0∞) * μ S ≤ μ (L : Set _) := by
    have h := GlobalTheory.T.disjoint_translates_volume_bound _ μ L S hSm hSL (Fin M → (Fin n → 𝓞 E) ⧸ Kc c')
      (fun φ => ratTuple J s₂ fun i => (φ i).out) (fun φ => hrat _) ?_
    · have hc : Fintype.card (Fin M → (Fin n → 𝓞 E) ⧸ Kc c') = delta c' ^ M := by
        rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]
        rfl
      rwa [hc] at h
    · intro φ φ' u v hu hv huv
      funext i₀
      have hρ : ratTuple (F := F) J s₂ (fun i => (φ i).out - (φ' i).out) = ratTuple J s₂ (fun i => (φ i).out) - ratTuple J s₂ (fun i => (φ' i).out) := by
        funext a j
        simp only [ratTuple, Pi.sub_apply, map_sub]
        rw [show (fun i => algebraMap (𝓞 E) E ((φ i).out a) - algebraMap (𝓞 E) E ((φ' i).out a)) =
          (fun i => algebraMap (𝓞 E) E ((φ i).out a)) - (fun i => algebraMap (𝓞 E) E ((φ' i).out a)) from rfl,
          Matrix.mulVec_sub]
        simp [mul_sub]
      have hmem : ∀ l ∈ L, B l (ratTuple J s₂ fun i => (φ i).out - (φ' i).out) = 1 := by
        intro l hl
        have : ratTuple (F := F) J s₂ (fun i => (φ i).out - (φ' i).out) = v - u := by
          rw [hρ, sub_eq_sub_iff_add_eq_add, add_comm v]
          exact huv
        rw [this]
        exact hdiff u hu v hv l hl
      have hK : (φ i₀).out - (φ' i₀).out ∈ Kc c' := by
        intro c₀
        have hx := htest ((s₂ : E) * ∑ a, c.1 a c₀ *
          algebraMap (𝓞 E) E (((φ i₀).out - (φ' i₀).out) a)) (fun x hx => by
            have h1 := hmem (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (by
              intro a i
              by_cases h : a = c₀ ∧ i = i₀
              · simpa [h] using hx
              · simp only [h, if_false]
                exact (latN b n M N).zero_mem a i)
            rw [hB, hbc, GlobalTheory.T.pairing_on_rational_tuple_formula F E σ M J hJ n (psiFin F ψ) c c₀ i₀ x s₂ _] at h1
            exact h1)
        obtain ⟨o, ho⟩ := hx
        refine ⟨o, ?_⟩
        rw [ho]
        simp only [Matrix.mulVec, dotProduct, hc', Matrix.map_apply, Finset.smul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        have h3 : σ (c.1 c₀ a) = c.1 a c₀ := c.2 a c₀
        rw [show σ ((t • c).1 c₀ a) = t • c.1 a c₀ from by
          show σ (t • c.1 c₀ a) = _
          rw [Algebra.smul_def, map_mul, AlgHom.commutes, h3, ← Algebra.smul_def]]
        simp only [ht, Algebra.smul_def, map_mul, map_natCast]
        ring
      have h5 : (QuotientAddGroup.mk (φ' i₀).out : (Fin n → 𝓞 E) ⧸ Kc c') = QuotientAddGroup.mk (φ i₀).out :=
        QuotientAddGroup.eq.2 (by rw [neg_add_eq_sub]; exact hK)
      rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h5
      exact h5.symm

  have hδpos : (0 : ℝ) < (delta c' : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hδ0)
  have hreal : (delta c' : ℝ) ^ M * (μ S).toReal ≤ (μ (L : Set _)).toReal := by
    have h := ENNReal.toReal_mono hLfin hcount
    rw [ENNReal.toReal_mul] at h
    simpa using h
  rw [← hδ]
  set A := (μ (L : Set _)).toReal with hA
  set Sr := (μ S).toReal with hSr
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ Sr := ENNReal.toReal_nonneg
  set w : ℝ := (delta c' : ℝ) ^ (-((M : ℝ) / 2)) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hδpos.le _
  have hw2 : w ^ 2 * (delta c' : ℝ) ^ M = 1 := by
    rw [hw, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hδpos.le, ← Real.rpow_natCast _ M, ← Real.rpow_add hδpos]
    have : -((M : ℝ) / 2) * ((2 : ℕ) : ℝ) + (M : ℝ) = 0 := by push_cast; ring
    rw [this, Real.rpow_zero]
  have hsq : √(A * Sr) ≤ A * w := by
    refine Real.sqrt_le_iff.2 ⟨mul_nonneg hA0 hw0, ?_⟩
    have h1 : Sr = w ^ 2 * ((delta c' : ℝ) ^ M * Sr) := by rw [← mul_assoc, hw2, one_mul]
    have h2 : Sr ≤ w ^ 2 * A := by
      rw [h1]
      exact mul_le_mul_of_nonneg_left hreal (sq_nonneg _)
    calc A * Sr ≤ A * (w ^ 2 * A) := mul_le_mul_of_nonneg_left h2 hA0
      _ = (A * w) ^ 2 := by ring
  calc _ ≤ (∑ a ∈ s, ‖Q a‖) * √(A * Sr) := hbd
    _ ≤ (∑ a ∈ s, ‖Q a‖) * (A * w) :=
        mul_le_mul_of_nonneg_left hsq (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
