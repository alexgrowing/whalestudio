import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdOfFnEqSingle
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.SecondKindChart

section Norm
open scoped Matrix.Norms.Operator ContDiff

variable {n : ℕ}

theorem ofFn_prod_single {M : Type*} [Monoid M] : ∀ {d : ℕ} (g : Fin d → M) (j : Fin d),
    (∀ i, i ≠ j → g i = 1) → (List.ofFn g).prod = g j := by
  first
  | exact @_root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
  | exact _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
  | (apply _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single ..)

def lc {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) : (Fin d → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (b i)

theorem lc_apply {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (v : Fin d → ℝ) : lc b v = ∑ i, v i • b i := by
  simp [lc, ContinuousLinearMap.sum_apply]

theorem expProd_line {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin d) (r : ℝ) :
    (List.ofFn fun i => NormedSpace.exp ((r • Pi.single j (1 : ℝ) : Fin d → ℝ) i • b i)).prod =
      NormedSpace.exp (r • b j) := by
  rw [ofFn_prod_single _ j]
  · simp
  · intro i hi
    simp [Pi.single_apply, hi]

theorem hasStrictFDerivAt_expProd {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    HasStrictFDerivAt (fun s : Fin d → ℝ => (List.ofFn fun i => NormedSpace.exp (s i • b i)).prod) (lc b) 0 := by
  set f := fun s : Fin d → ℝ => (List.ofFn fun i => NormedSpace.exp (s i • b i)).prod with hfdef
  have hcd : ContDiff ℝ ∞ f := GlobalTheory.GardingVec.contDiff_expProd b
  have hs : HasStrictFDerivAt f (fderiv ℝ f 0) 0 := hcd.contDiffAt.hasStrictFDerivAt (by simp)
  suffices e : fderiv ℝ f 0 = lc b by rwa [e] at hs
  have hD : HasFDerivAt f (fderiv ℝ f 0) 0 := hs.hasFDerivAt
  have hj : ∀ j : Fin d, fderiv ℝ f 0 (Pi.single j 1) = b j := by
    intro j
    have h1 : HasDerivAt (fun r : ℝ => f (r • Pi.single j (1 : ℝ))) (fderiv ℝ f 0 (Pi.single j 1)) 0 := by
      have hl : HasDerivAt (fun r : ℝ => r • (Pi.single j (1 : ℝ) : Fin d → ℝ)) ((1 : ℝ) • Pi.single j 1) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const _
      rw [one_smul] at hl
      exact hD.comp_hasDerivAt_of_eq 0 hl (by simp)
    have h2 : HasDerivAt (fun r : ℝ => f (r • Pi.single j (1 : ℝ))) (b j) 0 := by
      have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (b j) (0 : ℝ)
      simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h3
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
      exact expProd_line b j r
    exact h1.unique h2
  ext1 v
  rw [pi_eq_sum_univ v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : (fun k => if j = k then (1 : ℝ) else 0) = Pi.single j 1 := by
    ext k; simp [Pi.single_apply, eq_comm]
  rw [e1, map_smul, map_smul, hj, lc_apply]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_apply, hi]
  · simp

end Norm

section Chart
open scoped Matrix.Norms.Operator ContDiff

theorem exp_product_chart_local (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ lieSet ε)
    (hli : LinearIndependent ℝ b) (hsp : ∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) (c : Fin d → ℝ) :
    ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod := by
  classical
  set A : (Fin d → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ := lc b with hA
  have hAinj : LinearMap.ker (A : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx' : ∑ i, x i • b i = 0 := by rw [← lc_apply]; exact hx
    funext i
    exact Fintype.linearIndependent_iff.1 hli x hx' i
  obtain ⟨C, hC⟩ := LinearMap.exists_leftInverse_of_injective _ hAinj
  let Cc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap C
  have hCA : ∀ v, Cc (A v) = v := fun v => LinearMap.congr_fun hC v
  set f : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ :=
    fun s => (List.ofFn fun i => NormedSpace.exp (s i • b i)).prod with hfdef
  have hf : HasStrictFDerivAt f A 0 := hasStrictFDerivAt_expProd b
  have hf0 : f 0 = 1 := by simp [hfdef]
  have hlog : HasStrictFDerivAt (Formalism.MainNotions.S.Gauge.logM n) (ContinuousLinearMap.id ℝ _) (f 0) := by
    have h := (Formalism.MainNotions.S.Gauge.hasStrict_expM (n := n)).to_localInverse
    rw [NormedSpace.exp_zero] at h
    rw [hf0]
    exact h
  set ψ : (Fin d → ℝ) → (Fin d → ℝ) := fun s => Cc (Formalism.MainNotions.S.Gauge.logM n (f s)) with hψdef
  have hψ : HasStrictFDerivAt ψ ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
      (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) 0 := by
    have h := Cc.hasStrictFDerivAt.comp (0 : Fin d → ℝ) (hlog.comp (0 : Fin d → ℝ) hf)
    have e : (Cc.comp ((ContinuousLinearMap.id ℝ (Formalism.MainNotions.S.Gauge.MxC n)).comp A)) =
        ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) := by
      ext1 v
      simp [hCA]
    exact h.congr_fderiv e
  have hψ0 : ψ 0 = 0 := by simp [hψdef, hf0, Formalism.MainNotions.S.Gauge.logM_one]
  set g := hψ.localInverse ψ _ 0 with hgdef
  have hg : HasFDerivAt g (((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ)).symm : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
      (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (ψ 0) := hψ.to_localInverse.hasFDerivAt
  have hg0 : g (ψ 0) = 0 := hψ.localInverse_apply_image
  refine ⟨fun t => g (t • c), ?_, ?_, ?_⟩
  · simp only [zero_smul]; simpa [hψ0] using hg0
  · have hl : HasDerivAt (fun t : ℝ => t • c) ((1 : ℝ) • c) 0 := (hasDerivAt_id (0 : ℝ)).smul_const _
    rw [one_smul] at hl
    have := hg.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp [hψ0])
    exact this
  ·
    have hlin : Filter.Tendsto (fun t : ℝ => t • c) (nhds 0) (nhds (ψ 0)) := by
      exact (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • c).tendsto' 0 (ψ 0) (by simp [hψ0])
    have E1 : ∀ᶠ t in nhds (0 : ℝ), ψ (g (t • c)) = t • c := hlin.eventually hψ.eventually_right_inverse
    have hτc : ContinuousAt (fun t : ℝ => g (t • c)) 0 := by
      exact hg.continuousAt.comp_of_eq
        (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • c).continuousAt (by simp [hψ0])
    have hfc : ContinuousAt (fun t : ℝ => f (g (t • c))) 0 :=
      (GlobalTheory.GardingVec.contDiff_expProd b).continuous.continuousAt.comp hτc
    have E2 : ∀ᶠ t in nhds (0 : ℝ), f (g (t • c)) ∈ Formalism.MainNotions.S.Gauge.tOne ε := by
      apply hfc.preimage_mem_nhds
      have h0 : f (g ((0 : ℝ) • c)) = 1 := by simp only [zero_smul]; rw [← hψ0, hg0, hf0]
      rw [h0]
      exact (Formalism.MainNotions.S.Gauge.isOpen_tOne ε).mem_nhds (Formalism.MainNotions.S.Gauge.one_mem_tOne ε)
    filter_upwards [E1, E2] with t h1 h2
    set y := f (g (t • c)) with hy
    have hU : Formalism.REAL.inUJ ε y := by
      have := GlobalTheory.LowTypeDetermined.expProd_mem (GlobalTheory.TypeSum.isUnit_Jm ε) (Xs := b) (fun i => hb i) (g (t • c))
      exact this
    obtain ⟨hG, hE⟩ := Formalism.MainNotions.S.Gauge.logM_inG h2 hU
    obtain ⟨c', hc'⟩ := hsp _ hG
    have hc'A : Formalism.MainNotions.S.Gauge.logM n y = A c' := by rw [hc', hA, lc_apply]
    have hψy : ψ (g (t • c)) = c' := by
      show Cc (Formalism.MainNotions.S.Gauge.logM n y) = c'
      rw [hc'A, hCA]
    have hcc : c' = t • c := by rw [← hψy, h1]
    have hL : Formalism.MainNotions.S.Gauge.logM n y = t • ∑ i, c i • b i := by
      rw [hc'A, hcc, map_smul, hA, lc_apply]
    rw [← hL, hE]

end Chart

theorem exp_eq_expProd_near_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    LinearIndependent ℝ b → (∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) →
    ∀ c : Fin d → ℝ, ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod :=
  fun n ε d b hb hli hsp c => exp_product_chart_local n ε d b hb hli hsp c

end GlobalTheory.SecondKindChart
