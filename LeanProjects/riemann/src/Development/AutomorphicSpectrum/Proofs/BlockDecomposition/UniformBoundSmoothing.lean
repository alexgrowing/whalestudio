import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.Conc

theorem norm_integral_ker_le {K : Type} [Field K] [NumberField K] {n : ℕ}
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {β : archGroup K n → ℝ} (hk : Ker ν β)
    (g : archGroup K n → ℂ) {M : ℝ} (hg : ∀ y ∈ tsupport β, ‖g y‖ ≤ M) :
    ‖∫ y, (β y : ℂ) * g y ∂ν‖ ≤ M := by
  have hint : Integrable (fun y => β y * M) ν :=
    (hk.cont.integrable_of_hasCompactSupport hk.cpt).mul_const M
  have hpt : ∀ y, ‖(β y : ℂ) * g y‖ ≤ β y * M := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk.nonneg y)]
    by_cases hy : y ∈ tsupport β
    · exact mul_le_mul_of_nonneg_left (hg y hy) (hk.nonneg y)
    · rw [image_eq_zero_of_notMem_tsupport hy]
      simp
  have h := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
  rwa [integral_mul_const, hk.mass, one_mul] at h

theorem uBnd_sm (K : Type) [Field K] [NumberField K] (n : ℕ)
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type)
    (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (hk : Ker ν β) (_hf : ∀ i, Continuous (f i))
    (hb : UBnd f m) : UBnd (fun i => sm ν β (f i)) m := by
  intro ω hω hsub t₀ Q hQ
  have hQ' : IsCompact (Q * infEmb K n '' tsupport β) :=
    hQ.mul (hk.cpt.isCompact.image continuous_infEmb)
  obtain ⟨C, hC⟩ := hb ω hω hsub t₀ _ hQ'
  refine ⟨max C 0, fun i b hbω x hx q hq => ?_⟩
  refine norm_integral_ker_le ν hk _ ?_
  intro y hy
  rw [mul_assoc (b * _) q]
  refine (hC i b hbω x hx _ (Set.mul_mem_mul hq (Set.mem_image_of_mem _ hy))).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end GlobalTheory.CompanionTheory.Conc
