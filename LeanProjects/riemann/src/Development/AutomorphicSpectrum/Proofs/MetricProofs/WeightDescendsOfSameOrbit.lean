import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

private theorem grading_map_coeff_eq_monomial {K σ : Type} (s : σ → K)
    (φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial K (MvPolynomial σ ℤ))
    (hφ : ∀ q, φ (MvPolynomial.X q) = MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X (s q))
    (g : MvPolynomial σ ℤ) : ∀ a : K →₀ ℕ,
    φ ((φ g).coeff a) = MvPolynomial.monomial a ((φ g).coeff a) := by
  classical
  induction g using MvPolynomial.induction_on
  · rename_i r
    intro a
    have h1 : φ (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
      simpa [MvPolynomial.algebraMap_apply] using φ.commutes r
    rw [h1, MvPolynomial.coeff_C]
    split_ifs with h
    · subst h
      rw [h1, MvPolynomial.C_apply]
    · simp
  · rename_i f1 f2 hf hg
    intro a
    simp only [map_add, MvPolynomial.coeff_add, hf, hg]
  · rename_i f n hf
    intro a
    rw [map_mul φ f (MvPolynomial.X n), hφ, mul_left_comm, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_mul_X']
    split_ifs with h
    · have he : Finsupp.single (s n) 1 ≤ a := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h)
      have hX : (MvPolynomial.X (s n) : MvPolynomial K (MvPolynomial σ ℤ)) =
          MvPolynomial.monomial (Finsupp.single (s n) 1) 1 := rfl
      rw [map_mul, hφ, hf, mul_assoc, hX, MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial,
        one_mul, add_tsub_cancel_of_le he]
    · simp

private theorem smul_mem_lemma_2 {K : Type} {ι : K → Type} {Φ : Type} [Field Φ]
    (y : (Σ k, ι k) → Φ) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ f ∈ mCoordIdeal y, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0)
    (c : K → ℂ) (f : MRing ι) (hf : f ∈ mCoordIdeal y) :
    MvPolynomial.eval (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  classical
  let φ : MvPolynomial ((k : K) × ι k) ℤ →ₐ[ℤ] MvPolynomial K (MvPolynomial ((k : K) × ι k) ℤ) :=
    MvPolynomial.aeval (fun q => MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X q.1)
  have hφ : ∀ q, φ (MvPolynomial.X q) = MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X q.1 :=
    fun q => MvPolynomial.aeval_X _ _
  have hA : ∀ g, mConeMap y g =
      MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom (φ g) := by
    intro g
    have key : (mConeMap y : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial K Φ) =
        ((MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom).toIntAlgHom).comp φ := by
      apply MvPolynomial.algHom_ext
      intro q
      show mConeMap y (MvPolynomial.X q) =
        MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom (φ (MvPolynomial.X q))
      rw [hφ]
      simp [mConeMap]
    rw [key]
    rfl
  have hf' : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  have hcomp : ∀ a, (φ f).coeff a ∈ mCoordIdeal y := by
    intro a
    have h1 : (MvPolynomial.aeval (R := ℤ) y).toRingHom ((φ f).coeff a) = 0 := by
      have := congrArg (MvPolynomial.coeff a) (hA f)
      rw [hf', MvPolynomial.coeff_zero, MvPolynomial.coeff_map] at this
      exact this.symm
    show (φ f).coeff a ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, hA, grading_map_coeff_eq_monomial Sigma.fst φ hφ f a, MvPolynomial.map_monomial, h1,
      map_zero]
  have hB : MvPolynomial.eval (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.map (Int.castRingHom ℂ) f) =
      MvPolynomial.eval c (MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ f)) := by
    rw [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def]
    have key : (MvPolynomial.aeval (R := ℤ) (fun r : (Σ k, ι k) => c r.1 * z r)) =
        ((MvPolynomial.eval c).toIntAlgHom).comp
          (((MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom).toIntAlgHom).comp φ) := by
      apply MvPolynomial.algHom_ext
      intro q
      show MvPolynomial.aeval (R := ℤ) (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.X q) =
        MvPolynomial.eval c (MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ (MvPolynomial.X q)))
      rw [hφ]
      simp [mul_comm]
    rw [key]
    rfl
  rw [hB]
  have hzero : MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ f) = 0 := by
    ext a
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    have := hz _ (hcomp a)
    rwa [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def] at this
  rw [hzero, map_zero]

theorem weight_descends_of_sameOrbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (e e' : ℕ)
    (R : AnLogRes (mCoordIdeal y) ⊤ e) (Rp : AnLogRes (mCoordIdeal (y ∘ stepV M p)) ⊤ e') (h : R.X → Rp.X)
    (A B : HermLine ι) (ph : Rp.X → ℝ) (W : Set Rp.X), A.a = B.a →
    (∀ x, SameOrbit (Rp.lift (h x) (h x)) (R.lift x x ∘ stepV M p)) →
    (∀ x ∈ W, ∀ z ∈ mcPts (mCoordIdeal y), z ∘ stepV M p = Rp.lift x x →
      Real.log (A.h z) = Real.log (B.h z) + ph x) →
    ∀ x, h x ∈ W → Real.log (A.h (R.lift x x)) = Real.log (B.h (R.lift x x)) + ph (h x) := by
  intro K _ ι _ Φ _ y Ψ N j M p e e' R Rp h A B ph W hab horb hW x hx
  classical
  obtain ⟨c, hc0, hceq⟩ := horb x
  have hwmem : R.lift x x ∈ mcPts (mCoordIdeal y) := R.mem x x (R.mem_U x)
  let c' : K → ℂ := fun k =>
    if hk : ((∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some k) ∨ M.blk p = Option.some k) then c ⟨k, hk⟩ else 1
  have hc'0 : ∀ k, c' k ≠ 0 := by
    intro k
    by_cases hk : ((∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some k) ∨ M.blk p = Option.some k)
    · simp only [c', dif_pos hk]
      exact hc0 _
    · simp only [c', dif_neg hk]
      exact one_ne_zero
  let z : (Σ k, ι k) → ℂ := fun r => c' r.1 * R.lift x x r
  have hzstep : z ∘ stepV M p = Rp.lift (h x) (h x) := by
    rw [hceq]
    funext q
    have hq : (∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some q.1.1) ∨ M.blk p = Option.some q.1.1 := q.1.2
    show c' q.1.1 * R.lift x x ⟨q.1.1, q.2⟩ = c q.1 * R.lift x x ⟨q.1.1, q.2⟩
    congr 1
    simp only [c', dif_pos hq]
  have hzmem : z ∈ mcPts (mCoordIdeal y) := by
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := hwmem.1 k
      exact ⟨i, mul_ne_zero (hc'0 k) hi⟩
    · exact smul_mem_lemma_2 y (R.lift x x) hwmem.2 c' f hf
  have key := hW (h x) hx z hzmem hzstep
  have hAz : A.h z = (∏ k, ‖c' k‖ ^ A.a k) * A.h (R.lift x x) := A.smul c' _ hc'0
  have hBz : B.h z = (∏ k, ‖c' k‖ ^ A.a k) * B.h (R.lift x x) := by
    rw [hab]
    exact B.smul c' _ hc'0
  have hP : (∏ k, ‖c' k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc'0 k)))
  have hApos := A.pos _ hwmem.1
  have hBpos := B.pos _ hwmem.1
  rw [hAz, hBz, Real.log_mul hP hApos.ne', Real.log_mul hP hBpos.ne'] at key
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.FA
