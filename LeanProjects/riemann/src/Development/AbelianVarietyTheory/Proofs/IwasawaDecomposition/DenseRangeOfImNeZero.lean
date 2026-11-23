import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem denseRange_of_im_ne_zero {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) (h : ∃ a, (σ a).im ≠ 0) :
    DenseRange σ := by
  obtain ⟨a, ha⟩ := h
  have hg : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * σ a := by fun_prop
  have hs : Function.Surjective fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * σ a := by
    intro z
    refine ⟨(z.re - z.im / (σ a).im * (σ a).re, z.im / (σ a).im), ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]
      field_simp
      ring
  have hq : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hc := hs.denseRange.comp hq hg
  refine hc.mono ?_
  rintro _ ⟨⟨p, q⟩, rfl⟩
  exact ⟨(p : K) + (q : K) * a, by simp⟩

theorem normAt_sq_eq_majAt_re {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : Formalism.HermitianLatticesTheory.normAt b X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem fnorm_cjv_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (s : Bool), (∀ a, (InfinitePlace.mk σ).embedding a = cj s (σ a)) → (∃ a, (σ a).im ≠ 0) → ∀ (A : HLat K) (d : ℕ) (L : Submodule (RingOfIntegers K) (Fin d → K)) (Xf : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (e : (Fin d → K) ≃ₗ[K] A.V), HLatTie A L Xf e → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : A.V →ₛₗ[σ] W) (c : W ≃ₗ[ℂ] (Fin d → ℂ)), (∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖j x‖) → (∀ x, c.symm (cpt σ x) = j (e x)) → ∀ w : W, Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s (c w)) = ‖w‖ := by
  intro K _ _ _ σ s htw hnr A d L Xf e hT W _ _ j c hn hc w
  have hd : DenseRange (cpt σ : (Fin d → K) → Fin d → ℂ) :=
    DenseRange.piMap (fun _ : Fin d => denseRange_of_im_ne_zero σ hnr)
  have hcj : Continuous (cj s) := by
    cases s
    · exact continuous_id
    · exact Complex.continuous_conj
  have h1 : Continuous fun z : Fin d → ℂ => Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s z) := by
    unfold Formalism.DivisionValues.fnorm Formalism.HermitianLatticesTheory.cnorm cjv Matrix.mulVec dotProduct
    fun_prop
  have h2 : Continuous fun z : Fin d → ℂ => ‖c.symm z‖ :=
    (LinearMap.continuous_of_finiteDimensional c.symm.toLinearMap).norm
  have key : ∀ z : Fin d → ℂ, Formalism.DivisionValues.fnorm (Xf (InfinitePlace.mk σ)) (cjv s z) = ‖c.symm z‖ := by
    intro z
    refine hd.induction_on z (isClosed_eq h1 h2) fun x => ?_
    rw [hc, ← hn, normAt_sq_eq_majAt_re, hT.metric, ← normAt_sq_eq_majAt_re]
    have hv : cjv s (cpt σ x) = Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) (InfinitePlace.mk σ) x := by
      funext i
      simp [cjv, cpt, Formalism.HermitianLatticesTheory.vecAt, htw]
    rw [hv]
    rfl
  rw [key, c.symm_apply_apply]

end GlobalTheory.Mem.SJ
