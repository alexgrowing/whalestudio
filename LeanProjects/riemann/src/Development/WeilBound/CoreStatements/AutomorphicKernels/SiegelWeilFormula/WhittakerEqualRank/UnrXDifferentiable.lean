import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.ExistsFinsetOfCofinite

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.WQ

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Filter PositivityTheory.SiegelWeilFormula.Gen.W
open scoped Topology Classical

def unrX (N M : ℕ) (c : ℂ) (q : ℕ) (z : ℂ) : ℂ :=
  ∏ i : Fin N, (1 - c ^ (M + (i : ℕ)) * (q : ℂ) ^ (-(2 * z + N - (i : ℕ))))

theorem unrX_differentiable (N M : ℕ) (c : ℂ) (q : ℕ) (hq : q ≠ 0) : Differentiable ℂ (unrX N M c q) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  unfold unrX
  refine Differentiable.fun_finsetProd fun i _ => ?_
  exact (differentiable_const _).sub ((differentiable_const _).mul
    ((by fun_prop : Differentiable ℂ (fun z : ℂ => -(2 * z + N - (i : ℕ)))).const_cpow (Or.inl hq')))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eSp_sq (v : HeightOneSpectrum (𝓞 F)) : eSp E v ^ 2 = 1 := by
  unfold eSp; split_ifs <;> norm_num

theorem norm_eSp (v : HeightOneSpectrum (𝓞 F)) : ‖eSp E v‖ = 1 := by
  unfold eSp; split_ifs <;> simp

theorem eSp_pow_sub (v : HeightOneSpectrum (𝓞 F)) (N i : ℕ) (hi : i ≤ N) :
    eSp E v ^ (N + i) = eSp E v ^ (((N - i : ℕ) : ℤ)) := by
  rw [zpow_natCast]
  have : N + i = (N - i) + 2 * i := by omega
  rw [this, pow_add, pow_mul, eSp_sq, one_pow, mul_one]

theorem one_sub_eSp_ne (v : HeightOneSpectrum (𝓞 F)) :
    1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  intro h
  have h1 : eSp E v / (Ideal.absNorm v.asIdeal : ℂ) = 1 := by linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_div, norm_eSp, Complex.norm_natCast, norm_one] at h2
  have : (1 : ℝ) / Ideal.absNorm v.asIdeal < 1 := by rw [div_lt_one (by linarith)]; exact hq
  linarith

theorem hasProd_split' {α : Type} (f : α → ℂ) (S : Finset α) (D : ℂ)
    (h : HasProd (fun v : {v // v ∉ S} => f v) D) : HasProd f ((∏ v ∈ S, f v) * D) :=
  hasProd_split f S D h

theorem fix_point (Z H : ℂ → ℂ) (j : ℂ) (hZ : MeromorphicOn Z Set.univ) (hH : AnalyticAt ℂ H j)
    (he : ∀ᶠ s in 𝓝[≠] j, H s = Z s) :
    MeromorphicOn (Function.update Z j (H j)) Set.univ ∧ AnalyticAt ℂ (Function.update Z j (H j)) j ∧
      Function.update Z j (H j) j = H j ∧ ∀ s, s ≠ j → Function.update Z j (H j) s = Z s := by
  refine ⟨fun z _ => (hZ z trivial).update _ _, ?_, by simp, fun s hs => Function.update_of_ne hs _ _⟩
  refine hH.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE ?_ (by simp))
  filter_upwards [he, self_mem_nhdsWithin] with s hs hs'
  rw [Function.update_of_ne (show s ≠ j from hs'), hs]

end PositivityTheory.SiegelWeilFormula.Gen.WQ

end
