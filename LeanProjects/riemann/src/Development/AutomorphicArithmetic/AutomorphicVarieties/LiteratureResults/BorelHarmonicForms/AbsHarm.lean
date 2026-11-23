import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaSucc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IpAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IpDef
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem absHarm_real {z : ℂ} (h : z = starRingEnd ℂ z) (h0 : z.re = 0) : z = 0 := by
  have h1 := congrArg Complex.im h
  rw [Complex.conj_im] at h1
  exact Complex.ext h0 (by rw [Complex.zero_im]; linarith)

theorem UpperTheory.V.Lit.Bor.absHarm :
    UpperTheory.V.Lit.Bor.AbsHarm := by
  intro E _ _ _ a n e he M _ _ _ _ A B hA hB hAB hc H hH hadj q ω hω
  have hadj' := fun q ω η => ipAdj E a n e M (A + B) (B - A) H ⊤ (fun X x _ y _ => hadj X x y) q ω η
    (fun _ => Submodule.mem_top) (fun _ => Submodule.mem_top)
  have hdef := ipDef E a n e he M H ⊤ hH
  have hpos := fun q ω => ((hdef q).2 ω (fun _ => Submodule.mem_top)).1
  have hzero := fun q ω (h : (ip e H ω ω).re = 0) =>
    ((hdef q).2 ω (fun _ => Submodule.mem_top)).2 (absHarm_real ((hdef q).1 ω ω) h)
  have hc0 : cas B e - cas A e = 0 := sub_eq_zero.2 hc
  cases q with
  | zero =>
    refine ⟨hzero _ _ ?_, trivial⟩
    have h1 := kugaZero E a n e M A B hAB ω hω
    have h2 : ip e H (del (B - A) e (dCo (A + B) ω)) ω = 0 := by
      simp only [ip, h1, hc0, LinearMap.zero_apply, map_zero, Finset.sum_const_zero]
    rw [hadj', h2, mul_zero, Complex.zero_re]
  | succ q =>
    have h1 := kugaSucc E a n e he M A B hA hB hAB q ω hω
    have h2 : ip e H (dCo (A + B) (del (B - A) e ω)) ω + ip e H (del (B - A) e (dCo (A + B) ω)) ω = 0 := by
      simp only [ip]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun I _ => ?_
      rw [← LinearMap.add_apply, ← map_add, h1, hc0, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
    have h3 := congrArg Complex.re (hadj' (q + 1) (dCo (A + B) ω) ω)
    have h4 := congrArg Complex.re (hadj' q ω (del (B - A) e ω))
    have h5 := congrArg Complex.re ((hdef (q + 1)).1 ω (dCo (A + B) (del (B - A) e ω)))
    have h6 := congrArg Complex.re h2
    have p1 := hpos _ (dCo (A + B) ω)
    have p2 := hpos _ (del (B - A) e ω)
    rw [Complex.conj_re] at h5
    rw [Complex.add_re, Complex.zero_re] at h6
    have hmul : ∀ (k : ℕ) (z : ℂ), (((k : ℂ) + 1) * z).re = ((k : ℝ) + 1) * z.re := fun k z => by simp
    rw [hmul] at h3 h4
    have q0 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    have q1 : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) + 1 := by positivity
    have h7 : (ip e H (dCo (A + B) ω) (dCo (A + B) ω)).re +
        (((q + 1 : ℕ) : ℝ) + 1) * ((q : ℝ) + 1) * (ip e H (del (B - A) e ω) (del (B - A) e ω)).re = 0 := by
      rw [h3, mul_assoc, ← h4, ← h5, ← mul_add, add_comm (Complex.re _), h6, mul_zero]
    have p3 := mul_nonneg (mul_pos q1 q0).le p2
    refine ⟨hzero _ _ (by linarith), hzero _ _ ?_⟩
    exact (mul_eq_zero.1 (show _ * _ = (0 : ℝ) from le_antisymm (by linarith) p3)).resolve_left (mul_pos q1 q0).ne'
