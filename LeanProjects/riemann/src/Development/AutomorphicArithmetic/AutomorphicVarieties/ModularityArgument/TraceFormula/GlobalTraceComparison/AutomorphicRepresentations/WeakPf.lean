import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ctx_fub (X : Ctx) (φ : X.G → ℂ) (hφ : Tst φ) (g f : X.G → ℂ) (hg : MemLp g 2 X.ν) (hf : MemLp f 2 X.ν) :
    Integrable (fun y => (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y) X.ν ∧
      Integrable (fun z => g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν) X.ν ∧
      ∫ y, (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y ∂X.ν = ∫ z, g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν ∂X.ν := by
  obtain ⟨A, hA, h1, h2⟩ := rowInt X φ hφ
  have hm : Measurable (Function.uncurry (ker X.Γ φ)) := (kerBasic X φ hφ).2.1.measurable
  have hν : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hP := schurInt X.G X.ν (ker X.Γ φ) A hm hA h1 h2 g f hg hf
  have e1 : ∀ y, ∫ z, g z * ker X.Γ φ z y * f y ∂X.ν = (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y :=
    fun y => integral_mul_const _ _
  have e2 : ∀ z, ∫ y, g z * ker X.Γ φ z y * f y ∂X.ν = g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν := fun z => by
    simp_rw [mul_assoc]; exact integral_const_mul _ _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [e1] using hP.integral_prod_right
  · simpa only [e2] using hP.integral_prod_left
  · simp_rw [← e1, ← e2]
    exact (integral_integral_swap (f := fun z y => g z * ker X.Γ φ z y * f y) hP).symm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.weak_pf :
    Weak := by
  intro E _ _ _ n ι _ s v u i
  have hth : ∀ y : H E n 0, th (th y) = y := fun y =>
    Prod.ext (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _) (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _)
  let c : ι → ℂ := fun l => s.M l i
  let g : ι → H E n 0 → ℂ := fun j z => starRingEnd ℂ ((u j : H E n 0 → ℂ) z)
  have hg : ∀ j, MemLp (g j) 2 s.D.ν := fun j => (Lp.memLp (u j)).star
  have F : ∀ j l, Integrable (fun y => (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) s.D.ν ∧
      Integrable (fun z => g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) s.D.ν ∧
      ∫ y, (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y ∂s.D.ν =
        ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν := fun j l =>
    ctx_fub (ctx ratProper_holds s.D) (s.Φ₂ j l) (s.t₂ j l) (g j) v (hg j) (Lp.memLp v)
  have hrep : ∀ y, (v : H E n 0 → ℂ) y * inner ℂ u (s.k₂ (th y) i) =
      ∑ j, ∑ l, c l * ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) := by
    intro y
    rw [s.vecs.rep₂ (th y) i u, hth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const]
    ring
  have hv : ∀ (l : ι) (φ : H E n 0 → ℂ), ∫ y, φ y * ((vecM v c l : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) y ∂s.D.ν =
      c l * ∫ y, φ y * (v : H E n 0 → ℂ) y ∂s.D.ν := by
    intro l φ
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    have e : (vecM v c l : Lp ℂ 2 s.D.ν) = c l • v := rfl
    filter_upwards [Lp.coeFn_smul (c l) v] with y hy
    rw [e, hy, Pi.smul_apply, smul_eq_mul]
    ring
  have hR : inner ℂ u (s.T₂ (vecM v c)) =
      ∑ j, ∑ l, c l * ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [L2.inner_def]
    have h : (fun z => inner ℂ ((u j : Lp ℂ 2 s.D.ν) z) ((s.T₂ (vecM v c) j : Lp ℂ 2 s.D.ν) z)) =ᵐ[s.D.ν]
        fun z => ∑ l, c l * (g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) := by
      filter_upwards [s.o₂ (vecM v c) j] with z hz
      rw [hz, RCLike.inner_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hv]
      simp only [g]
      ring
    rw [integral_congr_ae h, integral_finset_sum _ fun l _ => (F j l).2.1.const_mul _]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  have hint : Integrable (fun y => ∑ j, ∑ l, c l *
      ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y)) s.D.ν :=
    integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => (F j l).1.const_mul _
  refine ⟨?_, ?_⟩
  · simpa only [hrep] using hint
  · simp only [hrep]
    change _ = inner ℂ u (s.T₂ (vecM v c))
    rw [hR, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => (F j l).1.const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finset_sum _ fun l _ => (F j l).1.const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, (F j l).2.2]

end
