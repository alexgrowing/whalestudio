import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootConj
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SgIterateEqSelf

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

private theorem UpperTheory.ConvolutionTheory.Loc.nrm_fixed_eq_pow {E : Type} [Field E] {n : ℕ} (σ : E ≃+* E) (q : ℕ) (u : GL (Fin n) E)
    (hu : sg σ u = u) : nrm σ q u = u ^ q := by
  induction q with
  | zero => simp [nrm]
  | succ q ih => rw [nrm_succ, ih, Function.iterate_fixed hu, pow_succ]

theorem UpperTheory.ConvolutionTheory.Loc.rigidNear :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ r : ValueGroupWithZero E, r < valuation E (q : E) →
      ∀ u ∈ ball n r, ∀ u' ∈ ball n r, sg σ u = u → sg σ u' = u' → ∀ g : GL (Fin n) E, g⁻¹ * u * sg σ g = u' → sg σ g = g := by
  intro E _ _ _ _ n σ q hc r hr u hu u' hu' h h' g hg
  have h1 : g⁻¹ * u ^ q * g = u' ^ q := by
    rw [← UpperTheory.ConvolutionTheory.Loc.nrm_fixed_eq_pow σ q u h, ← UpperTheory.ConvolutionTheory.Loc.nrm_fixed_eq_pow σ q u' h', ← hg, nrm_conj hc.ord]
  have h2 := UpperTheory.ConvolutionTheory.Loc.rootConj E n q r hr u hu u' hu' g h1
  exact mul_left_cancel (hg.trans h2.symm)
