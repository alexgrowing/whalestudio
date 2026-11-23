import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Carver
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.AmbAbs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem carver_abs (K : Type) [Field K] [IsAlgClosed K] (w : AbsoluteValue K ℝ) (hp : ∃ p, p ≠ 0 ∧ w p ≠ 1)
    (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X) (z : σ → K)
    (hz : ∀ n : σ →₀ ℕ, n ≠ 0 → Finsupp.weight wt n = 0 → w (n.prod fun s k => z s ^ k) < 1) :
    ∃ t : Multiplicative X →* Kˣ, ∀ s, w ((t (Multiplicative.ofAdd (wt s)) : K) * z s) < 1 := by
  letI : NormedField K := w.toNormedField
  exact carver σ X wt K z hp hz

theorem UpperTheory.V.Ws.Po.ambScale :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V), 𝔞.IsDvr f →
      ∀ (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X) (z : σ → 𝔞.K),
      (∀ n : σ →₀ ℕ, n ≠ 0 → Finsupp.weight wt n = 0 → 𝔞.V.valuation (n.prod fun s k => z s ^ k) < 1) →
      ∃ t : Multiplicative X →* 𝔞.Kˣ, ∀ s, 𝔞.V.valuation ((t (Multiplicative.ofAdd (wt s)) : 𝔞.K) * z s) < 1 := by
  intro l _ 𝔞 A _ _ _ f hf σ _ X _ _ _ wt z hz
  obtain ⟨w, hw, hp⟩ := UpperTheory.V.Ws.Po.ambAbs 𝔞 A f hf
  obtain ⟨t, ht⟩ := carver_abs 𝔞.K w hp σ X wt z fun n hn h0 => (hw _).2 (hz n hn h0)
  exact ⟨t, fun s => (hw _).1 (ht s)⟩
