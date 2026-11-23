import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DualGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.genOfRk :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N r : ℕ) (U : Subgroup (G F Ω)), IsClosed (U : Set (G F Ω)) → XRk l N (cycU l U) r → Tower.GenLE ℤ_[l] (Xinf l N U) r := by
  intro F Ω _ _ _ _ _ l _ N rk U hU hrk
  classical
  have hQ : ∀ q : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0 := by
    intro q
    revert q
    show ∀ q : ℚ_[l] ⧸ ZlSub l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt ‖x‖ hl
      refine ⟨r, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have hn : ‖(l : ℚ_[l]) ^ r * x‖ ≤ 1 := by
        rw [norm_mul, norm_pow, Padic.norm_p]
        have hp : (0 : ℝ) < (l : ℝ) ^ r := by positivity
        rw [inv_pow, inv_mul_le_iff₀ hp, mul_one]
        exact hr.le
      refine ⟨⟨(l : ℚ_[l]) ^ r * x, hn⟩, ?_⟩
      simp [Algebra.smul_def]
      rfl
  have hC : IsClosed ((cycU l U : Subgroup (G F Ω)) : Set (G F Ω)) :=
    hU.inter (isClosed_singleton.preimage (continuous_cycZ F Ω l))
  haveI : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hC.isCompact
  have htors : ∀ φ : Dinf l N U, ∃ k : ℕ, (l : ℤ_[l]) ^ k • φ = 0 := by
    intro φ
    have hfin := IsLocallyConstant.range_finite φ.2.1
    choose r hr using hQ
    refine ⟨∑ q ∈ hfin.toFinset, r q, ?_⟩
    apply Subtype.ext
    funext u
    have hq : (φ : cycU l U → QZ l) u ∈ hfin.toFinset := by simp
    change (l : ℤ_[l]) ^ (∑ q ∈ hfin.toFinset, r q) • (φ : cycU l U → QZ l) u = 0
    rw [← Finset.add_sum_erase _ _ hq, pow_add, mul_comm, mul_smul, hr, smul_zero]
  obtain ⟨ι, hι, hιr, -⟩ := zmodToQZ l 1
  let κ : ZMod l →+ QZ l := ι.comp (ZMod.ringEquivCongr (pow_one l).symm).toAddMonoidHom
  have hκ : Function.Injective κ := hι.comp (ZMod.ringEquivCongr (pow_one l).symm).injective
  have hκr : ∀ q : QZ l, (l : ℤ_[l]) • q = 0 → κ (Function.invFun κ q) = q := by
    intro q hq
    apply Function.invFun_eq
    obtain ⟨a, ha⟩ := (hιr q).2 (by rw [pow_one]; exact hq)
    exact ⟨(ZMod.ringEquivCongr (pow_one l).symm).symm a, by simp [κ, ha]⟩
  have hval : ∀ φ : Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]), ∀ u : cycU l U,
      (l : ℤ_[l]) • ((φ : Dinf l N U) : cycU l U → QZ l) u = 0 := by
    intro φ u
    have h := (Submodule.mem_torsionBy_iff _ _).1 φ.2
    have h2 := congrArg (fun ψ : Dinf l N U => (ψ : cycU l U → QZ l) u) h
    exact h2
  let f : Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]) → XDual N (cycU l U) (ZMod l) (ZMod l) :=
    fun φ => ⟨fun u => Function.invFun κ (((φ : Dinf l N U) : cycU l U → QZ l) u), by
      have hφ := (φ : Dinf l N U).2
      refine ⟨by exact hφ.1.comp (Function.invFun κ), ?_, ?_, ?_⟩
      · intro a b
        apply hκ
        rw [map_add, hκr _ (hval φ _), hκr _ (hval φ _), hκr _ (hval φ _), hφ.2.1]
      · intro A u hu
        apply hκ
        rw [hκr _ (hval φ _), hφ.2.2.1 A u hu, map_zero]
      · intro A hA u hu
        apply hκ
        rw [hκr _ (hval φ _), hφ.2.2.2 A hA u hu, map_zero]⟩
  have hf : Function.Injective f := by
    intro φ ψ h
    apply Subtype.ext
    apply Subtype.ext
    funext u
    have h1 := congrArg (fun χ : XDual N (cycU l U) (ZMod l) (ZMod l) => κ ((χ : cycU l U → ZMod l) u)) h
    simp only [f] at h1
    rwa [hκr _ (hval φ u), hκr _ (hval ψ u)] at h1
  exact dualGen l (Dinf l N U) rk htors (hrk.of_injective f hf)
