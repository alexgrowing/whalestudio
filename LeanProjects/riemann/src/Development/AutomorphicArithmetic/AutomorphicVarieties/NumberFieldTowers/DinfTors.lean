import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DinfNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.dinfTors :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G k Ω)), (IsClosed (U : Set (G k Ω)) → ∀ φ : Dinf l N U, ∃ r : ℕ, (l : ℤ_[l]) ^ r • φ = 0) ∧
        Dinf l N U ≤ Dinf l 1 U ∧ xRank l N U ≤ xRank l 1 U ∧
        ∀ [U.Normal] (e : ℤ), ∀ g ∈ cycU l U, dRep l N U g = 1 ∧ xRep l N U g = 1 ∧ dTw l N U e g = 1 ∧ xTw l N U e g = 1 := by
  intro k Ω _ _ _ _ _ l _ N U
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
  have hconj : ∀ [U.Normal] (g : G k Ω), g ∈ cycU l U → ∀ φ : Dinf l N U, dRep l N U g φ = φ := by
    intro _ g hg φ
    have hadd := φ.2.2.1
    have h1 : (φ : cycU l U → QZ l) 1 = 0 := by
      have := hadd 1 1
      rw [mul_one] at this
      simpa using this
    apply Subtype.ext
    funext u
    have e1 : conjHom (cycU l U) g u = (⟨g, hg⟩ : cycU l U)⁻¹ * u * ⟨g, hg⟩ := rfl
    change (φ : cycU l U → QZ l) (conjHom (cycU l U) g u) = _
    rw [e1, hadd, hadd]
    have h2 := hadd (⟨g, hg⟩ : cycU l U)⁻¹ ⟨g, hg⟩
    rw [inv_mul_cancel, h1] at h2
    rw [add_comm ((φ : cycU l U → QZ l) _) ((φ : cycU l U → QZ l) u), add_assoc, ← h2, add_zero]
  have hmono : Dinf l N U ≤ Dinf l 1 U := fun φ hφ =>
    ⟨hφ.1, hφ.2.1, hφ.2.2.1, fun A hA => by simp at hA⟩
  refine ⟨fun hU φ => ?_, hmono, ?_, ?_⟩
  · classical
    have hC : IsClosed ((cycU l U : Subgroup (G k Ω)) : Set (G k Ω)) :=
      hU.inter (isClosed_singleton.preimage (continuous_cycZ k Ω l))
    haveI : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hC.isCompact
    have hfin := IsLocallyConstant.range_finite φ.2.1
    choose r hr using hQ
    refine ⟨∑ q ∈ hfin.toFinset, r q, ?_⟩
    apply Subtype.ext
    funext u
    have hq : (φ : cycU l U → QZ l) u ∈ hfin.toFinset := by simp
    change (l : ℤ_[l]) ^ (∑ q ∈ hfin.toFinset, r q) • (φ : cycU l U → QZ l) u = 0
    rw [← Finset.add_sum_erase _ _ hq, pow_add, mul_comm, mul_smul, hr, smul_zero]
  · refine Module.length_le_of_injective
      (LinearMap.restrict (Submodule.inclusion hmono)
        (p := Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]))
        (q := Submodule.torsionBy ℤ_[l] (Dinf l 1 U) (l : ℤ_[l])) fun x hx => ?_) ?_
    · rw [Submodule.mem_torsionBy_iff] at hx ⊢
      rw [← LinearMap.map_smul, hx, map_zero]
    · intro a b hab
      apply Subtype.ext
      apply Submodule.inclusion_injective hmono
      exact congrArg Subtype.val hab
  · intro _ e g hg
    have hc : cycZ k Ω l g = 1 := hg.2
    have hd : dRep l N U g = 1 := LinearMap.ext fun φ => hconj g hg φ
    have hx : xRep l N U g = 1 := by
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro φ
      change ((dRep l N U).linHom (Representation.trivial ℤ_[l] (G k Ω) (QZ l)) g f) φ = f φ
      rw [Representation.linHom_apply]
      simp [hconj g⁻¹ (inv_mem hg)]
    refine ⟨hd, hx, ?_, ?_⟩
    · show ((cycZ k Ω l ^ (-e)) g : ℤ_[l]) • dRep l N U g = 1
      simp [hc, hd]
    · show ((cycZ k Ω l ^ e) g : ℤ_[l]) • xRep l N U g = 1
      simp [hc, hx]
