import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ExistsSecNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SameDegreeZeroOfRestriction
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.KillHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.GrEqRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem quotient_homogeneous_graded {k : ℕ} (X : HidaSetting k) (J : Ideal X.R) (hJ : (GMod.self X.𝒜).IsHomSub J) :
    ((GMod.self X.𝒜).quo J).IsGr X.𝒜 := by
  have h : (GMod.self X.𝒜).IsGr X.𝒜 :=
    ⟨fun ha hx => SetLike.mul_mem_graded (A := X.𝒜) ha hx, DirectSum.Decomposition.isInternal X.𝒜,
      inferInstanceAs (Module.Finite X.R X.R)⟩
  exact ((ruleGr k X _ h).1 J hJ).2

private theorem power_ideal_kills_graded_pieces {k : ℕ} (X : HidaSetting k) (J : Ideal X.R) (hJ : (GMod.self X.𝒜).IsHomSub J)
    (I I' : Ideal X.B)
    (h : ∀ p : Ideal X.R, p.IsPrime → ¬ Irr X.𝒜 ≤ p → J ≤ p → I'.map (algebraMap X.B X.R) ≤ p →
      I.map (algebraMap X.B X.R) ≤ p) :
    ∃ n : ℕ, ∀ᶠ d in atTop, I ^ n • ((GMod.self X.𝒜).quo J).gr d ≤ I' • ((GMod.self X.𝒜).quo J).gr d := by
  have : IsNoetherianRing X.R := Std.isNoetherianRing X.𝒜 X.std
  have h1 : I.map (algebraMap X.B X.R) * Irr X.𝒜 ≤ (J ⊔ I'.map (algebraMap X.B X.R)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hp, hpp⟩
    by_cases hi : Irr X.𝒜 ≤ p
    · exact Ideal.mul_le_right.trans hi
    · exact Ideal.mul_le_left.trans (h p hpp hi (le_sup_left.trans hp) (le_sup_right.trans hp))
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h1 (IsNoetherian.noetherian _)
  refine ⟨n, kill_holds k X _ (quotient_homogeneous_graded X J hJ) I I' n (hn.trans (sup_le_sup_right ?_ _))⟩
  exact (Ideal.annihilator_quotient (I := J)).ge

private theorem localized_length_zero {O B K M : Type} [CommRing O] [CommRing B] [Algebra O B] [Field K] [Algebra O K]
    [AddCommGroup M] [Module B M] (σ : B →ₐ[O] K) (N : Submodule B M) [Module.Finite B N]
    (I I' : Ideal B) (n : ℕ) (h : I ^ n • N ≤ I' • N) (hI' : I' ≤ RingHom.ker σ) (b : B) (hb : b ∈ I)
    (hσ : σ b ≠ 0) : locLen σ N = 0 := by
  have hp : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
  unfold locLen
  rw [Module.length_eq_zero_iff]
  by_contra hs
  rw [not_subsingleton_iff_nontrivial] at hs
  have h1 : (⟨RingHom.ker σ, hp⟩ : PrimeSpectrum B) ∈ Module.support B (N ⧸ (I' • ⊤ : Submodule B N)) := by
    rw [Module.support_quotient]
    exact ⟨hs, hI'⟩
  rw [Module.mem_support_iff_of_finite] at h1
  have h2 : b ^ n ∈ Module.annihilator B (N ⧸ (I' • ⊤ : Submodule B N)) := by
    rw [Module.mem_annihilator]
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff]
    exact h (Submodule.smul_mem_smul (Ideal.pow_mem_pow hb n) y.2)
  exact hσ (hp.mem_of_pow_mem n (h1 h2))

private theorem finite_quotient_of_kernel_pow {O B C : Type} [CommRing O] [CommRing B] [Algebra O B] [IsNoetherianRing B]
    [CommRing C] [Algebra O C] (g : B →ₐ[O] C) (hg : (LinearMap.range g.toLinearMap).FG)
    (L : Ideal B) (n : ℕ) (h : RingHom.ker g ^ n ≤ L) : Module.Finite O (B ⧸ L) := by
  have h1 : Module.Finite O g.range := Module.Finite.iff_fg.2 hg
  have h2 : Module.Finite O (B ⧸ RingHom.ker g) :=
    Module.Finite.equiv (Ideal.quotientKerEquivRange g).symm.toLinearEquiv
  have h3 : Module.Finite O (B ⧸ (L ⊔ RingHom.ker g)) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ O (le_sup_right : RingHom.ker g ≤ L ⊔ RingHom.ker g)).toLinearMap
      (Ideal.Quotient.factor_surjective le_sup_right)
  refine Module.finite_of_surjective_of_ker_le_nilradical
    (Ideal.Quotient.factorₐ O (le_sup_left : L ≤ L ⊔ RingHom.ker g)) (Ideal.Quotient.factor_surjective le_sup_left) ?_
    (IsNoetherian.noetherian _)
  intro y hy
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hy' : y ∈ L ⊔ RingHom.ker g := Ideal.Quotient.eq_zero_iff_mem.1 hy
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hy'
  refine mem_nilradical.2 ⟨n, ?_⟩
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact h (Ideal.pow_mem_pow hc n)

theorem UpperTheory.V.Alg.M.eventually_mQ_gr_finite_annihilator :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    SpansCot x 𝒜 (-1) Q.F → SpansCot x 𝒜 (-2) Q.G → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal →
    ∀ J : Ideal (mR Q), (GMod.self (mGr Q)).IsHomSub J → secs (ts Q) ≤ J → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ J) →
      ∀ᶠ d in atTop, Module.Finite O (𝒜 0 ⧸ Module.annihilator (𝒜 0) ((mQ Q J).gr d)) ∧
        ∀ σ : 𝒜 0 →ₐ[O] K, (idD 𝒜 ≤ RingHom.ker σ ∨ ∃ b : 𝒜 0, (b : A) ∈ Q.ideal ∧ σ b ≠ 0) → locLen σ ((mQ Q J).gr d) = 0 := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q hF hG h2 h3 J hJ hs hZ
  have fg := fg_holds O A 𝒜 x hW
  have hstd : Std (mGr Q) := std_holds (𝒜 0) A 3 _ fun i => by
    fin_cases i
    · exact fg _
    · exact fg _
    · exact (Submodule.fg_span_singleton _).sup (((fg _).mul (fg _)).mul (fg _))
  let X : HidaSetting 3 := { B := 𝒜 0, R := mR Q, 𝒜 := mGr Q, std := hstd }
  let g : 𝒜 0 →ₐ[O] A ⧸ Q.ideal := (Ideal.Quotient.mkₐ O Q.ideal).comp (IsScalarTower.toAlgHom O (𝒜 0) A)
  have hgk : ∀ b : 𝒜 0, b ∈ RingHom.ker g ↔ (b : A) ∈ Q.ideal := fun b => Ideal.Quotient.eq_zero_iff_mem
  have hg : (LinearMap.range g.toLinearMap).FG := by
    unfold M2 at h2
    convert h2 using 1
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨n, hn⟩ := power_ideal_kills_graded_pieces X J hJ (RingHom.ker g) ⊥ fun p hp hi hJp _ =>
    Ideal.map_le_iff_le_comap.2 fun b hb =>
      (zi_holds O A 𝒜 x hW r s r' s' m Q p hp hi (hs.trans hJp) fun i => hJp (hZ i)).1 b ((hgk b).1 hb)
  obtain ⟨n', hn'⟩ := power_ideal_kills_graded_pieces X J hJ (maximalIdeal (𝒜 0)) (idD 𝒜) fun p hp hi hJp hD =>
    zii_holds O K A 𝒜 x hW r s r' s' m Q hF hG h2 h3 p hp hi (hs.trans hJp) (fun i => hJp (hZ i)) hD
  filter_upwards [hn, hn'] with d hd hd'
  have hfin : Module.Finite (𝒜 0) ((mQ Q J).gr d) := (ruleFin 3 X _ (quotient_homogeneous_graded X J hJ)).1 d
  refine ⟨finite_quotient_of_kernel_pow g hg _ n fun c hc => ?_, ?_⟩
  · rw [Module.mem_annihilator]
    intro y
    have := hd (Submodule.smul_mem_smul hc y.2)
    rw [Submodule.bot_smul, Submodule.mem_bot] at this
    exact Subtype.ext this
  · rintro σ (hσ | ⟨b, hb, hσ⟩)
    · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
      refine localized_length_zero σ _ _ _ n' hd' hσ (algebraMap O _ ϖ) (fun hu => hϖ.not_isUnit (IsLocalHom.map_nonunit _ hu)) ?_
      rw [AlgHom.commutes]
      exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).2 hϖ.ne_zero
    · exact localized_length_zero σ _ _ _ n hd bot_le b ((hgk b).2 hb) hσ
