import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedNeBotOfIsSubquotientOfIsCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EqOneOfIrreduciblePiAbelianFixedNeBot

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem UpperTheory.smooth_gl_one_cuspidal {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π) : IsCuspidal π := by
  refine ⟨hs, fun s d e he => absurd ?_ he⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  ext i j
  obtain rfl : i = j := Subsingleton.elim _ _
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  simpa using (mem_unipRad.1 hu).2 a i i

private theorem UpperTheory.fixed_vectors_nonzero_character {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (y : IrrRep (GL (Fin 1) k)) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1)
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (h : IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar χ hχ)
    (h1 : ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) :
    fixed y.ρ (GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) ≠ ⊥ := by
  have h' : IrrGL.of y.ρ y.smooth y.irr = IrrGL.of (detRep (Fin 1) χ) (isCuspidal_detRep_one hχ).1
      (isIrreducible_ofChar _) := h
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h'
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible y.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.V)
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv⟩
  have hg : valuation k ((g.1.val - 1) 0 0) < γ := g.2 0 0
  have h2 : χ (Matrix.GeneralLinearGroup.det g.1) = 1 := by
    refine h1 _ ?_
    simpa [Matrix.det_unique] using hg
  refine φ.toLinearEquiv.injective ?_
  have h3 := φ.toIntertwiningMap.isIntertwining _ _ g.1 v
  refine h3.trans ?_
  simp only [detRep, ofChar_apply, detChar_apply, h2, MonoidHom.one_apply, Units.val_one, one_mul, one_smul]
  rfl

theorem UpperTheory.jacquet_exists_levi_congruence_fixed_of_char_support :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL k)) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1), HasSupport π s → (∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) →
    ∀ e : (Σ _ : Fin N, Fin 1) ≃ Fin N, Nontrivial (Jacquet π (unipRad k e)) →
    ∃ y : Jacquet π (unipRad k e), y ≠ 0 ∧ ∀ g : Levi k fun _ : Fin N => Fin 1,
      (∀ a, g a ∈ GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) → jac e π g y = y := by
  intro hG hZ k _ _ _ _ N V _ _ π s γ hγ hs hχ e hJ
  have hjs : IsSmooth (jac e π) := isSmooth_jac e hs.isSmooth
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e π) hJ
  have hτsm : IsSmooth τ := hτs.isSmooth hjs
  have hsm : ∀ j : Fin N, IsSmooth (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) :
      Representation ℂ (GL (Fin 1) k) Y) := fun j =>
    isSmooth_comp hτsm _ (continuous_mulSingle (A := fun _ : Fin N => GL (Fin 1) k) j)
  have hy : ∀ j : Fin N, ∃ y : IrrRep (GL (Fin 1) k), IsSubquotient y.ρ
      (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) : Representation ℂ (GL (Fin 1) k) Y) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
    exact ⟨⟨X, υ, hυs.isSmooth (hsm j), hυ⟩, hυs⟩
  choose y hy using hy
  obtain ⟨u, hu, rfl⟩ := SupportUnique.exists_sum_of_jac (d := fun _ : Fin N => 1) hG hZ hs e hτ hτs y hy
  have hfix : ∀ j : Fin N, fixed (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) :
      Representation ℂ (GL (Fin 1) k) Y) (GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) ≠ ⊥ := by
    intro j
    have hc : (IrrGL.of (y j).ρ (y j).smooth (y j).irr).IsCusp :=
      ⟨Nat.one_pos, UpperTheory.smooth_gl_one_cuspidal (IrrGL.of (y j).ρ (y j).smooth (y j).irr).2.rep.smooth⟩
    have h1 := SupportUnique.eq_singleton_of_isCusp hc ((hu j).of_equiv (IrrGL.equivOf _ _ _))
    obtain ⟨χ, hχs, h2, h3⟩ := hχ (IrrGL.of (y j).ρ (y j).smooth (y j).irr)
      (Multiset.mem_sum.2 ⟨j, Finset.mem_univ j, by rw [h1]; exact Multiset.mem_singleton_self _⟩)
    exact UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact _ _ _ _ _ _ (hsm j) (hy j) (GlobalTheory.CentralExponent.isCompact_cong γ hγ)
      (UpperTheory.fixed_vectors_nonzero_character (y j) γ hγ χ hχs h2 h3)
  have hcomm : ∀ (_ : Fin N) (x z : GL (Fin 1) k), x * z = z * x := by
    intro _ x z
    ext i j
    simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]
  have htriv := UpperTheory.eq_one_of_irreducible_pi_abelian_fixed_ne_bot (Fin N) (fun _ => GL (Fin 1) k) hcomm Y τ
    (fun _ => GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) hτ hfix
  let H : Subgroup (Levi k fun _ : Fin N => Fin 1) :=
    Subgroup.pi Set.univ fun _ => GlobalTheory.CentralExponent.cong (Fin 1) γ hγ
  have hH : IsCompact (H : Set (Levi k fun _ : Fin N => Fin 1)) :=
    isCompact_univ_pi fun _ => GlobalTheory.CentralExponent.isCompact_cong γ hγ
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ
  obtain ⟨v, hv⟩ := exists_ne (0 : Y)
  have hτf : fixed τ H ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v, fun g => by
    rw [htriv g.1 fun a => g.2 a trivial]
    simp, hv⟩
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 (UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact _ _ _ τ (jac e π) H hjs hτs hH hτf)
  refine ⟨w, hw0, fun g hg => ?_⟩
  simpa using hw ⟨g, fun a _ => hg a⟩
