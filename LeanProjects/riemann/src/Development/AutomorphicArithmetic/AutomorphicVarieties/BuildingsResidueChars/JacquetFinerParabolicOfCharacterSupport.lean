import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRefinementBlockOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneUnipotentMonodromy

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_finer_parabolic_of_character_support :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL k)), HasSupport π s → (∀ y ∈ s, y.1 = 1) →
    ∀ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N) (j : Fin r), 2 ≤ d j → Nontrivial (Jacquet π (unipRad k e)) →
    ∃ (t : ℕ) (c : Fin t → ℕ) (f : (Σ a, Fin (c a)) ≃ Fin N), Nontrivial (Jacquet π (unipRad k f)) ∧
      (∀ p q, blk e p < blk e q → blk f p < blk f q) ∧ ∃ p q, blk f p < blk f q ∧ ¬ blk e p < blk e q := by
  intro hG hZ k _ _ _ _ N V _ _ π s hs hs1 r d e j hj hJ
  have hπ : IsSmooth π := by
    obtain ⟨h, x, -, hi, hc, e, hsub⟩ := hs
    exact hsub.isSmooth (isSmooth_parInd _ _)
  have hJs : IsSmooth (jac e π) := isSmooth_jac e hπ
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e π) hJ
  have hτsm : IsSmooth τ := hτs.isSmooth hJs
  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
      (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
    exact ⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _
      (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
  choose y hy using hy
  obtain ⟨u, hu, rfl⟩ := SupportUnique.exists_sum_of_jac hG hZ hs e hτ hτs y hy
  have hnc : ¬ IsCuspidal (IrrGL.of (y j).ρ (y j).smooth (y j).irr).rep := by
    intro hc
    have hx : (IrrGL.of (y j).ρ (y j).smooth (y j).irr).IsCusp := ⟨show 0 < d j by omega, hc⟩
    have h1 := SupportUnique.eq_singleton_of_isCusp hx ((hu j).of_equiv (IrrGL.equivOf _ _ _))
    have h2 : IrrGL.of (y j).ρ (y j).smooth (y j).irr ∈ ∑ i, u i :=
      Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h1 ▸ Multiset.mem_singleton_self _⟩
    have h3 : d j = 1 := hs1 _ h2
    omega
  obtain ⟨r', d', e', hU, hJ'⟩ : ∃ (r' : ℕ) (d' : Fin r' → ℕ) (e' : (Σ a, Fin (d' a)) ≃ Fin (d j)),
      unipRad k e' ≠ ⊥ ∧
      ¬ Subsingleton (Jacquet (IrrGL.of (y j).ρ (y j).smooth (y j).irr).rep (unipRad k e')) := by
    by_contra! hn
    exact hnc ⟨(IrrGL.of (y j).ρ (y j).smooth (y j).irr).2.rep.smooth, hn⟩
  obtain ⟨t, c, f, hf⟩ := UpperTheory.exists_refinement_block_order N r r' d e j d' e'
  refine ⟨t, c, f, ?_, fun p q h => (hf p q).2 (Or.inl h), ?_⟩
  · by_contra hn
    have h0 := UpperTheory.weilDeligne_unipotent_monodromy k N V π r r' d e j d' e' t c f (fun p q => (hf p q).1)
      (not_nontrivial_iff_subsingleton.1 hn)
    let φ := (IrrGL.equivOf (y j).ρ (y j).smooth (y j).irr).symm
    have h1 : IsSubquotient (IrrGL.of (y j).ρ (y j).smooth (y j).irr).rep (y j).ρ :=
      .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective
    have h2 := (h1.trans (hy j)).trans (SupportUnique.isSubquotient_comp hτs
      (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
    obtain ⟨S, g, hg⟩ := GlobalTheory.JacquetExact.isSubquotient_jac e' (isSmooth_comp hJs _
      (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)) h2
    haveI : Subsingleton S.toSubmodule := ⟨fun a b => Subtype.ext (h0.elim _ _)⟩
    exact hJ' (Function.Surjective.subsingleton hg)
  · obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
    refine ⟨e ⟨j, p⟩, e ⟨j, q⟩, (hf _ _).2 (Or.inr ⟨p, q, rfl, rfl, hpq⟩), ?_⟩
    rw [blk_apply, blk_apply]
    exact lt_irrefl _
