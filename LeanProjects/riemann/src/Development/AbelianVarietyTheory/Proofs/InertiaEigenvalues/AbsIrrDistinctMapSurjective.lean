import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem absIrrDistinct_of_semilinearEquiv {k L Γ V V' : Type} [Field k] [Field L] [Group Γ]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module L V']
    {σ : k →+* L} {τ : L →+* k} [RingHomInvPair σ τ] [RingHomInvPair τ σ]
    (ρ : Representation k Γ V) (ρ' : Representation L Γ V') (E : V ≃ₛₗ[σ] V')
    (hE : ∀ g v, E (ρ g v) = ρ' g (E v)) (h : AbsIrrDistinct ρ) : AbsIrrDistinct ρ' := by
  obtain ⟨ι, hι, hd, Vs, hs, hint, hne, hspan, hdist⟩ := h
  have hs' : ∀ j, Stable ρ' ((Vs j).map (E : V →ₛₗ[σ] V')) := by
    rintro j g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hs j g v hv, hE g v⟩
  have hcomm : ∀ j g (v : Vs j), E.submoduleMap (Vs j) ((ρ g).restrict (hs j g) v)
      = (ρ' g).restrict (hs' j g) (E.submoduleMap (Vs j) v) := by
    intro j g v
    apply Subtype.ext
    exact hE g v
  refine ⟨ι, hι, hd, fun j => (Vs j).map (E : V →ₛₗ[σ] V'), hs', ?_, ?_, ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
    refine ⟨hint.1.map_orderIso (Submodule.orderIsoMapComap E), ?_⟩
    rw [← Submodule.map_iSup, hint.2, Submodule.map_top, LinearEquiv.range]
  · intro j hj
    exact hne j ((Submodule.orderIsoMapComap E).injective (by simpa using hj))
  · intro j
    have hc : ∀ g, (E.submoduleMap (Vs j)).conj ((ρ g).restrict (hs j g))
        = (ρ' g).restrict (hs' j g) := by
      intro g
      ext1 w
      obtain ⟨v, rfl⟩ := (E.submoduleMap (Vs j)).surjective w
      rw [← hcomm]
      simp [LinearEquiv.conj_apply]
    have h1 := congrArg (Submodule.map ((E.submoduleMap (Vs j)).conj : Module.End k (Vs j) →ₛₗ[σ]
      Module.End L ((Vs j).map (E : V →ₛₗ[σ] V')))) (hspan j)
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at h1
    rw [← h1]
    congr 2
    funext g
    exact (hc g).symm
  · intro j j' hjj e he
    refine hdist j j' hjj
      (((E.submoduleMap (Vs j)).trans e).trans (E.submoduleMap (Vs j')).symm) ?_
    intro g v
    apply (E.submoduleMap (Vs j')).injective
    rw [hcomm]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [hcomm, he]

theorem absIrrDistinct_matRep_mapM_of_surjective : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L), Function.Surjective f → ∀ {a : ℕ} (M : Γ →* Matrix (Fin a) (Fin a) k), AbsIrrDistinct (matRep M) → AbsIrrDistinct (matRep (mapM f M)) := by
  intro k Γ _ _ L _ f hf a M h
  let s : k ≃+* L := RingEquiv.ofBijective f ⟨f.injective, hf⟩
  haveI := RingHomInvPair.of_ringEquiv s
  haveI := RingHomInvPair.of_ringEquiv_symm s
  let E : (Fin a → k) ≃ₛₗ[(s : k →+* L)] (Fin a → L) :=
    { toFun := fun v i => s (v i)
      invFun := fun v i => s.symm (v i)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun c v => by ext i; simp
      left_inv := fun v => by ext i; simp
      right_inv := fun v => by ext i; simp }
  refine absIrrDistinct_of_semilinearEquiv _ _ E ?_ h
  intro g v
  ext i
  exact RingHom.map_mulVec f (M g) v i

end GlobalTheory
