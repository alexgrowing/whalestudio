import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer

namespace ReciprocityTheory.AnForm.R

open MvPolynomial IsLocalRing

def jacSpanAt {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Submodule ℂ (σ → ℂ) :=
  Submodule.span ℂ ((fun h : MvPolynomial σ ℂ => fun j => eval z (pderiv j h)) '' (I : Set _))

theorem locAt_isLocalRing_isNoetherian {σ : Type} [Finite σ] (I : Ideal (MvPolynomial σ ℂ))
    (z : σ → ℂ) (hz : ∀ h ∈ I, eval z h = 0) :
    IsLocalRing (locAt I z) ∧ IsNoetherianRing (locAt I z) := by
  haveI := Fintype.ofFinite σ
  have hle : I ≤ ptIdealOf z := fun h hh => by
    show h ∈ RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)
    exact hz h hh
  have hne : Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z))) I ≠ ⊤ := by
    intro htop
    have h1 : Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)))
        (ptIdealOf z) = ⊤ := top_unique (htop ▸ Ideal.map_mono hle)
    rw [Localization.AtPrime.map_eq_maximalIdeal] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  haveI : Nontrivial (locAt I z) := Ideal.Quotient.nontrivial_iff.2 hne
  exact ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, inferInstance⟩

theorem grad_renC {σ : Type} [Fintype σ] (z : σ → ℂ) (h : MvPolynomial σ ℂ) :
    grad (renPt z) (renC σ h) = fun j => eval z (pderiv ((Fintype.equivFin σ).symm j) h) := by
  funext j
  simp only [grad, renC, renameEquiv_apply]
  conv_lhs => rw [← Equiv.apply_symm_apply (Fintype.equivFin σ) j]
  rw [pderiv_rename (Equiv.injective _), eval_rename]
  have hc : renPt z ∘ (Fintype.equivFin σ) = z := by
    funext i
    simp [renPt]
  rw [hc]

theorem finrank_jacSpanAt_eq {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) :
    Module.finrank ℂ (jacSpanAt I z) =
      Module.finrank ℂ (jacSpan (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) := by
  let L : (σ → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card σ) → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm
  have hset : grad (renPt z) '' ((I.map (renR σ : MvPolynomial σ ℂ →+* MvPolynomial (Fin (Fintype.card σ)) ℂ) :
      Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ)) : Set (MvPolynomial (Fin (Fintype.card σ)) ℂ)) =
      (L : (σ → ℂ) →ₗ[ℂ] _) '' ((fun h : MvPolynomial σ ℂ => fun j => eval z (pderiv j h)) '' (I : Set _)) := by
    ext v
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨h, hh, rfl⟩ := (Ideal.mem_map_of_equiv (renR σ) q).1 hq
      refine ⟨_, ⟨h, hh, rfl⟩, ?_⟩
      funext j
      rw [show (renR σ) h = renC σ h from rfl, grad_renC]
      rfl
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨renR σ h, Ideal.mem_map_of_mem _ hh, ?_⟩
      funext j
      rw [show (renR σ) h = renC σ h from rfl, grad_renC]
      rfl
  unfold jacSpan jacSpanAt
  rw [hset, Submodule.span_image]
  exact (LinearEquiv.finrank_map_eq L _).symm

theorem finrank_cotangentSpace_locAt {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ))
    (z : σ → ℂ) [IsLocalRing (locAt I z)] :
    Module.finrank (ResidueField (locAt I z)) (CotangentSpace (locAt I z))
      + Module.finrank ℂ (jacSpanAt I z) = Fintype.card σ := by
  haveI : IsNoetherianRing (locAt I z) := inferInstance
  haveI : Nontrivial (locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) :=
    (locAtEquiv I z).symm.toEquiv.nontrivial
  haveI : IsLocalRing (locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) :=
    IsLocalRing.of_surjective' (locAtEquiv I z).toRingHom (locAtEquiv I z).surjective
  haveI : IsNoetherianRing (locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) :=
    isNoetherianRing_of_ringEquiv _ (locAtEquiv I z)
  rw [finrank_cotangentSpace_eq_of_ringEquiv (locAtEquiv I z), finrank_jacSpanAt_eq,
    finrank_cotangentSpace_locRing]

end ReciprocityTheory.AnForm.R
