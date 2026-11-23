import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.TwMapEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.TwMapUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.TwChOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.ClosedJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LcOfKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.PhiTw

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open UpperTheory.V.Ws.H5 in
theorem UpperTheory.V.Ws.h5 :
    UIn → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.Modular ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ (n : ℕ) (φ' : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ' → J₀.map φ' = J := by
  intro _ Ω _ _ _ l _ c D T _ _ c' h K X B Λ ι J₀ hM φ hφ J hJ n φ' hφ'
  subst hJ
  have hl : ((l : ℕ) : B.B) ∈ maximalIdeal B.B := by
    haveI := (UpperTheory.V.Base.dvrFacts l c'.O).2.2.1
    have h1 : ((l : ℕ) : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    have h2 := map_nonunit (algebraMap c'.O B.B) _ (map_nonunit (algebraMap ℤ_[l] c'.O) _ h1)
    simpa using h2
  have stab : ∀ γ : K.V.frame.G₀ →* B.Bˣ, TwCh K.V.frame γ → ∃ τ : B.B →ₐ[c'.O] B.B,
      TwMap B (RingHom.id B.B) (τ : B.B →+* B.B) γ ∧ ∀ b ∈ J₀, τ b ∈ J₀ := fun γ hγ => by
    obtain ⟨τ, hτ⟩ := twMapEx B (AlgHom.id c'.O B.B) γ hγ
    exact ⟨τ, hτ, fun b hb => closedJ _ J₀ _ (twJN B J₀ hM.dense hM.twist hl γ hγ τ hτ b hb)⟩
  have key : ∀ (γ : K.V.frame.G₀ →* c'.Oˣ), TwCh K.V.frame γ → ∀ f f' : B.B →ₐ[c'.O] X.B,
      TwMap B (f : B.B →+* X.B) (f' : B.B →+* X.B) (W.pushCh (algebraMap c'.O X.B) γ) → J₀.map f' ≤ J₀.map f := by
    intro γ hγ f f' hf
    obtain ⟨τ, hτ, hτJ⟩ := stab _ ((twChOps _ γ hγ).2.2 B.B (algebraMap c'.O B.B) inferInstance)
    have h1 := hτ.comp (f : B.B →+* X.B)
    have h2 : W.pushCh (f : B.B →+* X.B) (W.pushCh (algebraMap c'.O B.B) γ) = W.pushCh (algebraMap c'.O X.B) γ :=
      MonoidHom.ext fun g => Units.ext (f.commutes _)
    rw [h2, RingHom.comp_id] at h1
    have h3 : f' = f.comp τ := twMapUniq B _ _ f' (f.comp τ) hf h1
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, h3]
    exact Ideal.mem_map_of_mem _ (hτJ b hb)
  obtain ⟨β₀, hβ, hβ'⟩ := descend K
  have hn := (twChOps _ β₀ hβ).1 n
  have hT := phiTw K X B β₀ hβ' n φ φ' hφ hφ'
  refine le_antisymm (key _ hn φ φ' hT) (key _ (twChOps _ _ hn).2.1 φ' φ ?_)
  have hu : ∀ g, algebraMap c'.O X.B (((β₀ ^ n)⁻¹ g : c'.Oˣ) : c'.O) * algebraMap c'.O X.B (((β₀ ^ n) g : c'.Oˣ) : c'.O) = 1 :=
    fun g => by rw [← map_mul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one, map_one]
  refine ⟨fun g i hi => ?_, fun v i g => ?_⟩
  · rw [hT.1 g i hi, ← mul_assoc, ← mul_pow]
    erw [hu g]
    rw [one_pow, one_mul]
  · rw [hT.2 v i g, mul_assoc, mul_comm (_ : X.B) ((W.pushCh _ (β₀ ^ n)⁻¹ _ : X.Bˣ) : X.B)]
    erw [hu]
    rw [mul_one]
