import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.TanEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DerLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DimLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RegOfDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem rank_le_res {O A B K : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
    [Field K] [Algebra O K] (f : A →ₐ[O] B) (x : B →ₐ[O] K)
    (h : ∀ x' : B →ₐ[O] DualNumber K, (∀ b, (x' b).fst = x b) → (∀ a, (x' (f a)).snd = 0) → ∀ b, (x' b).snd = 0) :
    Module.rank K (PtDer x K) ≤ Module.rank K (PtDer (x.comp f) K) := by
  classical
  let F : PtDer x K →ₗ[K] PtDer (x.comp f) K :=
    { toFun := fun D => ⟨(D : B →ₗ[O] K).comp f.toLinearMap, by
        intro a a'
        have hD := D.2 (f a) (f a')
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, AlgHom.comp_apply]
        simpa using hD⟩
      map_add' := fun D E => by
        ext a
        simp
      map_smul' := fun c D => by
        ext a
        simp }
  refine LinearMap.rank_le_of_injective F ?_
  have key : ∀ G : PtDer x K, F G = 0 → G = 0 := by
    intro G hG
    have hmul : ∀ b b' : B, (G : B →ₗ[O] K) (b * b') = x b • (G : B →ₗ[O] K) b' + x b' • (G : B →ₗ[O] K) b :=
      G.2
    have h1 : (G : B →ₗ[O] K) 1 = 0 := by
      have := hmul 1 1
      simp only [map_one, one_smul, mul_one] at this
      have h2 : (G : B →ₗ[O] K) 1 + (G : B →ₗ[O] K) 1 = (G : B →ₗ[O] K) 1 + 0 := by
        rw [add_zero]; exact this.symm
      exact add_left_cancel h2
    have hc : ∀ r : O, (G : B →ₗ[O] K) (algebraMap O B r) = 0 := by
      intro r
      rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
    have halg : ∀ r : O, algebraMap O (DualNumber K) r = TrivSqZeroExt.inl (algebraMap O K r) := fun r => rfl
    let y : B →ₐ[O] DualNumber K :=
      { toFun := fun b => TrivSqZeroExt.inl (x b) + TrivSqZeroExt.inr ((G : B →ₗ[O] K) b)
        map_one' := by
          ext <;> simp [h1]
        map_mul' := fun b b' => by
          ext
          · simp
          · simp [hmul b b', smul_eq_mul, mul_comm, add_comm]
        map_zero' := by
          ext <;> simp
        map_add' := fun b b' => by
          ext <;> simp [add_comm, add_left_comm, add_assoc]
        commutes' := fun r => by
          rw [halg]
          ext
          · simp
          · simp [hc] }
    have hz := h y (fun b => by simp [y]) (fun a => by
      have := congrArg (fun H : PtDer (x.comp f) K => (H : A →ₗ[O] K) a) hG
      simpa [F, y] using this)
    ext b
    simpa [y] using hz b
  intro D E hDE
  have := key (D - E) (by rw [map_sub, hDE, sub_self])
  exact sub_eq_zero.1 this

theorem UpperTheory.V.Ws.Eb.regOfTan :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] B) (J : Ideal B), ((Ideal.Quotient.mk J).comp (f : MvPowerSeries (Fin N) c.O →+* B)).Finite → (∀ a, a ≠ 0 → ∀ b, f a * b ∈ J → b ∈ J) →
        ∀ x : B →ₐ[c.O] PadicAlgCl l, J ≤ RingHom.ker x → (∀ x' : B →ₐ[c.O] DualNumber (PadicAlgCl l), (∀ b, (x' b).fst = x b) → (∀ a, (x' (f a)).snd = 0) → ∀ b, (x' b).snd = 0) → ∀ q : Ideal B, q.IsPrime → q ≤ RingHom.ker x → J ≤ q := by
  intro l _ c N B _ _ _ f J hfin hreg x hJ htan q hq hqx
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l])).2 inferInstance
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) (UpperTheory.V.Base.dvrFacts l c.O).1
  haveI : FaithfulSMul c.O (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI hp : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  have h1 := tanEmb c.O B (PadicAlgCl l) x (RingHom.ker x) rfl N
    ((rank_le_res f x htan).trans (derLam c N (x.comp f)))
  have h2 := dimLow c N B f J hfin hreg x (RingHom.ker x) rfl hJ
  have hne : J.map (algebraMap B (Localization.AtPrime (RingHom.ker x))) ≠ ⊤ := by
    intro ht
    have := Ideal.map_mono (f := algebraMap B (Localization.AtPrime (RingHom.ker x))) hJ
    rw [ht, Localization.AtPrime.map_eq_maximalIdeal] at this
    exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.1 this)
  have h3 := UpperTheory.V.AlgebraTools.regOfDim _ _ hne (le_trans (by exact_mod_cast h1) h2)
  intro a ha
  have h4 : algebraMap B (Localization.AtPrime (RingHom.ker x)) a = 0 := by
    have := Ideal.mem_map_of_mem (algebraMap B (Localization.AtPrime (RingHom.ker x))) ha
    rw [h3] at this
    exact this
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (RingHom.ker x).primeCompl _ a).1 h4
  have h5 : (s : B) * a ∈ q := by rw [hs]; exact q.zero_mem
  exact (hq.mem_or_mem h5).resolve_left fun h => s.2 (hqx h)
