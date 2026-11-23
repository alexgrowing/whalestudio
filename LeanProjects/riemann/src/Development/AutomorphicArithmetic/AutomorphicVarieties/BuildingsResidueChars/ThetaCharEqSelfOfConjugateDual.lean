import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem conjSrc_eq {E : Type} [Field E] [NumberField E] (τ : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc τ w = preplace τ w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))

private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : G (maximalRealSubfield F) Ω} (hc : Af.IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)

theorem UpperTheory.thetaChar_eq_self_of_conjugate_dual :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (κ : HChar E) (m : ℕ), 0 < m → κ.OrderDvd m → ∀ β : G E Ω →* (Qbar l)ˣ, Continuous β → IsLAdicOf art ι κ 0 β → ∀ c : G (maximalRealSubfield E) Ω, Af.IsConjEl c → (∀ s s' : G E Ω, s'.restrictScalars (maximalRealSubfield E) = c * s.restrictScalars (maximalRealSubfield E) * c⁻¹ → β s' = (β s)⁻¹) → GlobalTheory.ThetaPull.thetaChar κ = κ := by
  intro E Ω _ _ _ _ _ _ l _ ι art ha κ m _ _ β _ hL c hc hβ
  have hLi := isLift_conj hc
  have hval : ∀ v, κ.UnrAt v → κ.UnrAt (conjSrc (IsCMField.complexConj E).toRingEquiv v) →
      κ.val (conjSrc (IsCMField.complexConj E).toRingEquiv v) = (κ.val v)⁻¹ := by
    intro v hv hv'
    rw [conjSrc_eq] at hv' ⊢
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
    have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
    have e1 := hL.frob_unr ha (Or.inr rfl) hv hA hσ
    have e2 := hL.frob_unr ha (Or.inr rfl) hv' (isPlaceOver_preplace hLi hAA hA) (σ := conjGal hLi σ)
      (by rw [normV_preplace]; exact isFrob_conjGal hLi hAA hσ)
    rw [hβ σ (conjGal hLi σ) (AlgEquiv.ext fun _ => rfl), Units.val_inv_eq_inv_val, e1, inv_inj, ← map_inv₀] at e2
    exact Units.ext (by rw [Units.val_inv_eq_inv_val]; exact (ι.symm.injective e2).symm)
  have hu := GlobalTheory.GalChar.unr_ae κ
  have hu' := (Function.LeftInverse.injective (GlobalTheory.ThetaPull.conjSrc_conjSrc (E := E))).tendsto_cofinite.eventually hu
  have hS := Filter.eventually_cofinite.1 (hu.and hu')
  have h : (GlobalTheory.ThetaPull.thetaChar κ).1 * κ.1⁻¹ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away _ ((GlobalTheory.ThetaPull.thetaChar κ).2.1.mul κ.2.1.inv) (fun k => ?_) hS.toFinset
      fun v hv => ?_
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, κ.2.2, (GlobalTheory.ThetaPull.thetaChar κ).2.2, inv_one, one_mul]
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
      obtain ⟨v, rfl⟩ : ∃ v', conjSrc (IsCMField.complexConj E).toRingEquiv v' = v := ⟨_, GlobalTheory.ThetaPull.conjSrc_conjSrc v⟩
      rw [GlobalTheory.ThetaPull.conjSrc_conjSrc] at hv
      refine GlobalTheory.FrobDense.eq_one_of_unif (((GlobalTheory.ThetaPull.thetaChar κ).1 * κ.1⁻¹).comp (localIdele E _)) fun y hy => ?_
      have hy' : IsUnifAt v (Units.map (conjLoc _ v).toMonoidHom y) := ((conjLoc_spec _ v).2.2 y.val).trans hy
      have h1 : κ.1 (localIdele E _ y) = κ.val _ := κ.val_eq hv.1 y hy
      have h2 : κ.1 (localIdele E v _) = κ.val v := κ.val_eq hv.2 _ hy'
      rw [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, GlobalTheory.ThetaPull.thetaChar_apply,
        GlobalTheory.ThetaPull.conjAd_localIdele, h1, h2, hval v hv.2 hv.1, mul_inv_cancel]
  exact Subtype.ext (mul_inv_eq_one.1 h)
