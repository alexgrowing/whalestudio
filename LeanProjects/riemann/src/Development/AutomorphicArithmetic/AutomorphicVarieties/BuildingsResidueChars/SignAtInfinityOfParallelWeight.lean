import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

open ReciprocityTheory.Neutral.Bridge.HCFR

private theorem UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal {F : Type} [Field F] [NumberField F] (a : (F →+* ℂ) → ℤ)
    (a0 : ℤ) (ha : ∀ φ, a φ = a0) (w : InfinitePlace F) (hw : w.IsReal) :
    infPow a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = (-1) ^ a0 := by
  have hcont : Continuous (Complex.ofRealHom.comp
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)) :=
    Complex.continuous_ofReal.comp
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  let i0 : {i : w.Completion →+* ℂ // Continuous i} := ⟨_, hcont⟩
  have huniq : ∀ i : {i : w.Completion →+* ℂ // Continuous i}, i = i0 := by
    intro i
    apply Subtype.ext
    ext x
    let E := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let g : ℝ →+* ℂ := (i : w.Completion →+* ℂ).comp
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
    have hg : Continuous g := i.2.comp E.symm.continuous
    have hg' := Complex.ringHom_eq_ofReal_of_continuous hg
    have hx : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
        (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x) = x :=
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm_apply_apply x
    have := congrArg (fun f : ℝ →+* ℂ => f
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x)) hg'
    simp only [g, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hx] at this
    simpa [i0] using this
  unfold infPow
  rw [Finset.prod_eq_single w]
  · rw [finprod_eq_single _ i0 (fun j hj => absurd (huniq j) hj)]
    rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self, ha]
    simp
  · intro w' _ hne
    simp [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne F w w' hne]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem UpperTheory.sign_at_infinity_of_parallel_weight :
    UpperTheory.V.Af.Sol.Parallel → UpperTheory.V.Af.Sol.SignOf := by
  intro hP F Ω _ _ _ _ _ _ l _ ι χ μ hμ hs v v'
  obtain ⟨-, art, a, hart, halg, hlad⟩ := hμ
  have hpar := hP F χ a halg
  have key : ∀ w : InfinitePlace F, ∃ c : G F Ω, IsConjEl c ∧
      ((χ.locInf w (-1) : ℂˣ) : ℂ) = ι (μ c) * (-1) ^ (a v.embedding) := by
    intro w
    obtain ⟨j, c, hc, hw⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) w
      (NumberField.IsTotallyReal.isReal w)
    refine ⟨c, ⟨j, hc⟩, ?_⟩
    have hart' := GlobalTheory.HilbertFromArtin.art_sign_eq hart j c hc
    rw [hw] at hart'
    have h := hlad _ c hart'
    have hl : lPow ι a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = 1 := by
      simp [GlobalTheory.HeckeGal.lPow, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_snd, GlobalTheory.HeckeGal.locPow_one]
    rw [hl, mul_one, UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal a (a v.embedding) (fun φ => hpar φ v.embedding) w
      (NumberField.IsTotallyReal.isReal w)] at h
    have h2 := congrArg ι h
    rw [RingEquiv.apply_symm_apply] at h2
    rw [h2]
    have hne : ((-1 : ℂ) ^ (a v.embedding)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
    rfl
  obtain ⟨c, hc, hcv⟩ := key v
  obtain ⟨c', hc', hcv'⟩ := key v'
  apply Units.ext
  rw [hcv, hcv', hs c c' hc hc']
