import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem UpperTheory.V.LDataCardLeFinrank.transport_mem_NS
    {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {F' Ω' : Type} [Field F']
    [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] {l : ℕ} [Fact l.Prime] (f : F →+* F')
    (σ : Ω ≃+* Ω') (hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) (φ : G F' Ω' →* G F Ω)
    (h1 : Continuous φ) (h2 : ∀ g x, σ (φ g x) = g (σ x))
    {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S = Above F l) {S' : Set (HeightOneSpectrum (𝓞 F'))}
    (hS' : S' = Above F' l) : NS Ω' S' ≤ (NS Ω S).comap φ := by
  have hN : (NS Ω S).Normal := Subgroup.is_normal_topologicalClosure _
  have hclosed : IsClosed ((NS Ω S).comap φ : Set (G F' Ω')) := (isClosed_NS Ω S).preimage h1
  haveI : ((NS Ω S).comap φ).Normal := hN.comap φ
  apply Subgroup.topologicalClosure_minimal _ _ hclosed
  apply Subgroup.normalClosure_le_normal
  intro g hg
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq] at hg
  obtain ⟨v', hv', A', hA', hgA⟩ := hg
  obtain ⟨v, A, hA, habove, -, -, hine⟩ := placeTransport F Ω F' Ω' f σ hσ φ h2 v' A' hA'
  have hgi : φ g ∈ Ine A := (hine g).2 hgA
  show φ g ∈ NS Ω S
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq]
  refine ⟨v, ?_, A, hA, hgi⟩
  rw [hS]
  rw [hS'] at hv'
  exact fun h => hv' ((habove l).1 h)

theorem UpperTheory.V.LDataCardLeFinrank.gsTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (D' : LData F' Ω' l) (f : F ≃+* F') (σ : Ω ≃+* Ω'), (∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) →
      ∃ (φ : G F' Ω' ≃* G F Ω) (ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) ≃* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))),
        Continuous φ ∧ Continuous φ.symm ∧ Continuous ψ ∧ Continuous ψ.symm ∧ (∀ g x, σ (φ g x) = g (σ x)) ∧
        (∀ g, ψ (toGS Ω' _ g) = toGS Ω _ (φ g)) ∧ ∀ g, D.chi (ψ g) = D'.chi g := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ l _ D D' f σ hσ
  obtain ⟨φ, hφc, hφact, hφcyc, -, -⟩ := galTransport F Ω F' Ω' (f : F →+* F') σ hσ
  have hσ' : ∀ x : F', σ.symm (algebraMap F' Ω' x) = algebraMap F Ω ((f.symm : F' →+* F) x) := by
    intro x
    apply σ.injective
    rw [RingEquiv.apply_symm_apply, hσ]
    simp
  obtain ⟨φ', hφ'c, hφ'act, -, -, -⟩ := galTransport F' Ω' F Ω (f.symm : F' →+* F) σ.symm hσ'
  have hleft : ∀ g, φ' (φ g) = g := by
    intro g
    refine AlgEquiv.ext fun y => ?_
    apply σ.symm.injective
    rw [hφ'act]
    apply σ.injective
    rw [hφact, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hright : ∀ g, φ (φ' g) = g := by
    intro g
    refine AlgEquiv.ext fun x => ?_
    apply σ.injective
    rw [hφact]
    apply σ.symm.injective
    rw [hφ'act, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  let Φ : G F' Ω' ≃* G F Ω :=
    { toFun := φ, invFun := φ', left_inv := hleft, right_inv := hright, map_mul' := φ.map_mul }
  haveI : (NS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F')))).Normal :=
    Subgroup.is_normal_topologicalClosure _
  haveI : (NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))).Normal :=
    Subgroup.is_normal_topologicalClosure _
  have hmap : (NS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F')))).map (Φ : G F' Ω' →* G F Ω) =
      NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact UpperTheory.V.LDataCardLeFinrank.transport_mem_NS (f : F →+* F') σ hσ φ hφc hφact D.hS D'.hS
    · intro h hh
      refine ⟨φ' h, ?_, hright h⟩
      exact UpperTheory.V.LDataCardLeFinrank.transport_mem_NS (f.symm : F' →+* F) σ.symm hσ' φ' hφ'c hφ'act D'.hS D.hS hh
  let Ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) ≃* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
    QuotientGroup.congr _ _ Φ hmap
  have hΨmk : ∀ g : G F' Ω', Ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) :=
    fun g => QuotientGroup.congr_mk _ _ Φ hmap g
  have hΨsmk : ∀ g : G F Ω, Ψ.symm (QuotientGroup.mk g) = QuotientGroup.mk (φ' g) := by
    intro g
    apply Ψ.injective
    rw [MulEquiv.apply_symm_apply, hΨmk, hright]
  have hΨc : Continuous Ψ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (Ψ ∘ QuotientGroup.mk) = (QuotientGroup.mk ∘ φ) := funext hΨmk
    rw [this]
    exact QuotientGroup.continuous_mk.comp hφc
  have hΨsc : Continuous Ψ.symm := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (Ψ.symm ∘ QuotientGroup.mk) = (QuotientGroup.mk ∘ φ') := funext hΨsmk
    rw [this]
    exact QuotientGroup.continuous_mk.comp hφ'c
  refine ⟨Φ, Ψ, hφc, hφ'c, hΨc, hΨsc, hφact, fun g => hΨmk g, ?_⟩
  intro g
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  rw [hΨmk]
  show D.chi (toGS Ω _ (φ h)) = D'.chi (toGS Ω' _ h)
  have e1 : D.chi (toGS Ω _ (φ h)) = cycZ F Ω l (φ h) := by
    rw [← D.hchi]
    rfl
  have e2 : D'.chi (toGS Ω' _ h) = cycZ F' Ω' l h := by
    rw [← D'.hchi]
    rfl
  exact e1.trans ((hφcyc l h).trans e2.symm)
