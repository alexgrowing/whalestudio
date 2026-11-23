import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralLatOfForall
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalFactorEquality

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits

theorem finite_vF_ne_zero {n : 𝓞 F} (hn : n ≠ 0) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | vF 𝔭.1 n ≠ 0}.Finite := by
  have hnF : ¬ IsField (𝓞 F) := NumberField.RingOfIntegers.not_isField F
  have hI : Ideal.span {n} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  let f : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    fun 𝔭 => ⟨𝔭.1, 𝔭.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 hnF⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h)
  refine ((Ideal.finite_factors hI).preimage hf.injOn).subset ?_
  intro 𝔭 h𝔭
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at h𝔭 ⊢
  show 𝔭.1 ∣ Ideal.span {n}
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply h𝔭
  unfold vF

  have hset : {e : ℕ | n ∈ 𝔭.1 ^ e} = {0} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro he
      by_contra h0
      exact hmem (Ideal.pow_le_self h0 he)
    · rintro rfl
      simp
  rw [hset, csSup_singleton]

theorem psiP_eq (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (hex : ∃ s, IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ hex.choose, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  unfold psiP
  rw [dif_pos hex]

theorem psiP_eq_zero (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (H : ∀ T, fibLoc S L 𝔭 T = 0) : psiP S L 𝔭 = 0 := by
  unfold psiP
  split_ifs with hs
  · simp [H]
  · rfl

theorem card_fibG_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsLattice K Λ') (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (H : fibLoc S L 𝔭.1 Λ' = 0) : (Nat.card (fibG S L Λ') : ℝ) = 0 := by
  rw [card_fibG_eq_prod hK hF hs hd S hL hLi hΛ']
  exact tprod_of_exists_eq_zero ⟨𝔭, by rw [H]; simp⟩

theorem isLattice_of_fibReps (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s') {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Λ' ∈ s') : Submodule.IsLattice K Λ' := by
  obtain ⟨Λ, hΛ, -, rfl⟩ := hs'.1 Λ' hΛ'
  exact StabilizerLattices.isLattice_cut S hΛ.1

theorem exists_norm_eq (hF : IsFixF K F) (hs : h.IsSymm) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∃ T, fibLoc S L 𝔭.1 T ≠ 0) :
    ∃ n : 𝓞 F, h S.x₀ S.x₀ = algebraMap F K (n : F) := by

  have hloc : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      h S.x₀ S.x₀ ∈ locF 𝔭.1 (1 : Submodule (𝓞 K) K) := by
    intro 𝔭
    obtain ⟨T, hT⟩ := H 𝔭
    obtain ⟨g, hg, hx, -⟩ := UnimodularLocalization.exists_of_fibLoc_ne_zero S hT
    exact GoodPrimeTerms.isIntegralAt_locF 𝔭.2.isPrime hF (UnimodularLocalization.isIntegralLat_gmap hg hLi) _ hx _ hx
  have h1 : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K)]
    exact Submodule.mem_iInf _ |>.mpr hloc
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp h1

  have hc : conjO K y = y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [BallB.algebraMap_conjO, hy]
    simpa [starRingEnd_apply] using hs.eq S.x₀ S.x₀
  obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF y).mp hc
  exact ⟨t, by rw [← hy, ← ht]; rfl⟩

open Classical in

theorem sum_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {A : Submodule (𝓞 K) V'} (hA : Submodule.IsLattice K A) (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h' A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hZ1 : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A = 1) (hZ2 : ∀ 𝔭 ∉ Z, vd h' A 𝔭.1 = 0)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) (hMA : ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A) :
    ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'),
        (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
      c * ∏ 𝔭 ∈ Z, ((fibLoc S L 𝔭.1 (locF 𝔭.1 M) : ℝ) * lamP h' (locF 𝔭.1 M) 𝔭.1) := by
  have hs2 := S.isSymm hs
  have hd2 := S.isTotPosDef hd
  have hMi := hM.integral hF hL hLi
  have hmass : Formalism.HermitianLatticesTheory.mass h' M = ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'),
      ((Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℕ) : ℝ)⁻¹ :=
    (Formalism.HermitianLatticesTheory.massBasic K V' h' hs2 (StabilizerLattices.trace_pos hd2) M hM.1).2.1 _
      (isClassReps_filter hK hF hs hd S hL hLi hs' hM)
  have hfr : finrank K V' = finrank K V - 1 := by
    have := S.finrank_add_one
    omega
  have hmc := hc V' h' M hs2 hd2 hfr hM.1 hMi
  have e1 : ∀ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'),
      (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
        (∏ 𝔭 ∈ Z, (fibLoc S L 𝔭.1 (locF 𝔭.1 M) : ℝ)) *
          ((Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℕ) : ℝ)⁻¹ := by
    intro Λ' hΛ'
    rw [Finset.mem_filter] at hΛ'
    rw [card_fibG_eq_prod (F := F) hK hF hs hd S hL hLi (isLattice_of_fibReps S hs' hΛ'.1),
      div_eq_mul_inv]
    congr 1
    have e2 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        fibLoc S L 𝔭.1 Λ' = fibLoc S L 𝔭.1 (locF 𝔭.1 M) := fun 𝔭 => by
      rw [fibLoc_eq_of_rel hs S L ((sameGenus_iff hK hF M Λ').mp hΛ'.2 𝔭), fibLoc_locF]
    simp only [e2]
    apply tprod_eq_prod
    intro 𝔭 h𝔭
    rw [fibLoc_locF, fibLoc_congr S L (hMA 𝔭 h𝔭), hZ1 𝔭 h𝔭, Nat.cast_one]
  rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, ← hmass, hmc, Finset.prod_mul_distrib]
  have e3 : lamG F h' M = ∏ 𝔭 ∈ Z, lamP h' (locF 𝔭.1 M) 𝔭.1 := by
    unfold lamG
    have e4 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        lamP h' M 𝔭.1 = lamP h' (locF 𝔭.1 M) 𝔭.1 := fun 𝔭 =>
      (localFactor_localField hK hF hs2 hd2 hM.1 hMi 𝔭.2).symm
    simp only [e4]
    apply tprod_eq_prod
    intro 𝔭 h𝔭
    rw [hMA 𝔭 h𝔭, localFactor_localField hK hF hs2 hd2 hA hAi 𝔭.2]
    exact localMassFactor_of_valuation_eq_zero hK hF hs2 hd2 hA hAi 𝔭.2 (hZ2 𝔭 h𝔭)
  rw [e3]
  ring

end Formalism.HermitianLattices.Ext.L3.LocalFactorEquality
