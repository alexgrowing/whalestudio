import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUnique
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagComparisonStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleChainStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifferenceStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.CkTransport

theorem mseg_restrict {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    {Ω : Type} [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) :
    mseg x (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.restrictChart s) ≠ 0 := by
  unfold mseg at hs ⊢
  rw [Finset.prod_ne_zero_iff] at hs ⊢
  intro k _
  exact hs (Sum.inl k) (Finset.mem_univ _)

theorem pull_transport (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module Ω V] {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁]
    (e : V ≃ₗ[Ω] V₁) (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁)
    (h : ∀ s, mseg x s ≠ 0 → ∀ v, e v ∈ F.lat s ↔ v ∈ E.lat s)
    (EB : ChartBundle O (mseg (joinCoord x z)) N V) (FB : ChartBundle O (mseg (joinCoord x z)) N V₁)
    (hE : IsPull O x z E EB) (hF : IsPull O x z F FB) :
    ∀ s, mseg (joinCoord x z) s ≠ 0 → ∀ v, e v ∈ FB.lat s ↔ v ∈ EB.lat s := by
  intro s hs v
  have hr := h _ (mseg_restrict x z s hs)
  have key : FB.lat s = (EB.lat s).map (e : V →+ V₁) := by
    rw [hE s hs, hF s hs, AddMonoidHom.map_closure]
    congr 1
    ext u
    constructor
    · rintro ⟨a, ha, t, ht, rfl⟩
      refine ⟨a • e.symm t, ⟨a, ha, e.symm t, (hr _).1 (by simpa using ht), rfl⟩, ?_⟩
      simp
    · rintro ⟨_, ⟨a, ha, t, ht, rfl⟩, rfl⟩
      exact ⟨a, ha, e t, (hr _).2 ht, by simp⟩
  rw [key]
  constructor
  · rintro ⟨u, hu, huv⟩
    have : u = v := e.injective huv
    exact this ▸ hu
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem frame_transport {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] {ι : K → Type} (y : (Σ k, ι k) → Ω) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module Ω V] {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁]
    (e : V ≃ₗ[Ω] V₁) (E : ChartBundle O (segreVec y) N V) (F : ChartBundle O (segreVec y) N V₁)
    (h : ∀ s, segreVec y s ≠ 0 → ∀ v, e v ∈ F.lat s ↔ v ∈ E.lat s)
    (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ) (hw : IsFlagFrame y E w b) :
    IsFlagFrame y F (w.map e) b := by
  refine ⟨fun c hc i => ?_⟩
  rw [← hw.graded c hc i]
  ext u
  constructor
  · rintro ⟨v, hv, h1, h2⟩
    refine ⟨e.symm v, (h c hc _).1 (by simpa using hv), ?_, ?_⟩
    · simpa using h1
    · simpa using h2
  · rintro ⟨v, hv, h1, h2⟩
    refine ⟨e v, (h c hc _).2 hv, ?_, ?_⟩
    · simpa using h1
    · simpa using h2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (e : V ≃ₗ[Ω] V₁) (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N V₁), SameGeneric O x E E' → (∀ s, mseg x s ≠ 0 → ∀ v, (e v ∈ F.lat s ↔ v ∈ E.lat s) ∧ (e v ∈ F'.lat s ↔ v ∈ E'.lat s)) → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N F F' k L Q = ck O x d N E E' k L Q) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N F G L Q a = rootNum O x d N E G L Q a) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hW N V _ _ V₁ _ _ e E E' F F' hEE' he
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hFF' : SameGeneric O x F F' := by
    intro s hs
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨c, hc, h⟩ := (hEE' s hs).1 (e.symm v) ((he s hs _).1.1 (by simpa using hv))
      exact ⟨c, hc, by simpa using (he s hs _).2.2 h⟩
    · obtain ⟨c, hc, h⟩ := (hEE' s hs).2 (e.symm v) ((he s hs _).2.1 (by simpa using hv))
      exact ⟨c, hc, by simpa using (he s hs _).1.2 h⟩
  have hEE : SameGeneric O x E E := fun s _ =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hW', hfn, hj⟩ :=
    GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hW N 1 V ![E, E'] (by
      intro j
      fin_cases j
      · exact hEE
      · exact hEE')
  have hp0 : IsPull O x z E (EB 0) := (hj 0).1
  have hp1 : IsPull O x z E' (EB 1) := (hj 1).1
  have hB : SameGeneric O (joinCoord x z) (EB 0) (EB 1) :=
    (GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) hp0 hp1).2.1 hEE'
  obtain ⟨-, f, g, hfp⟩ := GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d
    ((GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O _ d).1 hW').2 N V (EB 0) (EB 1) hB w w (b 0) (b 1) (hj 0).2 (hj 1).2
    (fun i j hij => by simp [Finsupp.single_apply, hij.ne])
  obtain ⟨FB, hF⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V₁ F).1 K' ι' z
  obtain ⟨FB', hF'⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V₁ F').1 K' ι' z
  have hfpF : IsFlagPair ϖ (joinCoord x z) FB FB' (w.map e) (w.map e) (b 0) (b 1) f g := by
    refine ⟨frame_transport _ e (EB 0) FB
        (pull_transport O x z e E F (fun s hs v => (he s hs v).1) _ _ hp0 hF) w _ hfp.flag,
      frame_transport _ e (EB 1) FB'
        (pull_transport O x z e E' F' (fun s hs v => (he s hs v).2) _ _ hp1 hF') w _ hfp.flag',
      fun i j hij => ?_, hfp.vertical, fun i => ?_⟩
    · rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg hij.ne]
    · have := hfp.generic i
      rw [Module.Basis.repr_self] at this ⊢
      exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hW N V E E' hEE' K' ι' z hW' hfn (EB 0) (EB 1)
    hp0 hp1 w w (b 0) (b 1) f g hfp
  obtain ⟨h3, h4⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hW N V₁ F F' hFF' K' ι' z hW' hfn FB FB'
    hF hF' (w.map e) (w.map e) (b 0) (b 1) f g hfpF
  refine ⟨fun k hk hkd q L Q hQ => ?_, fun c G hG hc hcd q L Q hQ a ha => ?_⟩
  · rw [h1 k hk hkd q L Q hQ, h3 k hk hkd q L Q hQ]
  · rw [h2 c G hG hc hcd q L Q hQ a ha, h4 c G hG hc hcd q L Q hQ a ha]

end GlobalTheory.CompanionTheory.Ar.Num.CkTransport
