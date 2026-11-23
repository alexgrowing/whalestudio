import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Inhabit
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBaseExtensionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleChainStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagComparisonStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUniqueStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleShortExactStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPairBaseExtensionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPairStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubQuotientStatementStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.SubQuotCk

section Generic

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
  [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {N N₁ N₂ : ℕ} {V V₁ V₂ : Type} [AddCommGroup V] [Module Ω V]
  [AddCommGroup V₁] [Module Ω V₁] [AddCommGroup V₂] [Module Ω V₂]

theorem sameGeneric_self (E : ChartBundle O (mseg x) N V) : SameGeneric O x E E :=
  fun _ _ => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
    fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩

theorem sameGeneric_sub {E E' : ChartBundle O (mseg x) N V} {i : V₁ →ₗ[Ω] V} {p : V →ₗ[Ω] V₂}
    {E₁ E₁' : ChartBundle O (mseg x) N₁ V₁} {E₂ E₂' : ChartBundle O (mseg x) N₂ V₂}
    (hs : SameGeneric O x E E') (h : IsSubQuot O x E i p E₁ E₂)
    (h' : IsSubQuot O x E' i p E₁' E₂') : SameGeneric O x E₁ E₁' := by
  intro s hx
  have l := (h.2.2.2 s hx).1
  have l' := (h'.2.2.2 s hx).1
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [l] at hv
    obtain ⟨c, hc, hcv⟩ := (hs s hx).1 (i v) hv
    refine ⟨c, hc, ?_⟩
    rw [l']
    change i (algebraMap O Ω c • v) ∈ E'.lat s
    rwa [map_smul]
  · rw [l'] at hv
    obtain ⟨c, hc, hcv⟩ := (hs s hx).2 (i v) hv
    refine ⟨c, hc, ?_⟩
    rw [l]
    change i (algebraMap O Ω c • v) ∈ E.lat s
    rwa [map_smul]

theorem sameGeneric_quot {E E' : ChartBundle O (mseg x) N V} {i : V₁ →ₗ[Ω] V} {p : V →ₗ[Ω] V₂}
    {E₁ E₁' : ChartBundle O (mseg x) N₁ V₁} {E₂ E₂' : ChartBundle O (mseg x) N₂ V₂}
    (hs : SameGeneric O x E E') (h : IsSubQuot O x E i p E₁ E₂)
    (h' : IsSubQuot O x E' i p E₁' E₂') : SameGeneric O x E₂ E₂' := by
  intro s hx
  have l := (h.2.2.2 s hx).2
  have l' := (h'.2.2.2 s hx).2
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [l] at hv
    obtain ⟨e, he, rfl⟩ := hv
    obtain ⟨c, hc, hce⟩ := (hs s hx).1 e he
    refine ⟨c, hc, ?_⟩
    rw [l']
    exact ⟨_, hce, map_smul p _ e⟩
  · rw [l'] at hv
    obtain ⟨e, he, rfl⟩ := hv
    obtain ⟨c, hc, hce⟩ := (hs s hx).2 e he
    refine ⟨c, hc, ?_⟩
    rw [l]
    exact ⟨_, hce, map_smul p _ e⟩

theorem rank_add {i : V₁ →ₗ[Ω] V} {p : V →ₗ[Ω] V₂} (hi : Function.Injective i)
    (hp : Function.Surjective p) (hr : LinearMap.range i = LinearMap.ker p)
    (w : Module.Basis (Fin N) Ω V) (w₁ : Module.Basis (Fin N₁) Ω V₁)
    (w₂ : Module.Basis (Fin N₂) Ω V₂) : N = N₁ + N₂ := by
  haveI : FiniteDimensional Ω V := w.finiteDimensional_of_finite
  have h := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.2 hp, finrank_top, ← hr, LinearMap.finrank_range_of_inj hi] at h
  have e := Module.finrank_eq_card_basis w
  have e₁ := Module.finrank_eq_card_basis w₁
  have e₂ := Module.finrank_eq_card_basis w₂
  simp only [Fintype.card_fin] at e e₁ e₂
  omega

end Generic

theorem length_classList {K : Type} {q m : ℕ} (cls : Fin q → K → ℤ) {Q : MvPolynomial (Fin q) ℤ}
    (hQ : Q.IsHomogeneous m) {μ : Fin q →₀ ℕ} (hμ : μ ∈ Q.support) :
    (classList cls μ).length = m := by
  have h := hQ (mem_support_iff.1 hμ)
  rw [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset, ← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

section Stages

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
  [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {N N₁ N₂ : ℕ} {V V₁ V₂ : Type} [AddCommGroup V] [Module Ω V]
  [AddCommGroup V₁] [Module Ω V₁] [AddCommGroup V₂] [Module Ω V₂]

def Setup (x : (Σ k, ι k) → Ω) (d : ℕ) (E E' : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V)
    (p : V →ₗ[Ω] V₂) (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁)
    (E₂ E₂' : ChartBundle O (mseg x) N₂ V₂) : Prop :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d ∧
    SameGeneric O x E E' ∧ IsSubQuot O x E i p E₁ E₂ ∧ IsSubQuot O x E' i p E₁' E₂'

def CkAdd (x : (Σ k, ι k) → Ω) (d : ℕ) (E E' : ChartBundle O (mseg x) N V)
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁) (E₂ E₂' : ChartBundle O (mseg x) N₂ V₂) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
    Q.IsHomogeneous (d + 1 - k) →
    ck O x d N E E' k L Q = ck O x d N₁ E₁ E₁' k L Q + ck O x d N₂ E₂ E₂' k L Q

def HasFlag {M : ℕ} {W : Type} [AddCommGroup W] [Module Ω W] (ϖ : O) (x : (Σ k, ι k) → Ω)
    (B B' : ChartBundle O (mseg x) M W) : Prop :=
  ∃ (w w' : Module.Basis (Fin M) Ω W) (b b' : Fin M → K → ℤ) (f g : Fin M → MRing ι O),
    IsFlagPair ϖ x B B' w w' b b' f g

theorem HasFlag.pull {M : ℕ} {W : Type} [AddCommGroup W] [Module Ω W] {ϖ : O}
    {x : (Σ k, ι k) → Ω} {B B' : ChartBundle O (mseg x) M W} (h : HasFlag ϖ x B B')
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {z : (Σ k, ι' k) → Ω} {BB B'B : ChartBundle O (mseg (joinCoord x z)) M W}
    (hp : IsPull O x z B BB) (hp' : IsPull O x z B' B'B) :
    HasFlag ϖ (joinCoord x z) BB B'B := by
  obtain ⟨w, w', b, b', f, g, hf⟩ := h
  exact ⟨w, w', _, _, _, _,
    (GlobalTheory.T.flag_pair_base_extension O Ω K ι x ϖ M W B B' w w' b b' f g hf).1 K' ι' z BB B'B hp hp'⟩

theorem exists_flag {M : ℕ} {W : Type} [AddCommGroup W] [Module Ω W] {ϖ : O} (hϖ : Irreducible ϖ)
    {x : (Σ k, ι k) → Ω} {d : ℕ}
    (hM : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d)
    {B B' : ChartBundle O (mseg x) M W} (hs : SameGeneric O x B B') :
    ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type)
      (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω)
      (BB B'B : ChartBundle O (mseg (joinCoord x z)) M W),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧
      fnField O (joinCoord x z) = fnField O x ∧ IsPull O x z B BB ∧ IsPull O x z B' B'B ∧
      HasFlag ϖ (joinCoord x z) BB B'B := by
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hMB, hbir, hEB⟩ :=
    GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hM M 1 W ![B, B'] (by
      intro j
      fin_cases j
      · exact sameGeneric_self B
      · exact hs)
  have hM' : IsModelOver (pointIdeal O (joinCoord x z)) d :=
    ((GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O _ d).1 hMB).2
  have p0 : IsPull O x z B (EB 0) := (hEB 0).1
  have p1 : IsPull O x z B' (EB 1) := (hEB 1).1
  have tri : ∀ i j : Fin M, i < j → w.repr (w i) j = 0 := by
    intro i j hij
    simp [Module.Basis.repr_self, Finsupp.single_apply, ne_of_lt hij]
  have s01 := (GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x M W B B' K' ι' z (EB 0) (EB 1) p0 p1).2.1 hs
  obtain ⟨-, f, g, hf⟩ := GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hM' M W
    (EB 0) (EB 1) s01 w w (b 0) (b 1) (hEB 0).2 (hEB 1).2 tri
  exact ⟨K', _, _, ι', _, z, EB 0, EB 1, hMB, hbir, p0, p1, w, w, b 0, b 1, f, g, hf⟩

theorem exists_pull {M : ℕ} {W : Type} [AddCommGroup W] [Module Ω W] {x : (Σ k, ι k) → Ω}
    (B : ChartBundle O (mseg x) M W) {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type}
    [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) :
    ∃ BB : ChartBundle O (mseg (joinCoord x z)) M W, IsPull O x z B BB :=
  (GlobalTheory.T.chart_bundle_base_extension O Ω K ι x M W B).1 K' ι' z

theorem descend {x : (Σ k, ι k) → Ω} {d : ℕ} {E E' : ChartBundle O (mseg x) N V}
    {i : V₁ →ₗ[Ω] V} {p : V →ₗ[Ω] V₂} {E₁ E₁' : ChartBundle O (mseg x) N₁ V₁}
    {E₂ E₂' : ChartBundle O (mseg x) N₂ V₂} (hS : Setup x d E E' i p E₁ E₁' E₂ E₂')
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {z : (Σ k, ι' k) → Ω}
    (hz : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d)
    (hb : fnField O (joinCoord x z) = fnField O x)
    {EB E'B : ChartBundle O (mseg (joinCoord x z)) N V}
    {E₁B E₁'B : ChartBundle O (mseg (joinCoord x z)) N₁ V₁}
    {E₂B E₂'B : ChartBundle O (mseg (joinCoord x z)) N₂ V₂}
    (p0 : IsPull O x z E EB) (p0' : IsPull O x z E' E'B)
    (p1 : IsPull O x z E₁ E₁B) (p1' : IsPull O x z E₁' E₁'B)
    (p2 : IsPull O x z E₂ E₂B) (p2' : IsPull O x z E₂' E₂'B)
    (H : Setup (joinCoord x z) d EB E'B i p E₁B E₁'B E₂B E₂'B →
      CkAdd (joinCoord x z) d EB E'B E₁B E₁'B E₂B E₂'B) :
    CkAdd x d E E' E₁ E₁' E₂ E₂' := by
  obtain ⟨hM, hs, h, h'⟩ := hS
  have hS' : Setup (joinCoord x z) d EB E'B i p E₁B E₁'B E₂B E₂'B :=
    ⟨hz, (GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E E' K' ι' z EB E'B p0 p0').2.1 hs,
      GlobalTheory.T.chart_bundle_short_exact O Ω K ι x N N₁ N₂ V V₁ V₂ E i p E₁ E₂ h K' ι' z EB E₁B E₂B p0 p1 p2,
      GlobalTheory.T.chart_bundle_short_exact O Ω K ι x N N₁ N₂ V V₁ V₂ E' i p E₁' E₂' h' K' ι' z E'B E₁'B E₂'B p0' p1' p2'⟩
  intro k hk1 hk2 q L Q hQ
  have e := H hS' k hk1 hk2 q (fun j => pullDeg (K' := K') (L j)) Q hQ
  rw [(GlobalTheory.T.same_generic_base_extension O Ω K ι x d hM N V E E' hs K' ι' z hz hb EB E'B p0 p0').1 k hk1 hk2 q L Q hQ,
    (GlobalTheory.T.same_generic_base_extension O Ω K ι x d hM N₁ V₁ E₁ E₁' (sameGeneric_sub hs h h') K' ι' z hz hb E₁B E₁'B
      p1 p1').1 k hk1 hk2 q L Q hQ,
    (GlobalTheory.T.same_generic_base_extension O Ω K ι x d hM N₂ V₂ E₂ E₂' (sameGeneric_quot hs h h') K' ι' z hz hb E₂B E₂'B
      p2 p2').1 k hk1 hk2 q L Q hQ] at e
  exact e

theorem ckAdd_of_flags {ϖ : O} (hϖ : Irreducible ϖ) {x : (Σ k, ι k) → Ω} {d : ℕ}
    {E E' : ChartBundle O (mseg x) N V} {i : V₁ →ₗ[Ω] V} {p : V →ₗ[Ω] V₂}
    {E₁ E₁' : ChartBundle O (mseg x) N₁ V₁} {E₂ E₂' : ChartBundle O (mseg x) N₂ V₂}
    (hS : Setup x d E E' i p E₁ E₁' E₂ E₂') (ha : HasFlag ϖ x E E') (hb : HasFlag ϖ x E₁ E₁')
    (hc : HasFlag ϖ x E₂ E₂') : CkAdd x d E E' E₁ E₁' E₂ E₂' := by
  obtain ⟨hM, hs, h, h'⟩ := hS
  obtain ⟨hK, hM'⟩ := (GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O _ d).1 hM
  obtain ⟨w, w', b, b', f, g, hf⟩ := ha
  obtain ⟨w₁, w₁', b₁, b₁', f₁, g₁, hf₁⟩ := hb
  obtain ⟨w₂, w₂', b₂, b₂', f₂, g₂, hf₂⟩ := hc
  have hN : N = N₁ + N₂ := rank_add h.1 h.2.1 h.2.2.1 w w₁ w₂
  have hN₂ : N₂ = N - N₁ := by omega
  subst hN₂
  have s0 := (GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.sameGeneric_iff hϖ x E E').1 hs
  have s1 := (GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.sameGeneric_iff hϖ x E₁ E₁').1
    (sameGeneric_sub hs h h')
  have s2 := (GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.sameGeneric_iff hϖ x E₂ E₂').1
    (sameGeneric_quot hs h h')
  intro k hk1 hk2 q L Q hQ
  have c0 := (GlobalTheory.T.chern_class_on_flag_pair O ϖ hϖ Ω K ι x d hK hM' N V E E' s0 w w' b b' f g hf).1 k hk1 hk2
    (psumExpansion N k) (isPairExpansion_psum N k) q L Q hQ
  have c1 := (GlobalTheory.T.chern_class_on_flag_pair O ϖ hϖ Ω K ι x d hK hM' N₁ V₁ E₁ E₁' s1 w₁ w₁' b₁ b₁' f₁ g₁ hf₁).1 k hk1
    hk2 (psumExpansion N₁ k) (isPairExpansion_psum N₁ k) q L Q hQ
  have c2 := (GlobalTheory.T.chern_class_on_flag_pair O ϖ hϖ Ω K ι x d hK hM' (N - N₁) V₂ E₂ E₂' s2 w₂ w₂' b₂ b₂' f₂ g₂ hf₂).1
    k hk1 hk2 (psumExpansion (N - N₁) k) (isPairExpansion_psum (N - N₁) k) q L Q hQ
  rw [c0, c1, c2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [← mul_add]
  congr 1
  exact GlobalTheory.T.sub_quotient_statement O ϖ hϖ Ω K ι x d hM' N N₁ V V₁ V₂ E E' E₁ E₁' E₂ E₂' i p h.1 h.2.1 h.2.2.1 s0
    (fun c hc => ⟨fun z => by rw [(h.2.2.2 c hc).1]; rfl, fun z => by rw [(h'.2.2.2 c hc).1]; rfl,
      fun q => by rw [(h.2.2.2 c hc).2]; rfl, fun q => by rw [(h'.2.2.2 c hc).2]; rfl⟩)
    w w' b b' f g hf w₁ w₁' b₁ b₁' f₁ g₁ hf₁ w₂ w₂' b₂ b₂' f₂ g₂ hf₂ k (psumExpansion N k)
    (psumExpansion N₁ k) (psumExpansion (N - N₁) k) (isPairExpansion_psum N k)
    (isPairExpansion_psum N₁ k) (isPairExpansion_psum (N - N₁) k) (classList L μ)
    (by rw [length_classList _ hQ hμ]; omega)

theorem ckAdd_of_two {ϖ : O} (hϖ : Irreducible ϖ) {x : (Σ k, ι k) → Ω} {d : ℕ}
    {E E' : ChartBundle O (mseg x) N V} {i : V₁ →ₗ[Ω] V} {p : V →ₗ[Ω] V₂}
    {E₁ E₁' : ChartBundle O (mseg x) N₁ V₁} {E₂ E₂' : ChartBundle O (mseg x) N₂ V₂}
    (hS : Setup x d E E' i p E₁ E₁' E₂ E₂') (ha : HasFlag ϖ x E E') (hb : HasFlag ϖ x E₁ E₁') :
    CkAdd x d E E' E₁ E₁' E₂ E₂' := by
  obtain ⟨K', _, _, ι', _, z, B, B', hz, hbir, q2, q2', hc⟩ :=
    exists_flag hϖ hS.1 (sameGeneric_quot hS.2.1 hS.2.2.1 hS.2.2.2)
  obtain ⟨EB, p0⟩ := exists_pull E z
  obtain ⟨E'B, p0'⟩ := exists_pull E' z
  obtain ⟨E₁B, p1⟩ := exists_pull E₁ z
  obtain ⟨E₁'B, p1'⟩ := exists_pull E₁' z
  exact descend hS hz hbir p0 p0' p1 p1' q2 q2' fun hS' =>
    ckAdd_of_flags hϖ hS' (ha.pull p0 p0') (hb.pull p1 p1') hc

theorem ckAdd_of_one {ϖ : O} (hϖ : Irreducible ϖ) {x : (Σ k, ι k) → Ω} {d : ℕ}
    {E E' : ChartBundle O (mseg x) N V} {i : V₁ →ₗ[Ω] V} {p : V →ₗ[Ω] V₂}
    {E₁ E₁' : ChartBundle O (mseg x) N₁ V₁} {E₂ E₂' : ChartBundle O (mseg x) N₂ V₂}
    (hS : Setup x d E E' i p E₁ E₁' E₂ E₂') (ha : HasFlag ϖ x E E') :
    CkAdd x d E E' E₁ E₁' E₂ E₂' := by
  obtain ⟨K', _, _, ι', _, z, B, B', hz, hbir, q1, q1', hc⟩ :=
    exists_flag hϖ hS.1 (sameGeneric_sub hS.2.1 hS.2.2.1 hS.2.2.2)
  obtain ⟨EB, p0⟩ := exists_pull E z
  obtain ⟨E'B, p0'⟩ := exists_pull E' z
  obtain ⟨E₂B, p2⟩ := exists_pull E₂ z
  obtain ⟨E₂'B, p2'⟩ := exists_pull E₂' z
  exact descend hS hz hbir p0 p0' q1 q1' p2 p2' fun hS' =>
    ckAdd_of_two hϖ hS' (ha.pull p0 p0') hc

theorem ckAdd {ϖ : O} (hϖ : Irreducible ϖ) {x : (Σ k, ι k) → Ω} {d : ℕ}
    {E E' : ChartBundle O (mseg x) N V} {i : V₁ →ₗ[Ω] V} {p : V →ₗ[Ω] V₂}
    {E₁ E₁' : ChartBundle O (mseg x) N₁ V₁} {E₂ E₂' : ChartBundle O (mseg x) N₂ V₂}
    (hS : Setup x d E E' i p E₁ E₁' E₂ E₂') : CkAdd x d E E' E₁ E₁' E₂ E₂' := by
  obtain ⟨K', _, _, ι', _, z, B, B', hz, hbir, q0, q0', hc⟩ := exists_flag hϖ hS.1 hS.2.1
  obtain ⟨E₁B, p1⟩ := exists_pull E₁ z
  obtain ⟨E₁'B, p1'⟩ := exists_pull E₁' z
  obtain ⟨E₂B, p2⟩ := exists_pull E₂ z
  obtain ⟨E₂'B, p2'⟩ := exists_pull E₂' z
  exact descend hS hz hbir q0 q0' p1 p1' p2 p2' fun hS' => ckAdd_of_one hϖ hS' hc

end Stages

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.Bb.Statement.{0,0,0} O Ω ι := by
  intro O _ _ _ Ω _ _ K _ ι _
  classical
  intro x d N N₁ N₂ V V₁ V₂ _ _ _ _ _ _ E E' i p E₁ E₁' E₂ E₂' hM hs h h' k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  exact ckAdd hϖ ⟨hM, hs, h, h'⟩ k hk1 hk2 q L Q hQ

end GlobalTheory.CompanionTheory.Ar.Num.SubQuotCk
