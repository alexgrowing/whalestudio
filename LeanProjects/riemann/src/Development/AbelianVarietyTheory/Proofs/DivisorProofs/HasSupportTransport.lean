import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedNeBotOfEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GoodTransport

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.FieldTransport GlobalTheory.LocLanglands.TransportGL GlobalTheory.LocLanglands.FieldCompat
  ValuativeRel Matrix

section Pull

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSubquotient_pull {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (φ : G →* H)
    (h : IsSubquotient σ ρ) : IsSubquotient (pull σ φ) (pull ρ φ) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (φ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (φ g)⟩, hf⟩

end Pull

section Fields

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k']

theorem hasSupport_transport (i : k ≃+* k') (hi : Continuous i) {x : IrrGL k} {x' : IrrGL k'} (hx : RepRel i x x')
    {s : Multiset (IrrGL k)} (hs : HasSupport x.rep s) :
    ∃ s' : Multiset (IrrGL k'), HasSupport x'.rep s' ∧ ∀ y' ∈ s', ∃ y ∈ s, RepRel i y y' := by
  have T1 := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi
  have hi' : Continuous i.symm := T1.1
  have T2 := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k' k i.symm hi'
  obtain ⟨T, hT, -⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero k k' i hi
  have hC := (GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar k k' i hi).1
  obtain ⟨r, xs, rfl, -, hc, e, hsub⟩ := hs
  let σ' : ∀ a, Representation ℂ (GL (Fin (xs a).1) k') (xs a).2.rep.V := fun a =>
    pull (xs a).rep (GeneralLinearGroup.map (i.symm : k' →+* k))
  have hsm : ∀ a, IsSmooth (σ' a) := fun a =>
    isSmooth_comp (xs a).2.rep.smooth (continuous_glMap (i.symm : k' →+* k) hi')
  have hir : ∀ a, (σ' a).IsIrreducible := fun a =>
    (isIrreducible_comp_iff (glMap_surjective i.symm)).2 (xs a).2.rep.irr
  have hrel : ∀ a, RepRel i (xs a) (IrrGL.of (σ' a) (hsm a) (hir a)) := fun a => by
    have h1 := (hT (xs a) (T (xs a))).2 rfl
    have h2 := eq_of_repRel i hi' h1
    rw [h2] at h1
    exact h1
  have hcu : ∀ a, IsCuspidal (σ' a) := fun a =>
    (IrrGL.isCusp_of.1 ((hC _ _ (hrel a)).1.1 ⟨(hc a).1, (hc a).2.2⟩)).2
  obtain rfl := eq_of_repRel i hi' hx
  have B := (nonempty_equiv_parInd e i.symm hi' hi T1.2.2.2.2 T2.2.2.2.2
    (ρ := piTensor σ') (ρ' := piTensor fun a => (xs a).rep) (fun h => by
      show _ = piTensor (fun a => (xs a).rep) (leviMap (i.symm : k' →+* k) (leviMap (i : k →+* k') h))
      rw [leviMap_symm_leviMap])).some
  have hS : IsSubquotient (IrrGL.of (pull x.rep (GeneralLinearGroup.map (i.symm : k' →+* k)))
      (isSmooth_comp x.2.rep.smooth (continuous_glMap (i.symm : k' →+* k) hi'))
      ((isIrreducible_comp_iff (glMap_surjective i.symm)).2 x.2.rep.irr)).rep (multiProd e σ') :=
    (IsSubquotient.of_injective (IrrGL.equivOf _ _ _).symm.toIntertwiningMap
      (IrrGL.equivOf _ _ _).symm.toLinearEquiv.injective).trans
      ((isSubquotient_pull _ hsub).trans
        (IsSubquotient.of_injective B.symm.toIntertwiningMap B.symm.toLinearEquiv.injective))
  have H : IsCuspSupport _ (fun a => (xs a).1) σ' :=
    ⟨IrrRep.irr _, fun a => ⟨(hc a).1, hir a, hcu a⟩, e, hS⟩
  refine ⟨_, hasSupport_of_isCuspSupport H, fun y' hy' => ?_⟩
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy'
  exact ⟨xs a, Multiset.mem_map_of_mem _ (Finset.mem_univ a), hrel a⟩

theorem goodCusp_transport (i : k ≃+* k') (hi : Continuous i)
    (hfixT : ∀ (z : IrrGL k) (z' : IrrGL k'), RepRel i z z' →
      GlobalTheory.PRep.fixed z.rep (GlobalTheory.SplitWeil.KOne k (Fin z.1)) ≠ ⊥ →
      GlobalTheory.PRep.fixed z'.rep (GlobalTheory.SplitWeil.KOne k' (Fin z'.1)) ≠ ⊥)
    {y : IrrGL k} {y' : IrrGL k'} (hy : RepRel i y y')
    (h : UpperTheory.Zero.LLC.GoodCusp y) : UpperTheory.Zero.LLC.GoodCusp y' := by
  have hi' : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi).1
  obtain ⟨T, hT, hTd⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero k k' i hi
  obtain rfl : T y = y' := (hT _ _).1 hy
  rcases h with h1 | ⟨⟨g, hg, j, hj⟩, y₀, χ, hχ, hfix, rfl⟩
  · left
    rw [hTd]
    exact h1
  · right
    have hv : ∀ z, (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) (Units.map i.toRingHom.toMonoidHom z) = χ z :=
      fun z => congrArg χ (Units.ext (by simp))
    refine ⟨⟨g, hg, j.trans i, hi.comp hj⟩, T y₀, χ.comp (Units.map i.symm.toRingHom.toMonoidHom),
      isSmoothChar_comp i.symm hi' hχ, hfixT _ _ ((hT _ _).2 rfl) hfix, ?_⟩
    apply (hT _ _).1
    obtain ⟨n, π, π', e, h1, h2, he⟩ := (hT y₀ (T y₀)).2 rfl
    rw [h2, h1]
    exact repRel_tw i π π' e he χ hχ _ _ hv

end Fields

theorem good_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'),
    Continuous i → ∀ (x : GlobalTheory.LocGL.IrrGL k) (x' : GlobalTheory.LocGL.IrrGL k'), GlobalTheory.LocLanglands.RepRel i x x' →
      UpperTheory.Zero.LLC.Good x → UpperTheory.Zero.LLC.Good x' := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi x x' hx ⟨s, hs, hg⟩
  obtain ⟨s', hs', hrel⟩ := hasSupport_transport i hi hx hs
  exact ⟨s', hs', fun y' hy' => let ⟨y, hy, h⟩ := hrel y' hy'
    goodCusp_transport i hi (GlobalTheory.FixedKOneTransport.fixed_kOne_transport k k' i hi) h (hg y hy)⟩

end GlobalTheory.GoodTransport

end
