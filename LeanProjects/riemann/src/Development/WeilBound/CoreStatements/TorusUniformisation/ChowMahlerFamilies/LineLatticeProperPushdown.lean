import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormalNoethLocalDimOneIsDVR
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineLatticeGeneratorCodimOne
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticePushdown

theorem exists_lift {X X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (f : X' ⟶ X) [IsProper f] (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra V Ω']
    [IsFractionRing V Ω'] (z : Spec (CommRingCat.of V) ⟶ X)
    (w : ξ' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ z) :
    ∃ p' : Cpt ξ', f p'.1 = z (IsLocalRing.closedPoint V) ∧
      ∀ a ∈ regAt ξ' p', ∃ v : V, algebraMap V Ω' v = a := by
  have hex : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Spec (CommRingCat.of V) ⟶ X',
      Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ l = ξ' ∧ l ≫ f = z := by
    obtain ⟨l, hl₁, hl₂⟩ := (hex { R := V, K := Ω', commSq := ⟨w⟩, .. }).exists_lift
    exact ⟨l, hl₁, hl₂⟩
  have hsp : genPt ξ' ⤳ l (IsLocalRing.closedPoint V) := by
    unfold genPt
    rw [← hl₁]
    exact (IsLocalRing.specializes_closedPoint _).map l.continuous
  have key : X'.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ' =
      Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω') := by
    apply Spec.map_injective
    rw [← cancel_mono (X'.fromSpecStalk (l (IsLocalRing.closedPoint V)))]
    have h1 : Spec.map (X'.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ') ≫
        X'.fromSpecStalk (l (IsLocalRing.closedPoint V)) = ξ' := by
      refine Eq.trans (congrArg (· ≫ X'.fromSpecStalk (l (IsLocalRing.closedPoint V)))
        (Spec.map_comp (X'.presheaf.stalkSpecializes hsp) (Scheme.stalkClosedPointTo ξ'))) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ') ≫ ·)
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp)) ?_
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
    have h2 : Spec.map (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω')) ≫
        X'.fromSpecStalk (l (IsLocalRing.closedPoint V)) = ξ' := by
      rw [Spec.map_comp, Category.assoc]
      refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ ·)
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk l)) hl₁
    exact h1.trans h2.symm
  refine ⟨⟨_, hsp⟩, ?_, ?_⟩
  · rw [← hl₂]
    exact (Scheme.Hom.comp_apply l f _).symm
  · rintro _ ⟨g, rfl⟩
    exact ⟨(Scheme.stalkClosedPointTo l).hom g, (congrArg (fun t => t.hom g) key).symm⟩

theorem spec_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) :
    Spec.map (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk q.1 = ξ := by
  refine Eq.trans (congrArg (· ≫ X.fromSpecStalk q.1)
    (Spec.map_comp (X.presheaf.stalkSpecializes q.2) (Scheme.stalkClosedPointTo ξ))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2)) ?_
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ

theorem exists_over {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    [IsLocallyNoetherian X] {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {f : X' ⟶ X} {i : Ω →+* Ω'} [IsProper f] (hD : Dominates ξ' ξ f i) (hi : Function.Bijective i)
    (hg : IsCptGen ξ) (hn : NormalCpt ξ) (q : Cpt ξ) (hd : ringKrullDim (X.presheaf.stalk q.1) = 1) :
    ∃ p' : Cpt ξ', f p'.1 = q.1 ∧ ∀ a : Ω, i a ∈ regAt ξ' p' → a ∈ regAt ξ q := by
  obtain ⟨hfr, -, -⟩ := RegAtRing.regAt_ring X Ω ξ hg q
  have : IsFractionRing (regAt ξ q) Ω := hfr
  have : IsIntegrallyClosed (regAt ξ q) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, hn q x hx⟩, rfl⟩
  have hdom : IsDomain (X.presheaf.stalk q.1) := (hg.inj q).isDomain (genMap ξ q)
  have : IsIntegrallyClosed (X.presheaf.stalk q.1) :=
    IsIntegrallyClosed.of_equiv (RegAtRing.stalkEquiv hg q).symm
  have : IsDiscreteValuationRing (X.presheaf.stalk q.1) := normal_noeth_local_dim_one_isDVR _ hd
  let _ : Algebra (X.presheaf.stalk q.1) Ω' := (i.comp (genMap ξ q)).toAlgebra
  have : FaithfulSMul (X.presheaf.stalk q.1) Ω' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (hi.1.comp (hg.inj q))
  have hfr' : IsFractionRing (X.presheaf.stalk q.1) Ω' := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨y, rfl⟩ := hi.2 z
    obtain ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩, rfl⟩ := RegAtRing.exists_div hg q y
    exact ⟨a, b, map_div₀ i _ _⟩
  have w : ξ' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk q.1) Ω')) ≫
      X.fromSpecStalk q.1 := by
    have e : CommRingCat.ofHom (algebraMap (X.presheaf.stalk q.1) Ω') =
        (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ CommRingCat.ofHom i := rfl
    refine hD.trans ?_
    refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom i) ≫ ·) (spec_genMap ξ q).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (· ≫ X.fromSpecStalk q.1) (Spec.map_comp _ _).symm
  have hv : ValuationRing (X.presheaf.stalk q.1) := inferInstance
  obtain ⟨p', h1, h2⟩ := @exists_lift X X' Ω' _ ξ' f _ (X.presheaf.stalk q.1) _ hdom hv _ hfr'
    (X.fromSpecStalk q.1) w
  refine ⟨p', h1.trans Scheme.fromSpecStalk_closedPoint, fun a ha => ?_⟩
  obtain ⟨v, hv⟩ := h2 _ ha
  exact ⟨v, hi.1 hv⟩

end PositivityTheory.Xgn.LineLatticePushdown

theorem PositivityTheory.Xgn.line_lattice_proper_pushdown : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t := by
  intro X Ω _ ξ _ X' Ω' _ ξ' f i _ hD hi hg hn L T p t hL hT hp
  have ht : t ≠ 0 := by
    have h0 := (hp ⟨genPt ξ', specializes_rfl⟩ (by
      show f (genPt ξ') ⤳ p.1
      rw [hD.map_genPt]; exact p.2)).1
    rintro rfl
    exact h0 (map_zero i)
  refine PositivityTheory.Xgn.line_lattice_generator_codim_one X Ω ξ hg hn L T p t hL hT ht fun q hqp hd => ?_
  obtain ⟨p', hq, hreg⟩ := PositivityTheory.Xgn.LineLatticePushdown.exists_over hD hi hg hn q hd
  obtain ⟨q, hq0⟩ := q
  obtain rfl : f p'.1 = q := hq
  obtain ⟨U, hU, b, -, h⟩ := hL _ (hT _ hqp)
  obtain ⟨h1, h2⟩ := h _ (hT _ hqp) hU
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  rw [hr] at h2
  have he : b 0 ≠ 0 := h1.ne_zero 0
  obtain ⟨_, -, hpull⟩ := pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hD p'
  have g1 := hpull L (b 0) ⟨he, h2⟩
  have g2 := hp p' hqp
  obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq g2.1 (g2.2.symm.trans g1.2)
  have hu' : u = i (t / b 0) := by
    rw [map_div₀, e, smul_eq_mul, mul_div_cancel_right₀ _ g1.1]
  subst hu'
  have hu2 : unitAt ξ ⟨f p'.1, hq0⟩ (t / b 0) :=
    ⟨div_ne_zero ht he, hreg _ hu.2.1, hreg _ (by rw [map_inv₀]; exact hu.2.2)⟩
  refine ⟨ht, h2.trans (span_singleton_eq_of_unitAt hu2 ?_).symm⟩
  rw [smul_eq_mul, div_mul_cancel₀ _ he]
