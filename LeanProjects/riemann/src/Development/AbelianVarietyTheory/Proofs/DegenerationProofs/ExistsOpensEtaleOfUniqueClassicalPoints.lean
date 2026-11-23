import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

open Polynomial in

theorem exists_etale_int_surjective_of_finite_field (K : Type) [Field K] [Finite K] :
    ∃ (A : Type) (_ : CommRing A) (β : A →+* K),
      (Int.castRingHom A).Etale ∧ Function.Surjective β := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  let f : ℤ[X] := X ^ (Fintype.card K - 1) - C 1
  let P : StandardEtalePair ℤ :=
    ⟨f, monic_X_pow_sub_C _ (by omega), derivative f, 1, 0, 1, by simp⟩
  obtain ⟨α, hα⟩ := IsCyclic.exists_generator (α := Kˣ)
  have h1 : (α : K) ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ α.ne_zero
  have hm : P.HasMap (α : K) := by
    refine ⟨by simp [P, f, h1], ?_⟩
    have : ((Fintype.card K - 1 : ℕ) : K) = -1 := by
      rw [Nat.cast_sub hq.le]; simp
    simp [P, f, derivative_X_pow, this]
  refine ⟨P.Ring, inferInstance, (P.lift _ hm).toRingHom, ?_, fun k => ?_⟩
  · have : Int.castRingHom P.Ring = algebraMap ℤ P.Ring := RingHom.ext_int _ _
    rw [this]
    exact RingHom.etale_algebraMap.mpr inferInstance
  · by_cases hk : k = 0
    · exact ⟨0, by simp [hk]⟩
    · obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hα (Units.mk0 k hk)))
      refine ⟨P.X ^ n, ?_⟩
      have := congrArg Units.val hn
      simpa using this

theorem exists_factor_fromSpecResidueField {K : Type} [Field K] {X : Scheme.{0}}
    (a : Spec (.of K) ⟶ X) {x : X} (hx : a (IsLocalRing.closedPoint K) = x) :
    ∃ φ : X.residueField x ⟶ .of K, Spec.map φ ≫ X.fromSpecResidueField x = a := by
  subst hx
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X a⟩

theorem exists_factor_of_lift_fromSpecResidueField {Y W : Scheme.{0}} (h : Y ⟶ W) (w : W)
    (ξ : Spec (W.residueField w) ⟶ Y) (hξ : ξ ≫ h = W.fromSpecResidueField w)
    {K : Type} [Field K] (a : Spec (.of K) ⟶ Y)
    (ha : a (IsLocalRing.closedPoint K) = ξ (IsLocalRing.closedPoint (W.residueField w))) :
    ∃ σ : W.residueField w ⟶ .of K, Spec.map σ ≫ ξ = a := by
  obtain ⟨σ, hσ⟩ := exists_factor_fromSpecResidueField a ha
  generalize hy : ξ (IsLocalRing.closedPoint (W.residueField w)) = y at σ hσ
  obtain ⟨φ, hφ⟩ := exists_factor_fromSpecResidueField (K := W.residueField w) ξ hy
  obtain ⟨ψ, hψ⟩ := exists_factor_fromSpecResidueField (K := Y.residueField y)
    (Y.fromSpecResidueField y ≫ h) (x := w) (by
      refine (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg h (Scheme.fromSpecResidueField_apply y _)).trans ?_)
      rw [← hy, ← Scheme.Hom.comp_apply, hξ]
      exact Scheme.fromSpecResidueField_apply w _)
  have h1 : ψ ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono (W.fromSpecResidueField w), Spec.map_comp, Category.assoc, hψ,
      ← Category.assoc, hφ, hξ, Spec.map_id]
    exact (Category.id_comp _).symm
  have h2 : φ ≫ ψ = 𝟙 _ := by
    ext z
    apply φ.hom.injective
    exact congr($h1 (φ z))
  refine ⟨ψ ≫ σ, ?_⟩
  rw [← hσ, ← hφ, ← Spec.map_comp_assoc, ← Category.assoc φ, h2, Category.id_comp]

theorem apply_eq_genericPoint_of_generalizingMap {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] [T0Space S] [QuasiSober T] [IrreducibleSpace T] {f : S → T}
    (hf : GeneralizingMap f) {s : S} (hs : s ∈ genericPoints S) : f s = genericPoint T := by
  obtain ⟨s', hs', e⟩ := hf (genericPoint_specializes (f s))
  have h : closure {s} ⊆ closure ({s'} : Set S) := specializes_iff_closure_subset.mp hs'
  have h' := hs.2 isIrreducible_singleton.closure h
  rw [← e, (hs'.antisymm (specializes_iff_closure_subset.mpr h')).eq]

theorem eq_of_specializes_of_locallyQuasiFinite {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] {a b : X} (h : a ⤳ b) (e : f a = f b) : a = b := by
  have hd := (f.isDiscrete_preimage_singleton (f b)).to_subtype
  have : (⟨a, e⟩ : f ⁻¹' {f b}) ⤳ ⟨b, rfl⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val this.eq

theorem exists_opens_etale_of_finite_etale_localisation_of_isIntegral
    (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (W : Scheme.{0}) [IsIntegral W] (u : W ⟶ X)
    [LocallyOfFiniteType u] [IsDominant u] (w : W) (U : W.Opens) (hw : IsClosed ({w} : Set W))
    (hU : (U : Set W).Nonempty)
    (huniq : ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W), a ≫ u = a' ≫ u → a (cPt p) = w →
      spMap (IsLocalRing.residue (OO p)) ≫ a = spMap (IsLocalRing.residue (OO p)) ≫ a' →
        Set.range (gPt p ≫ a) ⊆ U → Set.range (gPt p ≫ a') ⊆ U → a = a')
    {T V : Scheme.{0}} [IsIntegral T] (g : T ⟶ X) [Etale g] (h : V ⟶ W) [Etale h] (f : V ⟶ T)
    [IsFinite f] (sq : h ≫ u = f ≫ g)
    (hmono : ∀ (Z : Scheme.{0}) (a b : Z ⟶ V), a ≫ h = b ≫ h → a ≫ f = b ≫ f → a = b)
    (v : V) (hv : h v = w)
    (hgeo : ∀ (K : Type) [Field K] (a b : Spec (.of K) ⟶ V), a ≫ f = b ≫ f →
      (a ≫ f) (IsLocalRing.closedPoint K) = f v →
        a ≫ h = b ≫ h ∧ (a ≫ h) (IsLocalRing.closedPoint K) = w) :
    ∃ V : W.Opens, w ∈ V ∧ Etale (V.ι ≫ u) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian u
  have : LocallyOfFinitePresentation u :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  have hNT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g hN
  have := geometricallyReduced_of_smooth h
  have : IsReduced V := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian h
  have : Nonempty V := ⟨v⟩
  have hgh : ∀ z ∈ genericPoints V, h z = genericPoint W := fun z hz =>
    apply_eq_genericPoint_of_generalizingMap (Flat.generalizingMap h) hz
  have hgT : g (genericPoint T) = genericPoint X :=
    apply_eq_genericPoint_of_generalizingMap (Flat.generalizingMap g) (by rw [genericPoints_eq_singleton]; rfl)
  have := TangentCrit.locallyQuasiFinite_of_formallyUnramified g
  have := TangentCrit.locallyQuasiFinite_of_formallyUnramified h
  have hgu : u (genericPoint W) = genericPoint X := by
    apply IsGenericPoint.eq _ (genericPoint_spec X)
    have := (genericPoint_spec W).image u.continuous
    rwa [Set.image_univ, u.denseRange.closure_range] at this
  have hgf : ∀ z ∈ genericPoints V, f z = genericPoint T := fun z hz => by
    refine (eq_of_specializes_of_locallyQuasiFinite g (genericPoint_specializes _) ?_).symm
    rw [← Scheme.Hom.comp_apply, ← sq, Scheme.Hom.comp_apply, hgh z hz, hgu, hgT]
  have hvc : IsClosed ({v} : Set V) :=
    isClosed_of_subset_discrete_closed (t := h ⁻¹' {w}) (by simpa using hv)
      (h.isDiscrete_preimage_singleton w) (hw.preimage h.continuous)
  have htc : IsClosed ({f v} : Set T) := by
    simpa using f.isClosedMap _ hvc
  let U' : T.Opens := ⟨(f '' (h ⁻¹ᵁ U : Set V)ᶜ)ᶜ,
    (f.isClosedMap _ (h ⁻¹ᵁ U).isOpen.isClosed_compl).isOpen_compl⟩
  have hU' : ∀ z : V, f z ∈ U' → h z ∈ U := fun z hz => by
    by_contra H
    exact hz ⟨z, H, rfl⟩
  have hU'ne : (U' : Set T).Nonempty := by
    refine ⟨genericPoint T, ?_⟩
    rintro ⟨z, hz, e⟩
    obtain ⟨z₀, hz₀, hs⟩ := exists_mem_genericPoints_specializes z
    obtain rfl : z₀ = z :=
      eq_of_specializes_of_locallyQuasiFinite f hs ((hgf z₀ hz₀).trans e.symm)
    apply hz
    change h z₀ ∈ U
    rw [hgh z₀ hz₀]
    exact ((genericPoint_spec W).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hiso : IsIso f := by
    refine isIso_of_isFinite_of_unique_lift_of_classical_points T (g ≫ π) hNT V f hgf (f v) U'
      htc hU'ne fun p _ a a' e hc hr => ?_
    have hcl : spMap (IsLocalRing.residue (OO p))
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField (OO p))) = cPt p :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
    obtain ⟨h₁, h₂⟩ := hgeo (IsLocalRing.ResidueField (OO p))
      (spMap (IsLocalRing.residue (OO p)) ≫ a) (spMap (IsLocalRing.residue (OO p)) ≫ a')
      (by rw [Category.assoc, e, Category.assoc])
      (by rw [Category.assoc, Scheme.Hom.comp_apply, hcl, hc])
    have hran : ∀ b : Sp (OO p) ⟶ V, b ≫ f = a ≫ f → Set.range (gPt p ≫ b ≫ h) ⊆ U := by
      rintro b hb _ ⟨z, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply]
      apply hU'
      rw [← Scheme.Hom.comp_apply, Category.assoc, hb]
      exact hr ⟨z, rfl⟩
    refine hmono _ a a' (huniq p (a ≫ h) (a' ≫ h) ?_ ?_ ?_ (hran a rfl) (hran a' e.symm)) e
    · rw [Category.assoc, Category.assoc, sq, reassoc_of% e]
    · rwa [Category.assoc, Scheme.Hom.comp_apply, hcl] at h₂
    · simpa only [Category.assoc] using h₁
  have : Etale (h ≫ u) := by rw [sq]; infer_instance
  obtain ⟨V', hV', hE⟩ := exists_opens_range_etale_of_comp V W X h u
  exact ⟨V', hV'.ge ⟨v, hv⟩, hE⟩

theorem exists_opens_etale_of_finite_etale_localisation
    (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (W : Scheme.{0}) [IsIntegral W] (u : W ⟶ X)
    [LocallyOfFiniteType u] [IsDominant u] (w : W) (U : W.Opens) (hw : IsClosed ({w} : Set W))
    (hU : (U : Set W).Nonempty)
    (huniq : ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W), a ≫ u = a' ≫ u → a (cPt p) = w →
      spMap (IsLocalRing.residue (OO p)) ≫ a = spMap (IsLocalRing.residue (OO p)) ≫ a' →
        Set.range (gPt p ≫ a) ⊆ U → Set.range (gPt p ≫ a') ⊆ U → a = a')
    {T V : Scheme.{0}} (g : T ⟶ X) [Etale g] (h : V ⟶ W) [Etale h] (f : V ⟶ T)
    [IsFinite f] (sq : h ≫ u = f ≫ g)
    (hmono : ∀ (Z : Scheme.{0}) (a b : Z ⟶ V), a ≫ h = b ≫ h → a ≫ f = b ≫ f → a = b)
    (v : V) (hv : h v = w)
    (hgeo : ∀ (K : Type) [Field K] (a b : Spec (.of K) ⟶ V), a ≫ f = b ≫ f →
      (a ≫ f) (IsLocalRing.closedPoint K) = f v →
        a ≫ h = b ≫ h ∧ (a ≫ h) (IsLocalRing.closedPoint K) = w) :
    ∃ V : W.Opens, w ∈ V ∧ Etale (V.ι ≫ u) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (g ≫ π)
  have := IsNormalScheme.of_pred hN
  have := isNormalScheme_of_smooth g
  let T' : T.Opens :=
    IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents (f v)⟩
  have hv' : v ∈ f ⁻¹ᵁ T' := mem_irreducibleComponent
  have hcomp : ∀ {Z : Scheme.{0}} {a b : Z ⟶ (f ⁻¹ᵁ T').toScheme}, a ≫ f ∣_ T' = b ≫ f ∣_ T' →
      (a ≫ (f ⁻¹ᵁ T').ι) ≫ f = (b ≫ (f ⁻¹ᵁ T').ι) ≫ f := fun e => by
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% e]
  refine exists_opens_etale_of_finite_etale_localisation_of_isIntegral X π hN W u w U hw hU huniq
    (T'.ι ≫ g) ((f ⁻¹ᵁ T').ι ≫ h) (f ∣_ T') ?_ (fun Z a b e₁ e₂ => ?_) ⟨v, hv'⟩ ?_
    fun K _ a b e hc => ?_
  · rw [Category.assoc, sq, morphismRestrict_ι_assoc]
  · rw [← cancel_mono (f ⁻¹ᵁ T').ι]
    exact hmono _ _ _ (by simpa only [Category.assoc] using e₁) (hcomp e₂)
  · rw [Scheme.Hom.comp_apply]
    exact hv
  · have := hgeo K _ _ (hcomp e) (by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_apply, hc,
        ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
      rfl)
    simpa only [Category.assoc] using this

theorem exists_opens_etale_of_unique_classical_points :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (W : Scheme.{0}) [IsIntegral W] (u : W ⟶ X) [LocallyOfFiniteType u] [IsSeparated u] [IsDominant u] (w : W) (U : W.Opens), IsClosed ({w} : Set W) → u.QuasiFiniteAt w → (U : Set W).Nonempty → (∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W), a ≫ u = a' ≫ u → a (cPt p) = w → spMap (IsLocalRing.residue (OO p)) ≫ a = spMap (IsLocalRing.residue (OO p)) ≫ a' → Set.range (gPt p ≫ a) ⊆ U → Set.range (gPt p ≫ a') ⊆ U → a = a') → ∃ V : W.Opens, w ∈ V ∧ Etale (V.ι ≫ u) := by
  intro X _ π _ _ hN W _ u _ _ _ w U hw hqf hU huniq

  let Q : W.Opens := u.quasiFiniteLocus
  let w₀ : Q := ⟨w, hqf⟩
  let u₀ : Q.toScheme ⟶ X := Q.ι ≫ u
  have hw₀ : IsClosed ({w₀} : Set Q) := by
    have := hw.preimage Q.ι.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff

  have : Finite (Q.toScheme.residueField w₀) :=
    (jacobson_closedPoints_tools_int Q (u₀ ≫ π)).2.1 w₀ hw₀
  obtain ⟨A, _, β, hA, hβ⟩ :=
    @exists_etale_int_surjective_of_finite_field (Q.toScheme.residueField w₀)
      (Scheme.instFieldCarrierResidueField _ _) this
  let ρ : Sp A ⟶ Sp ℤ := spMap (Int.castRingHom A)
  have : Etale ρ := HasRingHomProperty.Spec_iff.mpr hA
  let g₁ := pullback.fst π ρ
  let h₁ := pullback.fst u₀ g₁
  let f₁ := pullback.snd u₀ g₁
  let β' : Spec (Q.toScheme.residueField w₀) ⟶ Sp A := spMap β
  let ξ₀ : Spec (Q.toScheme.residueField w₀) ⟶ pullback π ρ :=
    pullback.lift (Q.toScheme.fromSpecResidueField w₀ ≫ u₀) β' (specZIsTerminal.hom_ext _ _)
  let ξ : Spec (Q.toScheme.residueField w₀) ⟶ pullback u₀ g₁ :=
    pullback.lift (Q.toScheme.fromSpecResidueField w₀) ξ₀ (pullback.lift_fst _ _ _).symm
  have hξ : ξ ≫ h₁ = Q.toScheme.fromSpecResidueField w₀ := pullback.lift_fst _ _ _
  have hξ' : ξ ≫ f₁ ≫ pullback.snd π ρ = β' := by
    rw [pullback.lift_snd_assoc, pullback.lift_snd]
  let w₁ := ξ (IsLocalRing.closedPoint (Q.toScheme.residueField w₀))
  have hw₁ : h₁ w₁ = w₀ := by
    rw [← Scheme.Hom.comp_apply, hξ, Scheme.fromSpecResidueField_apply]
  have hgeo₁ : ∀ (K : Type) [Field K] (a b : Spec (.of K) ⟶ pullback u₀ g₁), a ≫ f₁ = b ≫ f₁ →
      a (IsLocalRing.closedPoint K) = w₁ → b (IsLocalRing.closedPoint K) = w₁ → a = b := by
    intro K _ a b e ha hb
    obtain ⟨σ, rfl⟩ := exists_factor_of_lift_fromSpecResidueField h₁ w₀ ξ hξ a ha
    obtain ⟨τ, rfl⟩ := exists_factor_of_lift_fromSpecResidueField h₁ w₀ ξ hξ b hb
    have e' := congr($e ≫ pullback.snd π ρ)
    simp only [Category.assoc, hξ'] at e'
    have e'' : CommRingCat.ofHom β ≫ σ = CommRingCat.ofHom β ≫ τ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp]
      exact e'
    have : σ = τ := by
      ext z
      obtain ⟨z, rfl⟩ := hβ z
      exact congr($e'' z)
    rw [this]

  obtain ⟨O, hO, hOw⟩ : ∃ O : Set ↥(pullback u₀ g₁), IsOpen O ∧ O ∩ f₁ ⁻¹' {f₁ w₁} = {w₁} :=
    isDiscrete_iff_forall_exists_isOpen.mp (f₁.isDiscrete_preimage_singleton (f₁ w₁)) w₁ rfl
  let O' : (pullback u₀ g₁).Opens := ⟨O, hO⟩
  let w₂ : O' := ⟨w₁, (hOw.ge rfl).1⟩
  let f₂ := O'.ι ≫ f₁
  obtain ⟨T, g, _, -, V, -, v, -, _, hv⟩ :=
    exists_etale_isCompl_of_quasiFiniteAt f₂ (x := w₂) rfl (f₂.quasiFiniteAt w₂)
  let k : V.toScheme ⟶ pullback u₀ g₁ := V.ι ≫ pullback.fst f₂ g ≫ O'.ι
  let f : V.toScheme ⟶ T := V.ι ≫ pullback.snd f₂ g
  have hk : k ≫ f₁ = f ≫ g := by
    simp only [k, f, Category.assoc]
    rw [← pullback.condition]
  have hkv : k v = w₁ := by
    simp only [k, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, hv]
    rfl
  have hfib : ∀ z : V.toScheme, f z = f v → k z = w₁ := fun z hz => by
    refine hOw.le ⟨(pullback.fst f₂ g (V.ι z)).2, ?_⟩
    change f₁ (k z) = f₁ w₁
    rw [← hkv, ← Scheme.Hom.comp_apply k f₁, ← Scheme.Hom.comp_apply k f₁, hk,
      Scheme.Hom.comp_apply f g, Scheme.Hom.comp_apply f g, hz]
  refine exists_opens_etale_of_finite_etale_localisation X π hN W u w U hw hU huniq
    (g ≫ g₁) (k ≫ h₁ ≫ Q.ι) f ?_ (fun Z a b e₁ e₂ => ?_) v ?_ fun K _ a b e hc => ?_
  · rw [← reassoc_of% hk, ← pullback.condition (f := u₀) (g := g₁)]
    simp only [Category.assoc]
    rfl
  · have e₃ : a ≫ k = b ≫ k := by
      apply pullback.hom_ext
      · rw [← cancel_mono Q.ι]
        simpa only [Category.assoc] using e₁
      · rw [Category.assoc a k, Category.assoc b k, hk, reassoc_of% e₂]
    rw [← cancel_mono V.ι]
    apply pullback.hom_ext
    · rw [← cancel_mono O'.ι]
      simpa only [Category.assoc] using e₃
    · simpa only [Category.assoc] using e₂
  · rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hkv, hw₁]
    rfl
  · have ha : (a ≫ k) (IsLocalRing.closedPoint K) = w₁ := hfib _ hc
    have hb : (b ≫ k) (IsLocalRing.closedPoint K) = w₁ := hfib _ (e ▸ hc :
      (b ≫ f) (IsLocalRing.closedPoint K) = f v)
    have := hgeo₁ K _ _ (by
      rw [Category.assoc a k, Category.assoc b k, hk, reassoc_of% e]) ha hb
    refine ⟨by rw [reassoc_of% this], ?_⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply, ha, Scheme.Hom.comp_apply, hw₁]
    rfl

end GlobalTheory
