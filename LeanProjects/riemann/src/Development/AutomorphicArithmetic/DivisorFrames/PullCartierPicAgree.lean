import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

private theorem isDominant_of_generic_points {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (p : W ⟶ X)
    (φ : X.functionField →+* W.functionField) (h : gpt W ≫ p = spMap φ ≫ gpt X) : IsDominant p := by
  have h1 : p (gpt W (closedPoint W.functionField)) = gpt X (spMap φ (closedPoint W.functionField)) :=
    congrArg (fun q : Sp W.functionField ⟶ X => q (closedPoint W.functionField)) h
  have h2 : spMap φ (closedPoint W.functionField) = closedPoint X.functionField :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  have h3 : gpt X (closedPoint X.functionField) = genericPoint X := Scheme.fromSpecStalk_closedPoint
  rw [h2, h3] at h1
  refine ⟨fun x => ?_⟩
  have : x ∈ closure ({genericPoint X} : Set X) := by rw [(genericPoint_spec X).def]; trivial
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range.2 ⟨_, h1⟩)) this

private theorem functionFieldMap_eq_of_generic {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (p : W ⟶ X) [IsDominant p]
    (φ : X.functionField →+* W.functionField) (h : gpt W ≫ p = spMap φ ≫ gpt X) : functionFieldMap p = φ := by
  have e : spMap (functionFieldMap p) ≫ gpt X = spMap φ ≫ gpt X := (specMap_functionFieldMap p).trans h
  have e' := Spec.map_injective ((cancel_mono (X.fromSpecStalk (genericPoint X))).mp e)
  exact congrArg CommRingCat.Hom.hom e'

private theorem valuation_agree_common_model {X₁ X₂ W : Scheme.{0}} [IsIntegral X₁] [IsIntegral X₂] [IsIntegral W]
    (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂) (θ : X₂.functionField →+* X₁.functionField)
    (ε : X₁.functionField ≃+* W.functionField) (h₁ : gpt W ≫ p₁ = spMap ε.toRingHom ≫ gpt X₁)
    (h₂ : gpt W ≫ p₂ = spMap ε.toRingHom ≫ spMap θ ≫ gpt X₂) {D₁ : CartierDiv X₁} {D₂ : CartierDiv X₂}
    (h : DvrAgree θ D₁ D₂) (w : W) {g₁ : X₁.functionFieldˣ} {g₂ : X₂.functionFieldˣ} (e₁ : D₁.IsEqn (p₁ w) g₁)
    (e₂ : D₂.IsEqn (p₂ w) g₂) (V : ValuationSubring W.functionField) (hV : IsDiscreteValuationRing V)
    (hr : ∀ r : W.presheaf.stalk w, algebraMap _ W.functionField r ∈ V)
    (hm : ∀ r ∈ maximalIdeal (W.presheaf.stalk w), algebraMap _ W.functionField r ∈ V.nonunits) :
    ε g₁ / ε (θ g₂) ∈ V ∧ (ε g₁ / ε (θ g₂))⁻¹ ∈ V := by
  let R : ValuationSubring X₁.functionField := V.comap ε.toRingHom
  have hmem (x : X₁.functionField) : x ∈ R ↔ ε x ∈ V := Iff.rfl
  let j : V ≃+* R :=
    { toFun := fun v => ⟨ε.symm v, (hmem _).2 (by simp)⟩
      invFun := fun v => ⟨ε v, (hmem _).1 v.2⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hR : IsDiscreteValuationRing R := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing j
  obtain ⟨hr', hloc⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ V).1
    ((localSubring_range_le_valuationSubring_iff _ V).2 ⟨hr, hm⟩)
  let ψ : W.presheaf.stalk w →+* R := j.toRingHom.comp ((algebraMap _ W.functionField).codRestrict V hr')
  have : IsLocalHom j.toRingHom := ⟨fun a ha => (isLocalHom_equiv j).1 a ha⟩
  have : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
  let c : Sp R ⟶ W := spMap ψ ≫ W.fromSpecStalk w
  have hc : c (closedPoint R) = w := by
    have : spMap ψ (closedPoint R) = closedPoint (W.presheaf.stalk w) := IsLocalRing.comap_closedPoint ψ
    change W.fromSpecStalk w (spMap ψ (closedPoint R)) = w
    rw [this]
    exact Scheme.fromSpecStalk_closedPoint
  have hg : spMap R.subtype ≫ c = spMap ε.symm.toRingHom ≫ gpt W := by
    have : R.subtype.comp ψ = ε.symm.toRingHom.comp (algebraMap _ W.functionField) := rfl
    have e : spMap (algebraMap (W.presheaf.stalk w) W.functionField) ≫ W.fromSpecStalk w = gpt W :=
      specAlgebraMap_fromSpecStalk w
    rw [← e, ← Category.assoc, ← Category.assoc, spectrumMap_comp, spectrumMap_comp, this]
  have hid : spMap ε.symm.toRingHom ≫ spMap ε.toRingHom = 𝟙 _ := by
    rw [spectrumMap_comp, RingEquiv.symm_toRingHom_comp_toRingHom]
    exact Spec.map_id _
  have key := h R hR (c ≫ p₁) (c ≫ p₂)
    (by rw [← Category.assoc, hg, Category.assoc, h₁, ← Category.assoc, hid, Category.id_comp])
    (by rw [← Category.assoc, hg, Category.assoc, h₂, ← Category.assoc, hid, Category.id_comp])
    g₁ g₂ (by change D₁.IsEqn (p₁ (c (closedPoint R))) g₁; rw [hc]; exact e₁)
    (by change D₂.IsEqn (p₂ (c (closedPoint R))) g₂; rw [hc]; exact e₂)
  have h0 : R.valuation (θ g₂) ≠ 0 := by simp
  have k : R.valuation (g₁ / θ g₂) = 1 := by rw [map_div₀, key, div_self h0]
  rw [← map_div₀, ← map_inv₀, ← hmem, ← hmem, ← R.valuation_le_one_iff, ← R.valuation_le_one_iff, map_inv₀, k, inv_one]
  exact ⟨le_rfl, le_rfl⟩

theorem UpperTheory.pull_cartier_pic_agree :
    ∀ (X₁ X₂ W : Scheme.{0}) [IsIntegral X₁] [IsIntegral X₂] [IsIntegral W] [IsLocallyNoetherian W] (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂) (θ : X₂.functionField →+* X₁.functionField) (ε : X₁.functionField ≃+* W.functionField), GlobalTheory.IsNormalScheme W → gpt W ≫ p₁ = spMap ε.toRingHom ≫ gpt X₁ → gpt W ≫ p₂ = spMap ε.toRingHom ≫ spMap θ ≫ gpt X₂ → ∀ (D₁ : CartierDiv X₁) (D₂ : CartierDiv X₂), DvrAgree θ D₁ D₂ → pull p₁ (toPic D₁) = pull p₂ (toPic D₂) := by
  intro X₁ X₂ W _ _ _ _ p₁ p₂ θ ε hN h₁ h₂ D₁ D₂ h
  have h₂' : gpt W ≫ p₂ = spMap (ε.toRingHom.comp θ) ≫ gpt X₂ := by
    rw [h₂, ← Category.assoc, spectrumMap_comp]
  have := isDominant_of_generic_points p₁ _ h₁
  have := isDominant_of_generic_points p₂ _ h₂'
  have f₁ := functionFieldMap_eq_of_generic p₁ _ h₁
  have f₂ := functionFieldMap_eq_of_generic p₂ _ h₂'
  have e : DomPull.pullback p₁ D₁ = DomPull.pullback p₂ D₂ := by
    refine CartierDiv.ext_of_isEqn fun w => ?_
    obtain ⟨g₁, e₁⟩ := D₁.exists_isEqn (p₁ w)
    obtain ⟨g₂, e₂⟩ := D₂.exists_isEqn (p₂ w)
    refine ⟨_, DomPull.isEqn_pullback p₁ D₁ e₁, (DomPull.isEqn_pullback p₂ D₂ e₂).iff_unitAt.2 ?_⟩
    obtain ⟨_, _⟩ := (GlobalTheory.isNormalScheme_iff _).1 hN w
    have hu : UnitAt w (ε g₁ / ε (θ g₂)) := by
      refine (unitAt_iff (by simp)).2 ⟨?_, ?_⟩
      · exact exists_algebraMap_eq_of_forall_discreteValuationSubring fun V hV hr hm =>
          (valuation_agree_common_model p₁ p₂ θ ε h₁ h₂ h w e₁ e₂ V hV hr hm).1
      · exact exists_algebraMap_eq_of_forall_discreteValuationSubring fun V hV hr hm =>
          (valuation_agree_common_model p₁ p₂ θ ε h₁ h₂ h w e₁ e₂ V hV hr hm).2
    change UnitAt w (functionFieldMap p₁ g₁ / functionFieldMap p₂ g₂)
    rw [f₁, f₂]
    exact hu
  have c₁ := (DomPull.presents_pullback p₁ D₁).toPic_eq
  have c₂ := (DomPull.presents_pullback p₂ D₂).toPic_eq
  rw [cls_pull (isLB_toLB D₁)] at c₁
  rw [cls_pull (isLB_toLB D₂)] at c₂
  rw [toPic_apply, toPic_apply, ← c₁, ← c₂, e]
