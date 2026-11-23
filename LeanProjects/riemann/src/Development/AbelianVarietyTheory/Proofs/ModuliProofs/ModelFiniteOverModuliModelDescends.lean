import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isNormalScheme_genericFibre {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : @IsFractionRing O _ F _ β.toAlgebra) {X : Scheme.{0}} (s : X ⟶ Sp O)
    [GlobalTheory.IsNormalScheme X] : GlobalTheory.IsNormalScheme (pullback s (spMap β)) := by
  rename_i hX
  obtain ⟨hd, hi⟩ := hX
  let _ : Algebra O F := β.toAlgebra
  have : IsLocalization (nonZeroDivisors O) F := h
  have hfl : Flat (spMap β) := by
    change Flat (Spec.map (CommRingCat.ofHom β))
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (nonZeroDivisors O))
  have hso : SurjectiveOnStalks (spMap β) := by
    change SurjectiveOnStalks (Spec.map (CommRingCat.ofHom β))
    rw [HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)]
    exact RingHom.surjectiveOnStalks_of_isLocalization (M := nonZeroDivisors O) F
  have : SurjectiveOnStalks (pullback.fst s (spMap β)) :=
    @MorphismProperty.pullback_fst _ _ @SurjectiveOnStalks _ _ _ s (spMap β) _
      (@MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStableUnderBaseChange _ _ _
        SurjectiveOnStalks.stableUnderBaseChange _ _ s) hso
  have iso : ∀ x, (X.presheaf.stalk (pullback.fst s (spMap β) x)) ≃+* ((pullback s (spMap β)).presheaf.stalk x) :=
    fun x => (@asIso _ _ _ _ _ (GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap β)) x)).commRingCatIsoToRingEquiv
  refine ⟨fun x => ?_, fun x => ?_⟩
  · exact (iso x).symm.toMulEquiv.isDomain _
  · exact IsIntegrallyClosed.of_equiv (iso x)

theorem isIso_of_isFinite_of_common_dense_open {U Y T : Scheme.{0}} [IsLocallyNoetherian T]
    [IsReduced Y] [GlobalTheory.IsNormalScheme T] (j : U ⟶ Y) [IsDominant j] (e : Y ⟶ T) [IsFinite e]
    [IsOpenImmersion (j ≫ e)] [IsDominant (j ≫ e)] : IsIso e := by
  obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := GlobalTheory.existsUnique_lift_of_isOpenImmersion_of_isDominant (j ≫ e) e j (𝟙 T)
    (by rw [Category.comp_id])
  have hce : e ≫ c = 𝟙 Y := GlobalTheory.lift_unique_of_isDominant j e (c := e ≫ c) (c' := 𝟙 Y)
    (by rw [← Category.assoc, hc₁, Category.comp_id]) (by rw [Category.assoc, hc₂, Category.comp_id, Category.id_comp])
  exact ⟨⟨c, hce, hc₂⟩⟩

theorem isPullback_genericFibre_of_isFinite {O₀ O K F : Type} [CommRing O₀] [CommRing O] [Field K]
    [Field F] (β₀ : O₀ →+* K) (β : O →+* F) (b : O₀ →+* O) (i : K →+* F)
    (h₀ : @IsFractionRing O₀ _ K _ β₀.toAlgebra) (h : @IsFractionRing O _ F _ β.toAlgebra)
    (hb : β.comp b = i.comp β₀) [Smooth (spMap i)]
    {X Y U : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [GlobalTheory.IsNormalScheme Y]
    (sX : X ⟶ Sp O₀) [LocallyOfFiniteType sX] (sY : Y ⟶ Sp O) (sU : U ⟶ Sp K)
    (π : Y ⟶ X) (w : π ≫ sX = sY ≫ spMap b) [IsFinite (pullback.lift π sY w)]
    (jX : U ⟶ pullback sX (spMap β₀)) [IsOpenImmersion jX] [IsDominant jX]
    (hjX : jX ≫ pullback.snd _ _ = sU)
    (jY : pullback sU (spMap i) ⟶ pullback sY (spMap β)) [IsDominant jY]
    (hjY : jY ≫ pullback.snd _ _ = pullback.snd _ _)
    (e : pullback sY (spMap β) ⟶ pullback sX (spMap β₀))
    (he₁ : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π)
    (he₂ : e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap i)
    (hj : jY ≫ e = pullback.fst _ _ ≫ jX) :
    IsPullback e (pullback.snd _ _) (pullback.snd sX (spMap β₀)) (spMap i) := by
  have hXK : GlobalTheory.IsNormalScheme (pullback sX (spMap β₀)) := isNormalScheme_genericFibre β₀ h₀ sX
  have hYF : GlobalTheory.IsNormalScheme (pullback sY (spMap β)) := isNormalScheme_genericFibre β h sY

  have hspec : spMap i ≫ spMap β₀ = spMap β ≫ spMap b := by
    change Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom β₀) =
      Spec.map (CommRingCat.ofHom β) ≫ Spec.map (CommRingCat.ofHom b)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]

  obtain ⟨g, hg₁, hg₂⟩ : ∃ g : pullback sY (spMap β) ⟶
      pullback (pullback.snd sX (spMap β₀)) (spMap i),
      g ≫ pullback.fst _ _ = e ∧ g ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift e (pullback.snd _ _) he₂, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  obtain ⟨r, hr₁, hr₂⟩ : ∃ r : pullback (pullback.snd sX (spMap β₀)) (spMap i) ⟶ pullback sX (spMap b),
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ ∧
      r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap β := by
    refine ⟨pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spMap β) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
      hspec, Category.assoc]

  have outer := (IsPullback.of_hasPullback (pullback.snd sX (spMap β₀)) (spMap i)).paste_horiz
    (IsPullback.of_hasPullback sX (spMap β₀))
  have sq₁ : IsPullback (pullback.snd _ _) r (spMap β) (pullback.snd sX (spMap b)) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst sX (spMap b)) (v₂₂ := spMap b) (h₃₁ := sX) ?_
      hr₂.symm (IsPullback.of_hasPullback sX (spMap b)).flip
    rw [hr₁, ← hspec]
    exact outer.flip

  have sq₂ : IsPullback g (pullback.fst sY (spMap β)) r (pullback.lift π sY w) := by
    refine IsPullback.of_right ?_ ?_ sq₁
    · rw [hg₂, pullback.lift_snd]
      exact (IsPullback.of_hasPullback sY (spMap β)).flip
    · apply pullback.hom_ext
      · rw [Category.assoc, hr₁, ← Category.assoc, hg₁, he₁, Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, hr₂, ← Category.assoc, hg₂, Category.assoc, pullback.lift_snd,
          pullback.condition]
  have hgfin : IsFinite g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) sq₂.flip inferInstance

  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : pullback sU (spMap i) ⟶ pullback (pullback.snd sX (spMap β₀)) (spMap i),
      m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ jX ∧ m ≫ pullback.snd _ _ = pullback.snd _ _ := by
    refine ⟨pullback.lift (pullback.fst _ _ ≫ jX) (pullback.snd _ _) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, hjX, pullback.condition]
  have hjm : jY ≫ g = m := by
    apply pullback.hom_ext
    · rw [Category.assoc, hg₁, hj, hm₁]
    · rw [Category.assoc, hg₂, hjY, hm₂]
  have sq₃ : IsPullback m (pullback.fst sU (spMap i)) (pullback.fst _ _) jX := by
    refine IsPullback.of_right ?_ hm₁ (IsPullback.of_hasPullback (pullback.snd sX (spMap β₀)) (spMap i)).flip
    rw [hm₂, hjX]
    exact (IsPullback.of_hasPullback sU (spMap i)).flip
  have hmo : IsOpenImmersion m :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) sq₃.flip inferInstance
  have : UniversallyOpen (pullback.fst (pullback.snd sX (spMap β₀)) (spMap i)) :=
    UniversallyOpen.of_flat _
  have hmd : IsDominant m := by
    have := GlobalTheory.isDominant_pullback_fst_of_isOpenMap jX
      (pullback.fst (pullback.snd sX (spMap β₀)) (spMap i)) (Scheme.Hom.isOpenMap _)
    rw [← sq₃.isoPullback_hom_fst]
    infer_instance

  have hPn : GlobalTheory.IsNormalScheme (pullback (pullback.snd sX (spMap β₀)) (spMap i)) :=
    ⟨fun x => (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (pullback.fst _ _)
        (fun y => ⟨hXK.isDomain_stalk y, hXK.isIntegrallyClosed_stalk y⟩) x).1,
      fun x => (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (pullback.fst _ _)
        (fun y => ⟨hXK.isDomain_stalk y, hXK.isIntegrallyClosed_stalk y⟩) x).2⟩
  have : IsReduced (pullback sY (spMap β)) := by
    have : ∀ x, _root_.IsReduced ((pullback sY (spMap β)).presheaf.stalk x) :=
      fun x => by have := hYF.isDomain_stalk x; infer_instance
    exact isReduced_of_isReduced_stalk _
  have : IsOpenImmersion (jY ≫ g) := hjm ▸ hmo
  have : IsDominant (jY ≫ g) := hjm ▸ hmd
  have hgi : IsIso g := isIso_of_isFinite_of_common_dense_open jY g
  exact IsPullback.of_iso_pullback ⟨he₂⟩ (asIso g) hg₁ hg₂

theorem descends_of_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O₀ : Type) [CommRing O₀] (β₀ : O₀ →+* KA l) (C : Cpt Xo.s Xo.univ.t β₀) (b : O₀ →+* O) (_ : (ofModel Y).Above C b (pullback.fst _ _) Y.m0.toSABMap), IsDedFrac β₀ → IsDedFrac β → β.comp b = (IntermediateField.inclusion c.le).toRingHom.comp β₀ → Y.Descends := by
  intro E _ _ _ H D l Xo c O _ β Y O₀ _ β₀ C b A hβ₀ hβ hb

  have hsm : Smooth (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    change Smooth (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion c.le).toRingHom))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    let _ : Algebra (KA l) c.F := (IntermediateField.inclusion c.le).toRingHom.toAlgebra
    have : IsScalarTower ℚ (KA l) c.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : FiniteDimensional ℚ c.F := c.fin
    have : FiniteDimensional (KA l) c.F := Module.Finite.of_restrictScalars_finite ℚ (KA l) c.F
    have : Algebra.IsSeparable (KA l) c.F := Algebra.IsAlgebraic.isSeparable_of_perfectField
    have : Algebra.FormallyEtale (KA l) c.F := Algebra.FormallyEtale.of_isSeparable _ _
    have : Algebra.FinitePresentation (KA l) c.F :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    show Algebra.Smooth (KA l) c.F
    exact ⟨inferInstance, inferInstance⟩

  have hCn : GlobalTheory.IsNormalScheme C.X := ⟨fun x => (C.normal x).1, fun x => (C.normal x).2⟩
  have hYn : GlobalTheory.IsNormalScheme Y.X := ⟨fun x => (Y.normal x).1, fun x => (Y.normal x).2⟩
  have hCft : LocallyOfFiniteType C.s := by
    obtain ⟨N, i, hi, hcomp⟩ := C.proj
    have := isProper_str O₀ N
    rw [← hcomp]
    infer_instance
  obtain ⟨π, hπ, hfin, hjc, φμ, hmu, hφc⟩ : ∃ (π : Y.X ⟶ C.X) (hπ : π ≫ C.s = Y.s ≫ spMap b),
      IsFinite (pullback.lift π Y.s hπ) ∧
      (Y.jQ ≫ pullback.fst _ _) ≫ π = pullback.fst _ _ ≫ C.jQ ≫ pullback.fst _ _ ∧
      ∃ φμ : Y.t.G.left ⟶ C.t.G.left, IsGrpPullback Y.t.G C.t.G π φμ ∧
        Y.m.φ ≫ φμ = Y.m0.toSABMap.φ ≫ C.m.φ :=
    ⟨A.π, A.π_over, A.fin, A.j_comm, A.mu.φ, A.mu.cart, A.φ_comm⟩
  have hspec : spMap β ≫ spMap b = spMap (IntermediateField.inclusion c.le).toRingHom ≫ spMap β₀ := by
    change Spec.map (CommRingCat.ofHom β) ≫ Spec.map (CommRingCat.ofHom b) =
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion c.le).toRingHom) ≫
        Spec.map (CommRingCat.ofHom β₀)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]

  obtain ⟨e, he₁, he₂⟩ : ∃ e : pullback Y.s (spMap β) ⟶ pullback C.s (spMap β₀),
      e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π ∧
      e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    refine ⟨pullback.lift (pullback.fst _ _ ≫ π)
      (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion c.le).toRingHom) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, hπ, ← Category.assoc, pullback.condition, Category.assoc, hspec,
      Category.assoc]
  have hj : Y.jQ ≫ e = pullback.fst _ _ ≫ C.jQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, he₁, ← Category.assoc, hjc, Category.assoc]
    · rw [Category.assoc, he₂, ← Category.assoc, Y.jQ_over, Category.assoc, C.jQ_over,
        pullback.condition]
  have : IsOpenImmersion C.jQ := C.jQ_open
  have : IsDominant C.jQ := ⟨C.jQ_dense⟩
  have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  have hpb := isPullback_genericFibre_of_isFinite β₀ β b (IntermediateField.inclusion c.le).toRingHom
    hβ₀.2.2 hβ.2.2 hb C.s Y.s Xo.s π hπ C.jQ C.jQ_over Y.jQ Y.jQ_over e he₁ he₂ hj

  have hCm : IsGrpPullback Xo.univ.t.G C.t.G (C.jQ ≫ pullback.fst _ _) C.m.φ := C.m.cart
  obtain ⟨φK, hφK₁, hφK₂⟩ : ∃ φK : Xo.univ.t.G.left ⟶ pullback C.t.G.hom (pullback.fst C.s (spMap β₀)),
      φK ≫ pullback.fst _ _ = C.m.φ ∧ φK ≫ pullback.snd _ _ = Xo.univ.t.G.hom ≫ C.jQ := by
    refine ⟨pullback.lift C.m.φ (Xo.univ.t.G.hom ≫ C.jQ) ?_, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
    rw [hCm.1.w, Category.assoc]
  have hGK := isGrpPullback_pullback C.t.G (pullback.fst C.s (spMap β₀))
  have h3 : IsGrpPullback Xo.univ.t.G ((Over.pullback (pullback.fst C.s (spMap β₀))).obj C.t.G)
      C.jQ φK := by
    refine IsGrpPullback.cancel hGK ?_ hφK₂
    have e1 : φK ≫ pullback.fst C.t.G.hom (pullback.fst C.s (spMap β₀)) = C.m.φ := hφK₁
    rw [e1]
    exact hCm

  have h6 := isGrpPullback_pullback Y.t.G (pullback.fst Y.s (spMap β))
  obtain ⟨φ₂, hφ₂₁, hφ₂₂⟩ : ∃ φ₂ : pullback Y.t.G.hom (pullback.fst Y.s (spMap β)) ⟶
      pullback C.t.G.hom (pullback.fst C.s (spMap β₀)),
      φ₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φμ ∧ φ₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ e := by
    refine ⟨pullback.lift (pullback.fst _ _ ≫ φμ) (pullback.snd _ _ ≫ e) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, hmu.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      he₁]
  have h7 : IsGrpPullback ((Over.pullback (pullback.fst Y.s (spMap β))).obj Y.t.G)
      ((Over.pullback (pullback.fst C.s (spMap β₀))).obj C.t.G) e φ₂ := by
    refine IsGrpPullback.cancel hGK ?_ hφ₂₂
    have e1 : φ₂ ≫ pullback.fst C.t.G.hom (pullback.fst C.s (spMap β₀)) =
        pullback.fst Y.t.G.hom (pullback.fst Y.s (spMap β)) ≫ φμ := hφ₂₁
    rw [e1, he₁]
    exact IsGrpPullback.comp h6 hmu

  have hYm : IsGrpPullback Y.oF.t.G Y.t.G (Y.jQ ≫ pullback.fst _ _) Y.m.φ := Y.m.cart
  obtain ⟨ψ, hψ₁, hψ₂⟩ : ∃ ψ : Y.oF.t.G.left ⟶ pullback Y.t.G.hom (pullback.fst Y.s (spMap β)),
      ψ ≫ pullback.fst _ _ = Y.m.φ ∧ ψ ≫ pullback.snd _ _ = Y.oF.t.G.hom ≫ Y.jQ := by
    refine ⟨pullback.lift Y.m.φ (Y.oF.t.G.hom ≫ Y.jQ) ?_, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
    rw [hYm.1.w, Category.assoc]
  have hm0 := Y.m0.toSABMap.cart.1.w
  have h10 : ψ ≫ φ₂ = Y.m0.toSABMap.φ ≫ φK := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφ₂₁, ← Category.assoc, hψ₁, hφc, Category.assoc, hφK₁]
    · rw [Category.assoc, hφ₂₂, ← Category.assoc, hψ₂, Category.assoc, hj, Category.assoc, hφK₂,
        ← Category.assoc, ← Category.assoc, hm0]
  unfold Model.Descends
  exact ⟨_, pullback.snd C.s (spMap β₀), (Over.pullback (pullback.fst C.s (spMap β₀))).obj C.t.G,
    inferInstance, C.jQ, φK, e, (Over.pullback (pullback.fst Y.s (spMap β))).obj Y.t.G, inferInstance,
    pullback.fst Y.t.G.hom (pullback.fst Y.s (spMap β)), φ₂, ψ, C.jQ_open, C.jQ_over, h3, hpb, hj,
    h6, h7, hψ₁, hψ₂, h10⟩

end GlobalTheory
