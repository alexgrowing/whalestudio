import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfIsPullbackSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.OntoFinite

theorem eq_genericPoint {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) (g : ℕ) (hX : SmoothOfRelativeDimension g (f ≫ p))
    (hY : SmoothOfRelativeDimension g p) (x : X) (hx : f x = genericPoint Y) : x = genericPoint X := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := f x) trivial
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := f ⁻¹ᵁ U) (x := x) hxU
  have hVU : V ≤ f ⁻¹ᵁ U := hVU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  obtain ⟨α, hα⟩ := Spec.map_surjective (hU.fromSpec ≫ p)
  let φ := f.appLE U V hVU
  have sq : Spec.map φ ≫ hU.fromSpec = hV.fromSpec ≫ f := hU.SpecMap_appLE_fromSpec f hV hVU
  algebraize [α.hom, φ.hom, φ.hom.comp α.hom]
  have t₁ : Algebra.trdeg K Γ(Y, U) = g :=
    trdeg_eq_of_smoothOfRelativeDimension K Y p g hY Γ(Y, U) hU.fromSpec inferInstance hα.symm
  have t₂ : Algebra.trdeg K Γ(X, V) = g :=
    trdeg_eq_of_smoothOfRelativeDimension K X (f ≫ p) g hX Γ(X, V) hV.fromSpec inferInstance (by
      rw [← Category.assoc, ← sq, Category.assoc, ← hα, ← Spec.map_comp]; rfl)
  obtain ⟨q, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have gU : hU.fromSpec (genericPoint (Spec Γ(Y, U))) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have gV : hV.fromSpec (genericPoint (Spec Γ(X, V))) = genericPoint X := genericPoint_eq_of_isOpenImmersion _
  have e : Spec.map φ q = genericPoint (Spec Γ(Y, U)) := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [gU, ← hx, ← Scheme.Hom.comp_apply, sq, Scheme.Hom.comp_apply]
  rw [genericPoint_eq_bot_of_affine] at e
  have e' : q.asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V)) = ⊥ := congrArg PrimeSpectrum.asIdeal e
  have : FaithfulSMul Γ(Y, U) Γ(X, V) := by
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← e']
    exact Ideal.ker_le_comap _
  have : FaithfulSMul K Γ(Y, U) := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact RingHom.injective _
  have h := trdeg_add_eq K Γ(Y, U) (A := Γ(X, V))
  rw [t₁, t₂] at h
  have h0 : Algebra.trdeg Γ(Y, U) Γ(X, V) = 0 :=
    Cardinal.eq_of_add_eq_add_left (h.trans (add_zero _).symm) (Cardinal.natCast_lt_aleph0)
  have halg : Algebra.IsAlgebraic Γ(Y, U) Γ(X, V) := trdeg_eq_zero_iff.1 h0
  have hq : q.asIdeal = ⊥ := by
    by_contra hne
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact Ideal.comap_ne_bot_of_algebraic_mem ha0 ha (halg.isAlgebraic a) e'
  rw [← gV, genericPoint_eq_bot_of_affine]
  exact congrArg _ (PrimeSpectrum.ext hq)

theorem quasiFiniteAt_genericPoint {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f] (g : ℕ)
    (hX : SmoothOfRelativeDimension g (f ≫ p)) (hY : SmoothOfRelativeDimension g p) :
    f.QuasiFiniteAt (genericPoint X) := by
  obtain ⟨x, hx⟩ := f.surjective (genericPoint Y)
  obtain rfl := eq_genericPoint p f g hX hY x hx
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : Subsingleton (f.fiber (f (genericPoint X))) := by
    refine (f.fiberHomeo _).toEquiv.subsingleton_congr.2 ⟨fun a b => Subtype.ext ?_⟩
    exact (eq_genericPoint p f g hX hY a.1 (a.2.trans hx)).trans
      (eq_genericPoint p f g hX hY b.1 (b.2.trans hx)).symm
  exact isOpen_discrete _

theorem isIso_transl {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) :
    IsIso ((toUnit A ≫ x) * 𝟙 A).left := by
  have hu (t : A ⟶ A) : t ≫ toUnit A = toUnit A := toUnit_unique _ _
  suffices IsIso ((toUnit A ≫ x) * 𝟙 A) from inferInstanceAs (IsIso ((Over.forget S).map ((toUnit A ≫ x) * 𝟙 A)))
  refine ⟨(toUnit A ≫ x)⁻¹ * 𝟙 A, ?_, ?_⟩ <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hu, Category.comp_id, inv_mul_cancel_left,
      mul_inv_cancel_left]

theorem locallyQuasiFinite_of_quasiFiniteAt {K : Type} [Field K] [IsAlgClosed K]
    {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B] [LocallyOfFiniteType A.hom]
    (f : A ⟶ B) [IsMonHom f] [LocallyOfFiniteType f.left] (x : A.left) (hx : f.left.QuasiFiniteAt x) :
    LocallyQuasiFinite f.left := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hpt (y : A.left) (hy : IsClosed ({y} : Set A.left)) : ∃ u : 𝟙_ _ ⟶ A, u.left pt = y :=
    ⟨Over.homMk (pointOfClosedPoint (K := K) A.hom y hy) (pointOfClosedPoint_comp (K := K) A.hom y hy),
      pointOfClosedPoint_apply (K := K) A.hom y hy pt⟩
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints (Z := (f.left.quasiFiniteLocus : Set A.left)) ⟨x, hx⟩
    f.left.quasiFiniteLocus.isOpen.isLocallyClosed
  obtain ⟨u, rfl⟩ := hpt a hac
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  by_contra hne
  obtain ⟨b, hb, hbc⟩ := nonempty_inter_closedPoints (Z := (f.left.quasiFiniteLocus : Set A.left)ᶜ)
    (Set.nonempty_compl.2 fun h => hne (SetLike.coe_injective h))
    f.left.quasiFiniteLocus.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨v, rfl⟩ := hpt b hbc
  have := isIso_transl (v * u⁻¹)
  have := isIso_transl ((v * u⁻¹) ≫ f)
  have e : ((toUnit A ≫ (v * u⁻¹)) * 𝟙 A) ≫ f = f ≫ ((toUnit B ≫ (v * u⁻¹) ≫ f) * 𝟙 B) := by
    rw [MonObj.mul_comp, MonObj.comp_mul f, ← Category.assoc f, toUnit_unique (f ≫ toUnit B) (toUnit A)]
    simp only [Category.assoc, Category.id_comp, Category.comp_id]
  have e₂ : u ≫ ((toUnit A ≫ (v * u⁻¹)) * 𝟙 A) = v := by
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (u ≫ toUnit A) (𝟙 _)]
    simp
  apply hb
  have h₁ : (f.left ≫ ((toUnit B ≫ (v * u⁻¹) ≫ f) * 𝟙 B).left).QuasiFiniteAt (u.left pt) :=
    Scheme.Hom.quasiFiniteAt_comp_iff.2 ha
  rw [← Over.comp_left, ← e, Over.comp_left, Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion,
    ← Scheme.Hom.comp_apply, ← Over.comp_left, e₂] at h₁
  exact h₁

theorem isFinite_of_surjective {K : Type} [Field K] {A B : Over (Sp K)} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g : ℕ} (dA : SmoothOfRelativeDimension g A.hom)
    (dB : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [IsMonHom f] [Surjective f.left] : IsFinite f.left := by
  have := hA.proper
  have := hB.proper
  have : IsProper (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := .of_comp _ B.hom
  let t : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))
  have gA := isGrpPullback_pullback A t
  have gB := isGrpPullback_pullback B t
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hA gA
  have hB' := PolPull.isAbelianScheme_of_isGrpPullback hB gB
  let f' := (Over.pullback t).map f
  have sq : IsPullback (pullback.fst A.hom t) f'.left f.left (pullback.fst B.hom t) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm gB.1
    rw [Over.w, Over.w]
    exact gA.1
  have : Surjective f'.left := MorphismProperty.of_isPullback (P := @Surjective) sq ‹_›
  have : IsProper f'.left := MorphismProperty.of_isPullback (P := @IsProper) sq ‹_›
  have : Surjective t := ⟨fun y => ⟨IsLocalRing.closedPoint _, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Surjective (pullback.fst B.hom t) := inferInstance
  have iA := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA'.smooth hA'.geomConnected
  have iB := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB'.smooth hB'.geomConnected
  have : IsIntegral ((Over.pullback t).obj A).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A).hom
  have : IsIntegral ((Over.pullback t).obj B).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj B).hom
  have := hA'.proper
  have hq := quasiFiniteAt_genericPoint ((Over.pullback t).obj B).hom f'.left g
    (by rw [Over.w]; exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback gA.1 dA)
    ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback gB.1 dB)
  have : LocallyQuasiFinite f.left := Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ sq ‹_›
    inferInstance inferInstance (locallyQuasiFinite_of_quasiFiniteAt f' _ hq)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end GlobalTheory.OntoFinite
