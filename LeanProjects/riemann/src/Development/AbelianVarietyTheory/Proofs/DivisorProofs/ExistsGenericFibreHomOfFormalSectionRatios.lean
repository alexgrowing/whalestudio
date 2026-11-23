import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerUniformisedGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismOfSectionRatiosVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfMulAtDominantPairCommGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomExtensionOpenPartFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveActionThickeningEndosCompletePointStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GenericRatio

theorem exists_complete_point (T : Scheme.{0}) [IsLocallyNoetherian T] (t : T) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B), IsAdicComplete (maximalIdeal B) B ∧
      ∃ q : Sp B ⟶ T, Flat q ∧ q (closedPoint B) = t := by
  let O : Type := T.presheaf.stalk t
  have : IsNoetherianRing O := inferInstanceAs (IsNoetherianRing (T.presheaf.stalk t))
  refine ⟨AdicCompletion (maximalIdeal O) O, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O))) ≫ T.fromSpecStalk t, ?_, ?_⟩
  · have h1 : Flat (T.fromSpecStalk t) := GenericExt.flat_fromSpecStalk T t
    have h2 : Flat (Spec.map (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    exact Flat.comp _ _
  · have : IsLocalHom (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O))).hom :=
      inferInstanceAs (IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O)))
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (T.fromSpecStalk t) Spec_closedPoint).trans
      Scheme.fromSpecStalk_closedPoint)

theorem secRatioEq_of_levels {B : Type} [CommRing B] [IsLocalRing B] [IsHausdorff (maximalIdeal B) B]
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {k k' : ℕ} {u v : Sp B ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'}
    (h : ∀ e, SecRatioEq L (thick B (maximalIdeal B) e ≫ u) (thick B (maximalIdeal B) e ≫ v) s₁ s₂ t₁ t₂) :
    SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  have top : ∀ w : Sp B ⟶ X, ∃ i : Fin 1 → L.ι, ⊤ ≤ w ⁻¹ᵁ secChart L i := fun w => by
    obtain ⟨i, hi⟩ := exists_chart hL (w (closedPoint B))
    have : closedPoint B ∈ w ⁻¹ᵁ secChart L (fun _ => i) := Set.mem_iInter.2 fun _ => hi
    exact ⟨fun _ => i, ((IsLocalRing.closedPoint_mem_iff _).1 this).ge⟩
  obtain ⟨i, hi⟩ := top u
  obtain ⟨i', hi'⟩ := top v
  have key : ∀ (s : H0 L k) (t : H0 L k') (Z : Scheme.{0}) (r : Z ⟶ Sp B) (z : Z),
      gs r z ⊤ ((u.appLE _ ⊤ hi).hom (s.f i) * (v.appLE _ ⊤ hi').hom (t.f i')) =
        secGerm (r ≫ u) z s i * secGerm (r ≫ v) z t i' := fun s t Z r z =>
    (gs_mul r z ⊤ trivial _ _).trans (congrArg₂ (· * ·) (gs_appLE u _ ⊤ hi r z trivial _)
      (gs_appLE v _ ⊤ hi' r z trivial _))
  have E := GlobalTheory.FormalGeneric.fn_ext_germs (maximalIdeal B) (a := (u.appLE _ ⊤ hi).hom (s₁.f i) *
      (v.appLE _ ⊤ hi').hom (t₂.f i')) (b := (u.appLE _ ⊤ hi).hom (s₂.f i) * (v.appLE _ ⊤ hi').hom (t₁.f i'))
    fun e z => (key _ _ _ _ z).trans ((secRatioEq_iff_germ.1 (h e) z i i' (hi trivial) (hi' trivial)).trans
      (key _ _ _ _ z).symm)
  refine secRatioEq_of_exists_germ fun y => ⟨i, i', hi trivial, hi' trivial, ?_⟩
  exact (key s₁ t₂ _ (𝟙 _) y).symm.trans ((congrArg _ E).trans (key s₂ t₁ _ (𝟙 _) y))

theorem exists_generic_mem {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) [Flat f]
    (W : Y.Opens) {y : Y} (hy : y ∈ W) : ∃ a : (pullback f (jK R) :), pullback.fst f (jK R) a ∈ W := by
  let ξ : Sp R := jK R (closedPoint (FractionRing R))
  have hξ : ξ ⤳ f y := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun r hr => ?_
    have h1 : algebraMap R (FractionRing R) r ∈ maximalIdeal (FractionRing R) := hr
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot,
      map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
    rw [h1]
    exact Ideal.zero_mem _
  obtain ⟨y', h1, h2⟩ := Flat.generalizingMap f hξ
  have : y' ∈ Set.range (pullback.fst f (jK R)) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨_, h2.symm⟩
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha ▸ h1.mem_open W.isOpen hy⟩

theorem isDominant_of_flat {X Y : Scheme.{0}} [IrreducibleSpace X] (f : Y ⟶ X) [Flat f] (y : Y) : IsDominant f := by
  obtain ⟨y', -, h2⟩ := Flat.generalizingMap f (genericPoint_specializes (f y))
  refine ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨y', h2⟩) ?_⟩
  exact dense_iff_closure_eq.2 (genericPoint_spec X)

theorem exists_formal_pair {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Sp R)) [GrpObj G] [LocallyOfFiniteType G.hom]
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (hb : ∀ e, IsMonHom (b e))
    (hc : ∀ e, thickMap R (maximalIdeal R) e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R (maximalIdeal R) e G)
    {L : LB G.left} (hL : L.IsLB) :
    ∃ (Y : Over (Sp R)) (x₁ x₂ : Y ⟶ G) (Φ : (Y ⟶ G) → (Y ⟶ G)), Nonempty Y.left ∧ Flat (lift x₁ x₂).left ∧
      (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Y ⟶ G) (k k' : ℕ) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k'),
        (∀ e, SecRatioEq L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left
          s₁ s₂ t₁ t₂) → SecRatioEq L (Φ x).left x.left s₁ s₂ t₁ t₂ := by
  have : LocallyOfFiniteType (G ⊗ G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G.hom ≫ G.hom))
  have : IsLocallyNoetherian (G ⊗ G).left := LocallyOfFiniteType.isLocallyNoetherian (G ⊗ G).hom
  let o : 𝟙_ (Over (Sp R)) ⟶ G ⊗ G := lift 1 1
  obtain ⟨B, _, _, hB, q, hq, hqt⟩ := exists_complete_point (G ⊗ G).left (o.left (closedPoint R))
  have hs : (q ≫ (G ⊗ G).hom) (closedPoint B) ∈ Set.range (thick R (maximalIdeal R) 0) := by
    have h1 : (q ≫ (G ⊗ G).hom) (closedPoint B) = closedPoint R :=
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (G ⊗ G).hom hqt).trans
        ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun g => g (closedPoint R)) (Over.w o))))
    exact ⟨_, (GlobalTheory.adicLevelι_closedPoint (maximalIdeal.isMaximal R).ne_top 0).trans h1.symm⟩
  obtain ⟨Φ, hΦ, hr⟩ := GlobalTheory.T.exists_additive_action_thickeningEndos_completePoints R (maximalIdeal R) G b hb hc B (q ≫ (G ⊗ G).hom) hs
  let q' : Over.mk (q ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk q rfl
  refine ⟨Over.mk (q ≫ (G ⊗ G).hom), q' ≫ fst G G, q' ≫ snd G G, Φ, ⟨closedPoint B⟩, ?_, hΦ,
    fun x k k' s₁ s₂ t₁ t₂ h => secRatioEq_of_levels hL fun e => ?_⟩
  · rw [lift_comp_fst_snd]
    exact hq
  · obtain ⟨r, h1, h2⟩ := hr x e
    have h3 := (h e).comp r
    exact h1 ▸ h2 ▸ h3

theorem exists_generic_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), 1 ≤ N → (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∃ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ ∧ (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' _ b hb N S _ hS hnd
  have := hR.1.1
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  let F := Over.pullback (jK R)
  let π : (F.obj G).left ⟶ G.left := pullback.fst G.hom (jK R)
  have hA : GlobalTheory.SS.SmConn (F.obj G) := ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd G.hom (jK R))),
    inferInstanceAs (IsSeparated (pullback.snd G.hom (jK R))),
    inferInstanceAs (QuasiCompact (pullback.snd G.hom (jK R))),
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (jK R)))⟩
  have := hA.2.1
  have := hA.2.2.2.2
  have hint : IsIntegral (F.obj G).left := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (F.obj G).hom
  obtain ⟨m, σ, hσ⟩ := GlobalTheory.T.exists_veryAmple_fourth_power_uniformised_group R (maximalIdeal R) D A G U
  obtain ⟨s₀, y₀, i₀, i₀', -, hy₀⟩ := hnd 4 (by norm_num)
  have ht₀ : ∃ p : (F.obj G).left, π p ∈ nonzeroLocus (S 4 s₀) := by
    refine exists_generic_mem G.hom _ (y := (fstG (maximalIdeal R) 0 G).left y₀) ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i₀', (Scheme.preimage_basicOpen _ _).ge hy₀⟩
  obtain ⟨Y, x₁, x₂, Φ, ⟨y⟩, hfl, hΦ, hrat⟩ := exists_formal_pair G b hb.1 hb.2.1 U.LG.isLB
  have hπ : ∀ x : Y ⟶ G, (F.map x).left ≫ π = pullback.fst Y.hom (jK R) ≫ x.left := fun x =>
    pullback.lift_fst _ _ _
  have hratK : ∀ (x : Y ⟶ G) (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((F.map (Φ x)).left ≫ π)
      ((F.map x).left ≫ π) s₁ s₂ (S k s₁) (S k s₂) := fun x k s₁ s₂ => by
    rw [hπ, hπ]
    exact (hrat x k _ s₁ s₂ _ _ fun e => hS k e s₁ s₂).comp _
  have hflK : Flat (lift (F.map x₁) (F.map x₂)).left := by
    rw [← Functor.OplaxMonoidal.lift_δ, Over.comp_left]
    have h1 : Flat (F.map (lift x₁ x₂)).left := MorphismProperty.overPullbackMap (P := @Flat) (jK R) _ hfl
    have h2 : IsIso (Functor.OplaxMonoidal.δ F G G).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (Functor.OplaxMonoidal.δ F G G)))
    infer_instance
  have hYfl : Flat Y.hom := by
    have : Flat (G ⊗ G).hom := inferInstanceAs (Flat (pullback.fst G.hom G.hom ≫ G.hom))
    rw [← Over.w (lift x₁ x₂)]
    infer_instance
  obtain ⟨yK, -⟩ := exists_generic_mem Y.hom ⊤ (y := y) trivial
  have : Smooth (fst (F.obj G) (F.obj G)).left :=
    inferInstanceAs (Smooth (pullback.fst (F.obj G).hom (F.obj G).hom))
  have : GeometricallyConnected (fst (F.obj G) (F.obj G)).left :=
    inferInstanceAs (GeometricallyConnected (pullback.fst (F.obj G).hom (F.obj G).hom))
  have : IsIntegral (F.obj G ⊗ F.obj G).left := by
    have := GlobalTheory.isNormalScheme_of_smooth (S := Sp (FractionRing R)) (F.obj G).hom
    have : IsLocallyNoetherian (F.obj G).left := LocallyOfFiniteType.isLocallyNoetherian (F.obj G).hom
    exact GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (fst (F.obj G) (F.obj G)).left
  have hdom : IsDominant (lift (F.map x₁) (F.map x₂)).left := isDominant_of_flat _ yK
  have hfl₁ : Flat (F.map x₁).left := by
    rw [← lift_fst (F.map x₁) (F.map x₂), Over.comp_left]
    infer_instance
  have hdom₁ : IsDominant (F.map x₁).left := isDominant_of_flat _ yK
  obtain ⟨V, j, f, hj, hV, hf⟩ := GlobalTheory.T.exists_morphism_of_sectionRatios_veryAmple (FractionRing R) (F.obj G) G.left U.LG.L U.LG.isLB π 4 _ m σ hσ s₀
    (S 4 s₀) (fun i => S 4 (σ i)) ht₀ (F.obj Y) (F.map x₁) (F.map (Φ x₁)) hdom₁ fun i => hratK x₁ 4 _ _
  have hpt : ∀ (x : Y ⟶ G) (Z : Over (Sp (FractionRing R))) (w : Z ⟶ F.obj Y) (u : Z ⟶ V),
      u ≫ j = w ≫ F.map x → u ≫ f = w ≫ F.map (Φ x) := fun x Z w u e => hf Z u _ fun i => by
    rw [e, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    exact (hratK x 4 _ _).comp _
  have hadd := GlobalTheory.T.mul_of_mul_at_dominant_pair_commGroup (FractionRing R) (F.obj G) hA V j f hj (F.obj Y) _ _ _ _ hdom (hpt x₁) (hpt x₂)
    (by rw [← Functor.map_mul, ← Functor.map_mul, ← hΦ]; exact hpt (x₁ * x₂))
  obtain ⟨φ, hφ, hjφ⟩ := GlobalTheory.T.exists_monHom_extension_openPart_field (FractionRing R) (F.obj G) (F.obj G) V hA hA j f hj hV hadd
  refine ⟨φ, hφ, fun k s₁ s₂ => ?_⟩
  let Z : Over (Sp (FractionRing R)) := Over.mk (pullback.fst (F.map x₁).left j.left ≫ (F.obj Y).hom)
  let w : Z ⟶ F.obj Y := Over.homMk (pullback.fst (F.map x₁).left j.left) rfl
  let u : Z ⟶ V := Over.homMk (pullback.snd (F.map x₁).left j.left) (by
    have e := congrArg (· ≫ (F.obj G).hom) (pullback.condition (f := (F.map x₁).left) (g := j.left))
    simp only [Category.assoc, Over.w] at e
    exact e.symm)
  have huw : u ≫ j = w ≫ F.map x₁ := Over.OverMorphism.ext pullback.condition.symm
  have e : (w ≫ F.map x₁) ≫ φ = w ≫ F.map (Φ x₁) := by rw [← huw, Category.assoc, hjφ, hpt x₁ Z w u huw]
  obtain ⟨z⟩ : Nonempty Z.left := by
    obtain ⟨v⟩ := hV
    obtain ⟨p, v', hp⟩ := (F.map x₁).left.denseRange.exists_mem_open (IsOpenImmersion.isOpen_range j.left)
      ⟨_, v, rfl⟩
    obtain ⟨z, -⟩ := Scheme.Pullback.exists_preimage_pullback p v' hp.symm
    exact ⟨z⟩
  have : Flat (w ≫ F.map x₁).left :=
    inferInstanceAs (Flat (pullback.fst (F.map x₁).left j.left ≫ (F.map x₁).left))
  have := isDominant_of_flat (w ≫ F.map x₁).left z
  refine SecRatioEq.of_isDominant (Y := (F.obj G).left) (w ≫ F.map x₁).left ?_
  have e' : (w ≫ F.map x₁).left ≫ φ.left ≫ π = w.left ≫ (F.map (Φ x₁)).left ≫ π := by
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
  have h3 := (hratK x₁ k s₁ s₂).comp w.left
  rw [← e', ← Category.assoc w.left] at h3
  exact h3

end GlobalTheory.Mum.GenericRatio
