import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonHomExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullbackDegree.EpsPullbackFst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenericHomField

abbrev bc (K : Type) [Field K] : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))

instance flat_bc (K : Type) [Field K] : Flat (bc K) := by
  rw [bc, spMap, Flat.SpecMap_iff]
  exact RingHom.Flat.of_isField (Field.toIsField K) _

instance surjective_bc (K : Type) [Field K] : Surjective (bc K) :=
  ⟨Function.surjective_to_subsingleton _⟩

theorem isPullback_map_left {S T : Scheme.{0}} (φ : T ⟶ S) {X Y : Over S} (u : X ⟶ Y) :
    IsPullback ((Over.pullback φ).map u).left (pullback.fst X.hom φ) (pullback.fst Y.hom φ) u.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd Y.hom φ) (v₁₃ := φ) (h₂₂ := Y.hom) ?_ ?_
    (IsPullback.of_hasPullback Y.hom φ).flip
  · have e1 : ((Over.pullback φ).map u).left ≫ pullback.snd Y.hom φ = pullback.snd X.hom φ :=
      Over.w ((Over.pullback φ).map u)
    have e2 : u.left ≫ Y.hom = X.hom := Over.w u
    rw [e1, e2]
    exact (IsPullback.of_hasPullback X.hom φ).flip
  · simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _

variable {K : Type} [Field K]

theorem map_injective {X Y : Over (Sp K)} {u v : X ⟶ Y}
    (h : (Over.pullback (bc K)).map u = (Over.pullback (bc K)).map v) : u = v := by
  have : Epi (pullback.fst X.hom (bc K)) := Flat.epi_of_flat_of_surjective _
  ext1
  apply (cancel_epi (pullback.fst X.hom (bc K))).1
  rw [← (isPullback_map_left (bc K) u).w, ← (isPullback_map_left (bc K) v).w, h]

theorem map_mul' {X M : Over (Sp K)} [MonObj M] (a b : X ⟶ M) :
    (Over.pullback (bc K)).map (a * b) = (Over.pullback (bc K)).map a * (Over.pullback (bc K)).map b :=
  map_mul (Over.pullback (bc K)).homMonoidHom a b

theorem flat_mul {S : Scheme.{0}} (H V : Over S) [GrpObj H] [Flat H.hom] (j : V ⟶ H)
    [IsOpenImmersion j.left] : Flat ((fst V V ≫ j) * (snd V V ≫ j)).left := by
  let sh : H ⊗ H ⟶ H ⊗ H := lift (fst H H) (fst H H * snd H H)
  let sh' : H ⊗ H ⟶ H ⊗ H := lift (fst H H) ((fst H H)⁻¹ * snd H H)
  have e1 : sh ≫ sh' = 𝟙 _ := by
    ext <;> simp [sh, sh', MonObj.comp_mul, GrpObj.comp_inv]
  have e2 : sh' ≫ sh = 𝟙 _ := by
    ext <;> simp [sh, sh', MonObj.comp_mul, GrpObj.comp_inv]
  have : IsIso sh.left := ⟨sh'.left, by rw [← Over.comp_left, e1]; rfl, by rw [← Over.comp_left, e2]; rfl⟩
  have hm : (fst V V ≫ j) * (snd V V ≫ j) = (j ⊗ₘ j) ≫ sh ≫ snd H H := by
    simp [sh, Hom.mul_def]
  have : Flat (snd H H).left := by
    show Flat (pullback.snd H.hom H.hom); infer_instance
  have : IsOpenImmersion (j ⊗ₘ j).left := by
    rw [Over.tensorHom_left]; infer_instance
  rw [hm, Over.comp_left, Over.comp_left]
  infer_instance

theorem quasiCompact_mul {S : Scheme.{0}} (H V : Over S) [GrpObj H] [IsLocallyNoetherian H.left]
    [QuasiCompact H.hom] [QuasiSeparated H.hom] (j : V ⟶ H) [IsOpenImmersion j.left] :
    QuasiCompact ((fst V V ≫ j) * (snd V V ≫ j)).left := by
  have : QuasiCompact V.hom := by rw [← Over.w j]; infer_instance
  have : QuasiCompact (V ⊗ V).hom := by
    show QuasiCompact (pullback.fst V.hom V.hom ≫ V.hom); infer_instance
  have h2 : QuasiCompact (((fst V V ≫ j) * (snd V V ≫ j)).left ≫ H.hom) := by
    rw [Over.w]; infer_instance
  have h3 : QuasiSeparated H.hom := inferInstance
  exact MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) _ H.hom h3 h2

theorem surjective_mul {K : Type} [Field K] (H V : Over (Sp K)) [GrpObj H] (hH : GlobalTheory.SS.SmConn H)
    (j : V ⟶ H) [IsOpenImmersion j.left] [Nonempty V.left] :
    Surjective ((fst V V ≫ j) * (snd V V ≫ j)).left := by
  have hH' := GlobalTheory.IsogRed.smConn_baseChange (bc K) H hH
  obtain ⟨_, hs, _, _, _⟩ := hH
  obtain ⟨_, hs', _, _, _⟩ := hH'
  have : IsIntegral ((Over.pullback (bc K)).obj H).left :=
    isIntegral_of_smooth_of_geometricallyConnected ((Over.pullback (bc K)).obj H).hom
  have hj' : IsOpenImmersion ((Over.pullback (bc K)).map j).left :=
    MorphismProperty.of_isPullback (isPullback_map_left (bc K) j).flip inferInstance
  have hV' : Nonempty ((Over.pullback (bc K)).obj V).left := by
    obtain ⟨v⟩ := ‹Nonempty V.left›
    obtain ⟨w, -⟩ := (pullback.fst V.hom (bc K)).surjective v
    exact ⟨w⟩
  have hflat : Flat ((Over.pullback (bc K)).map ((fst V V ≫ j) * (snd V V ≫ j))).left :=
    MorphismProperty.of_isPullback (isPullback_map_left (bc K) _).flip (flat_mul H V j)
  have htr : ∀ (a x : 𝟙_ (Over (Sp (AlgebraicClosure K))) ⟶ (Over.pullback (bc K)).obj H),
      x ≫ (GlobalTheory.SS.transl a).hom = a * x := fun a x =>
    (GlobalTheory.GenericHom.point_comp_mul x a (𝟙 _)).trans (by rw [Category.comp_id])
  have hdec : ∀ h : 𝟙_ (Over (Sp (AlgebraicClosure K))) ⟶ (Over.pullback (bc K)).obj H,
      ∃ a x : 𝟙_ (Over (Sp (AlgebraicClosure K))) ⟶ (Over.pullback (bc K)).obj V,
      (a ≫ (Over.pullback (bc K)).map j) * (x ≫ (Over.pullback (bc K)).map j) = h := by
    intro h
    obtain ⟨u, hu⟩ := GlobalTheory.GenericHom.exists_generic ((Over.pullback (bc K)).map j)
      [Iso.refl _, asIso (ι[(Over.pullback (bc K)).obj H]) ≪≫ GlobalTheory.SS.transl h]
    obtain ⟨x, hx⟩ := hu (Iso.refl _) (by simp)
    obtain ⟨a, ha⟩ := hu (asIso (ι[(Over.pullback (bc K)).obj H]) ≪≫ GlobalTheory.SS.transl h) (by simp)
    refine ⟨a, x, ?_⟩
    rw [ha, hx, Iso.trans_hom, ← Category.assoc, htr, asIso_hom, Iso.refl_hom, Category.comp_id,
      ← Hom.inv_def, inv_mul_cancel_right]
  have hrange : ∀ y, y ∈ Set.range ((Over.pullback (bc K)).map ((fst V V ≫ j) * (snd V V ≫ j))).left := by
    intro y
    obtain ⟨h, hh⟩ := GlobalTheory.GenericHom.exists_point_mem ((Over.pullback (bc K)).obj H) (closure {y})
      isClosed_closure.isLocallyClosed ⟨y, subset_closure rfl⟩
    obtain ⟨a, x, hax⟩ := hdec h
    let t := lift a x ≫ Functor.LaxMonoidal.μ (Over.pullback (bc K)) V V
    have ht : t ≫ (Over.pullback (bc K)).map ((fst V V ≫ j) * (snd V V ≫ j)) = h := by
      rw [map_mul', Functor.map_comp, Functor.map_comp, MonObj.comp_mul, ← hax]
      simp only [t, Category.assoc]
      rw [← Category.assoc (Functor.LaxMonoidal.μ _ V V), Functor.Monoidal.μ_fst,
        ← Category.assoc (Functor.LaxMonoidal.μ _ V V), Functor.Monoidal.μ_snd, lift_fst_assoc, lift_snd_assoc]
    have hpt : ((Over.pullback (bc K)).map ((fst V V ≫ j) * (snd V V ≫ j))).left
        (t.left (IsLocalRing.closedPoint (AlgebraicClosure K))) =
        h.left (IsLocalRing.closedPoint (AlgebraicClosure K)) := by
      have := congrArg (fun φ => φ.left (IsLocalRing.closedPoint (AlgebraicClosure K))) ht
      exact this
    exact (hflat.generalizingMap).stableUnderGeneralization_range
      (specializes_iff_mem_closure.2 (hh _)) ⟨_, hpt⟩
  refine ⟨fun y => ?_⟩
  obtain ⟨yb, rfl⟩ := (pullback.fst H.hom (bc K)).surjective y
  obtain ⟨w, rfl⟩ := hrange yb
  exact ⟨pullback.fst _ (bc K) w, by
    rw [← Scheme.Hom.comp_apply, ← (isPullback_map_left (bc K) _).w, Scheme.Hom.comp_apply]⟩

theorem exists_monHom_extension_of_field : ∀ (K : Type) [Field K] (H G V : Over (Sp K)) [GrpObj H] [GrpObj G], GlobalTheory.SS.SmConn H → GlobalTheory.SS.SmConn G → ∀ (j : V ⟶ H) (f : V ⟶ G), IsOpenImmersion j.left → Nonempty V.left → (∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f) → ∃ F : H ⟶ G, IsMonHom F ∧ j ≫ F = f := by
  intro K _ H G V _ _ hH hG j f hj hV hm
  have hj' : IsOpenImmersion ((Over.pullback (bc K)).map j).left :=
    MorphismProperty.of_isPullback (isPullback_map_left (bc K) j).flip hj
  have hV' : Nonempty ((Over.pullback (bc K)).obj V).left := by
    obtain ⟨v⟩ := hV
    obtain ⟨w, -⟩ := (pullback.fst V.hom (bc K)).surjective v
    exact ⟨w⟩
  have hpts : ∀ x y z : 𝟙_ (Over (Sp (AlgebraicClosure K))) ⟶ (Over.pullback (bc K)).obj V,
      (x ≫ (Over.pullback (bc K)).map j) * (y ≫ (Over.pullback (bc K)).map j) = z ≫ (Over.pullback (bc K)).map j →
      (x ≫ (Over.pullback (bc K)).map f) * (y ≫ (Over.pullback (bc K)).map f) = z ≫ (Over.pullback (bc K)).map f := by
    intro x y z hxyz
    obtain ⟨x', rfl⟩ := ((Over.mapPullbackAdj (bc K)).homEquiv _ V).surjective x
    obtain ⟨y', rfl⟩ := ((Over.mapPullbackAdj (bc K)).homEquiv _ V).surjective y
    obtain ⟨z', rfl⟩ := ((Over.mapPullbackAdj (bc K)).homEquiv _ V).surjective z
    simp only [← Adjunction.homEquiv_naturality_right, ← ReciprocityTheory.ChartRestriction.G.Out.UBC.homEquiv_mul] at hxyz ⊢
    exact congrArg _ (hm _ x' y' z' (Equiv.injective _ hxyz))
  obtain ⟨Fb, hFb, hjF⟩ := GlobalTheory.GenericHom.exists_monHom_extension (AlgebraicClosure K)
    ((Over.pullback (bc K)).obj H) ((Over.pullback (bc K)).obj G) ((Over.pullback (bc K)).obj V)
    (GlobalTheory.IsogRed.smConn_baseChange _ H hH) (GlobalTheory.IsogRed.smConn_baseChange _ G hG)
    ((Over.pullback (bc K)).map j) ((Over.pullback (bc K)).map f) hj' hV' hpts
  let m : V ⊗ V ⟶ H := (fst V V ≫ j) * (snd V V ≫ j)
  let g : V ⊗ V ⟶ G := (fst V V ≫ f) * (snd V V ≫ f)
  have hPg : (Over.pullback (bc K)).map g = (Over.pullback (bc K)).map m ≫ Fb := by
    simp only [m, g, map_mul', Functor.map_comp, MonObj.mul_comp, Category.assoc, hjF]
  haveI := hj
  haveI := hV
  obtain ⟨_, hs, _, _, _⟩ := id hH
  have : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  have hflat : Flat m.left := flat_mul H V j
  have hqc : QuasiCompact m.left := quasiCompact_mul H V j
  have hsurj : Surjective m.left := surjective_mul H V hH j
  have hcond : ∀ {Z : Scheme.{0}} (a b : Z ⟶ (V ⊗ V).left), a ≫ m.left = b ≫ m.left →
      a ≫ g.left = b ≫ g.left := by
    intro Z a b hab
    have hb : b ≫ (V ⊗ V).hom = a ≫ (V ⊗ V).hom := by
      rw [← Over.w m, ← Category.assoc, ← Category.assoc, hab]
    let a' : Over.mk (a ≫ (V ⊗ V).hom) ⟶ V ⊗ V := Over.homMk a rfl
    let b' : Over.mk (a ≫ (V ⊗ V).hom) ⟶ V ⊗ V := Over.homMk b hb
    have h1 : a' ≫ m = b' ≫ m := Over.OverMorphism.ext hab
    have h2 : a' ≫ g = b' ≫ g := map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hPg, ← Category.assoc, ← Category.assoc,
        ← Functor.map_comp, ← Functor.map_comp, h1])
    exact congrArg CommaMorphism.left h2
  let F₀ : H.left ⟶ G.left := EffectiveEpi.desc m.left g.left hcond
  have hF₀ : m.left ≫ F₀ = g.left := EffectiveEpi.fac m.left g.left hcond
  have hw : F₀ ≫ G.hom = H.hom := by
    apply (cancel_epi m.left).1
    rw [← Category.assoc, hF₀, Over.w g, Over.w m]
  let F : H ⟶ G := Over.homMk F₀ hw
  have hmF : m ≫ F = g := Over.OverMorphism.ext hF₀
  have hmb : Epi ((Over.pullback (bc K)).map m).left := by
    have : Flat ((Over.pullback (bc K)).map m).left :=
      MorphismProperty.of_isPullback (isPullback_map_left (bc K) m).flip hflat
    have : Surjective ((Over.pullback (bc K)).map m).left :=
      MorphismProperty.of_isPullback (isPullback_map_left (bc K) m).flip hsurj
    exact Flat.epi_of_flat_of_surjective _
  have hPF : (Over.pullback (bc K)).map F = Fb := by
    ext1
    apply (cancel_epi ((Over.pullback (bc K)).map m).left).1
    rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp, hmF, hPg]
  have hmul : ∀ (Z : Over (Sp K)) (x y : Z ⟶ H), (x * y) ≫ F = (x ≫ F) * (y ≫ F) := by
    intro Z x y
    apply map_injective
    rw [Functor.map_comp, map_mul', map_mul', Functor.map_comp, Functor.map_comp, hPF, MonObj.mul_comp]
  refine ⟨F, ?_, map_injective (by rw [Functor.map_comp, hPF, hjF])⟩
  have hone : (1 : 𝟙_ (Over (Sp K)) ⟶ H) ≫ F = 1 := by
    have h := hmul (𝟙_ (Over (Sp K))) 1 1
    rw [_root_.mul_one] at h
    exact _root_.mul_eq_left.1 h.symm
  have e1 : ∀ (A : Over (Sp K)) [GrpObj A], (η[A] : 𝟙_ _ ⟶ A) = 1 := fun A _ => by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  refine ⟨?_, ?_⟩
  · rw [e1 H, e1 G, hone]
  · have h := hmul _ (fst H H) (snd H H)
    simpa [Hom.mul_def] using h

end GlobalTheory.GenericHomField
