import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecMap

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExtUnique

theorem dense_open {S : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S] (U : S.Opens)
    (hU : Dense (U : Set S)) : QuasiCompact U.ι ∧ IsSchemeTheoreticallyDominant U.ι := by
  have := Opens.isDominant_ι (X := S) hU
  exact ⟨inferInstance, .of_isDominant _⟩

theorem dense_openImmersion {U S : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S] (j : U ⟶ S)
    [IsOpenImmersion j] [IsDominant j] : QuasiCompact j ∧ IsSchemeTheoreticallyDominant j :=
  ⟨inferInstance, .of_isDominant _⟩

theorem isSchemeTheoreticallyDominant_spec_of_injective {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by
  first
  | exact @_root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap
  | exact _root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap
  | (apply _root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap <;> assumption)
  | (intros; apply _root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap ..)

theorem spec_fractionRing (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K] :
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  ⟨inferInstance, isSchemeTheoreticallyDominant_spec_of_injective _ (IsFractionRing.injective R K)⟩

theorem hom_ext_of_dominant {W X Y Z : Scheme.{u}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) (w : W ⟶ X) [IsSchemeTheoreticallyDominant w] (hw : w ≫ f = w ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let W' : Over Z := Over.mk (w ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let w' : W' ⟶ X' := Over.homMk w
  have : IsSeparated Y'.hom := ‹_›
  have hw' : w' ≫ f' = w' ≫ g' := Over.OverMorphism.ext hw
  have e : (equalizer.lift w' hw').left ≫ (equalizer.ι f' g').left = w := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hk : (equalizer.ι f' g').left.ker = ⊥ := by
    have h₁ := Scheme.Hom.le_ker_comp (equalizer.lift w' hw').left (equalizer.ι f' g').left
    rw [e, w.ker_eq_bot] at h₁
    exact le_bot_iff.1 h₁
  have : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hk
  have c : (equalizer.ι f' g').left ≫ f'.left = (equalizer.ι f' g').left ≫ g'.left := by
    rw [← Over.comp_left, ← Over.comp_left, equalizer.condition]
  exact (cancel_epi _).1 c

variable {U S : Scheme.{u}} (j : U ⟶ S) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]

variable {j} in

theorem over_hom_ext_of_isPullback {X Y : Over S} [Flat X.hom] [IsSeparated Y.hom] {X' : Scheme.{u}}
    {φ : X' ⟶ X.left} {p : X' ⟶ U} (h : IsPullback φ p X.hom j) {f g : X ⟶ Y}
    (hfg : φ ≫ f.left = φ ≫ g.left) : f = g := by
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback h.flip
  exact Over.OverMorphism.ext (hom_ext_of_dominant Y.hom (by rw [Over.w, Over.w]) φ hfg)

omit [QuasiCompact j] [IsSchemeTheoreticallyDominant j] in
theorem pullback_map_left_fst {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback j).map a).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ a.left :=
  pullback.lift_fst _ _ _

theorem pullback_map_injective (X Y : Over S) [Flat X.hom] [IsSeparated Y.hom] :
    Function.Injective ((Over.pullback j).map : (X ⟶ Y) → _) := fun f g h =>
  over_hom_ext_of_isPullback (IsPullback.of_hasPullback X.hom j)
    (by rw [← pullback_map_left_fst, ← pullback_map_left_fst, h])

theorem comp_eq_id_of_pullback {X Y : Over S} [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom]
    (e : (Over.pullback j).obj X ≅ (Over.pullback j).obj Y) (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : (Over.pullback j).map f = e.hom) (hg : (Over.pullback j).map g = e.inv) :
    f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y :=
  ⟨pullback_map_injective j X X (by simp [hf, hg]), pullback_map_injective j Y Y (by simp [hf, hg])⟩

theorem isIso_of_pullback {X Y : Over S} [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom]
    (e : (Over.pullback j).obj X ≅ (Over.pullback j).obj Y) (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : (Over.pullback j).map f = e.hom) (hg : (Over.pullback j).map g = e.inv) : IsIso f :=
  ⟨g, comp_eq_id_of_pullback j e f g hf hg⟩

variable {j} in

theorem comp_eq_id_of_isPullback {X Y : Over S} [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom]
    {X' Y' : Over U} {φ : X'.left ⟶ X.left} {ψ : Y'.left ⟶ Y.left}
    (hX : IsPullback φ X'.hom X.hom j) (hY : IsPullback ψ Y'.hom Y.hom j) (e : X' ≅ Y') (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : e.hom.left ≫ ψ = φ ≫ f.left) (hg : e.inv.left ≫ φ = ψ ≫ g.left) :
    f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y := by
  constructor
  · refine over_hom_ext_of_isPullback hX ?_
    rw [Over.comp_left, ← Category.assoc, ← hf, Category.assoc, ← hg, ← Category.assoc, ← Over.comp_left,
      e.hom_inv_id, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine over_hom_ext_of_isPullback hY ?_
    rw [Over.comp_left, ← Category.assoc, ← hg, Category.assoc, ← hf, ← Category.assoc, ← Over.comp_left,
      e.inv_hom_id, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]

variable {j} in

theorem isIso_of_isPullback {X Y : Over S} [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom]
    {X' Y' : Over U} {φ : X'.left ⟶ X.left} {ψ : Y'.left ⟶ Y.left}
    (hX : IsPullback φ X'.hom X.hom j) (hY : IsPullback ψ Y'.hom Y.hom j) (e : X' ≅ Y') (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : e.hom.left ≫ ψ = φ ≫ f.left) (hg : e.inv.left ≫ φ = ψ ≫ g.left) : IsIso f :=
  ⟨g, comp_eq_id_of_isPullback hX hY e f g hf hg⟩

theorem flat_tensorObj (X Y : Over S) [Flat X.hom] [Flat Y.hom] : Flat (X ⊗ Y).hom := by
  change Flat (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance

theorem flat_tensorUnit : Flat (𝟙_ (Over S)).hom := by
  change Flat (𝟙 S)
  infer_instance

theorem isMonHom_of_pullback {G H : Over S} [MonObj G] [MonObj H] [Flat G.hom] [IsSeparated H.hom] (f : G ⟶ H)
    (hf : IsMonHom ((Over.pullback j).map f)) : IsMonHom f := by
  have := flat_tensorObj G G
  have := flat_tensorUnit (S := S)
  constructor
  · apply pullback_map_injective j
    have h := hf.one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at h
    rw [Functor.map_comp, h]
  · apply pullback_map_injective j
    have h := hf.mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.LaxMonoidal.μ_natural_assoc, Category.assoc,
      cancel_epi] at h
    rw [Functor.map_comp, Functor.map_comp, h]

theorem mapGrp_map_injective (G H : Grp (Over S)) [Flat G.X.hom] [IsSeparated H.X.hom] :
    Function.Injective ((Over.pullback j).mapGrp.map : (G ⟶ H) → _) := fun f g h => by
  ext1
  exact pullback_map_injective j G.X H.X (congrArg (fun z => z.hom.hom) h)

end GlobalTheory.ExtUnique

namespace GlobalTheory.ExtUnique

variable {U S : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]

theorem isMonHom_of_isGrpPullback {G H : Over S} [GrpObj G] [GrpObj H] [Flat G.hom] [IsSeparated H.hom]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : IsGrpPullback G' G j φ) (hH : IsGrpPullback H' H j ψ) (f' : G' ⟶ H') [IsMonHom f'] (f : G ⟶ H)
    (hf : f'.left ≫ ψ = φ ≫ f.left) : IsMonHom f := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j) hG
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hH (isGrpPullback_pullback H j)
  have e : (Over.pullback j).map f = a.hom ≫ f' ≫ b.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [pullback_map_left_fst, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', hf,
        ← Category.assoc, ha']
    · exact (Over.w _).trans (Over.w _).symm
  exact isMonHom_of_pullback j f (by rw [e]; infer_instance)

theorem oAct_ext {O : Type} [CommRing O] {G : Over S} [GrpObj G] {a b : OAct O G} (h : ∀ x, a.act x = b.act x) :
    a = b := by
  obtain ⟨a, _, _, _, _⟩ := a
  obtain ⟨b, _, _, _, _⟩ := b
  obtain rfl : a = b := funext h
  rfl

theorem existsUnique_oAct_of_isGrpPullback {O : Type} [CommRing O] {G : Over S} [GrpObj G] [Flat G.hom]
    [IsSeparated G.hom] {G' : Over U} [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G j φ)
    (i : OAct O G') (hi : ∀ x, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) :
    ∃! a : OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  choose f hf using hi
  refine ⟨⟨f, fun x => ?_, ?_, fun x y => ?_, fun x y => ?_⟩, hf, fun b hb => oAct_ext fun x => ?_⟩
  · have := i.hom x
    exact isMonHom_of_isGrpPullback hG hG (i.act x) (f x) (hf x)
  · refine over_hom_ext_of_isPullback hG.1 ?_
    rw [← hf, i.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine over_hom_ext_of_isPullback hG.1 ?_
    rw [← hf, i.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine over_hom_ext_of_isPullback hG.1 ?_
    let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hG.1.w
    have h := hG.2 G' (i.act x) (i.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, i.add, ← h]
    rfl
  · exact over_hom_ext_of_isPullback hG.1 ((hb x).symm.trans (hf x))

variable (j) in

theorem existsUnique_oAct_pullback {O : Type} [CommRing O] {G : Over S} [GrpObj G] [IsCommMonObj G] [Flat G.hom]
    [IsSeparated G.hom] (i : OAct O ((Over.pullback j).obj G))
    (hi : ∀ x, ∃ f : G ⟶ G, (Over.pullback j).map f = i.act x) :
    ∃! a : OAct O G, OAct.pullback j G a = i := by
  obtain ⟨a, ha, hu⟩ := existsUnique_oAct_of_isGrpPullback (isGrpPullback_pullback G j) i fun x => by
    obtain ⟨f, hf⟩ := hi x
    exact ⟨f, by rw [← hf, pullback_map_left_fst]⟩
  refine ⟨a, oAct_ext fun x => ?_, fun b hb => hu b fun x => ?_⟩
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (pullback_map_left_fst j _).trans (ha x).symm
    · exact (Over.w _).trans (Over.w _).symm
  · rw [← hb]
    exact pullback_map_left_fst j _

theorem flat_and_isSeparated_of_isSemiAbelian {S : Scheme.{u}} (G : Over S) [GrpObj G] (h : IsSemiAbelian G) :
    Flat G.hom ∧ IsSeparated G.hom := by
  have := h.smooth
  exact ⟨inferInstance, h.separated⟩

def intAct {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : OAct ℤ G where
  act n := 𝟙 G ^ n
  hom n := by
    induction n using Int.induction_on with
    | zero => rw [zpow_zero, Hom.one_def]; infer_instance
    | succ n ih => rw [zpow_add_one, Hom.mul_def]; infer_instance
    | pred n ih => rw [zpow_sub_one, Hom.mul_def]; infer_instance
  one := zpow_one _
  mul a b := by rw [GrpObj.comp_zpow, Category.comp_id, zpow_mul]
  add a b := zpow_add _ _ _

theorem intAct_pullback {U S : Scheme.{0}} (j : U ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℤ) :
    (Over.pullback j).map ((intAct G).act n) = (intAct ((Over.pullback j).obj G)).act n := by
  have h := map_zpow (MonoidHom.mk' (fun f : G ⟶ G => (Over.pullback j).map f)
    fun _ _ => CategoryTheory.Functor.map_mul _ _ _) (𝟙 G) n
  simpa [intAct] using h

theorem splitTorusAff_flat_and_isSeparated (R : CommRingCat.{u}) (X : Type u) [AddCommGroup X] :
    Flat (splitTorusAff R X).hom ∧ IsSeparated (splitTorusAff R X).hom := by
  constructor
  · change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))))
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  · change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))))
    infer_instance

theorem intAct_splitTorusAff_zero_ne_one (R : CommRingCat.{0}) [Nontrivial R] (X : Type) [AddCommGroup X]
    [Nontrivial X] : (intAct (splitTorusAff R X)).act 0 ≠ (intAct (splitTorusAff R X)).act 1 := by
  intro h
  rw [(intAct _).one] at h
  change (𝟙 _ : splitTorusAff R X ⟶ _) ^ (0 : ℤ) = _ at h
  rw [zpow_zero, Hom.one_def] at h
  have h₁ : Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ (η[splitTorusAff R X]).left =
      𝟙 (Spec (torusRing R X)) := congrArg (fun z => z.left) h
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := torusRing R X) (S := R) (η[splitTorusAff R X]).left
  rw [← hψ] at h₁
  have h₂ : ψ ≫ CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X)) = 𝟙 (torusRing R X) :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_id]; exact h₁)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have h₃ : algebraMap R (AddMonoidAlgebra R X) (ψ (AddMonoidAlgebra.single x 1)) = AddMonoidAlgebra.single x 1 :=
    congrArg (fun z => z.hom (AddMonoidAlgebra.single x 1)) h₂
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply] at h₃
  have h₄ := congrArg (fun z : AddMonoidAlgebra R X => z.coeff x) h₃
  simp [hx] at h₄

theorem intAct_unique_extension (a : OAct ℤ (splitTorusAff (CommRingCat.of ℤ) ℤ))
    (ha : OAct.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) _ a = intAct _) : a = intAct _ := by
  obtain ⟨_, _⟩ := spec_fractionRing ℤ ℚ
  obtain ⟨_, _⟩ := splitTorusAff_flat_and_isSeparated (CommRingCat.of ℤ) ℤ
  exact (existsUnique_oAct_pullback _ _ fun n => ⟨_, intAct_pullback _ _ n⟩).unique ha
    (oAct_ext fun n => intAct_pullback _ _ n)

end GlobalTheory.ExtUnique

namespace GlobalTheory

open ExtUnique

theorem extension_unique :
    (∀ (S : Scheme.{0}) [IsReduced S] [IsLocallyNoetherian S] (U : S.Opens), Dense (U : Set S) →
      QuasiCompact U.ι ∧ IsSchemeTheoreticallyDominant U.ι) ∧
    (∀ (R K : Type) [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K],
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
    ∀ (U S : Scheme.{0}) (j : U ⟶ S) [QuasiCompact j] [IsSchemeTheoreticallyDominant j],
      ((∀ (X Y : Over S) [Flat X.hom] [IsSeparated Y.hom] (f g : X ⟶ Y),
          (Over.pullback j).map f = (Over.pullback j).map g → f = g) ∧
        ∀ (X Y : Over S) [Flat X.hom] [IsSeparated Y.hom] (X' : Scheme.{0}) (φ : X' ⟶ X.left) (p : X' ⟶ U),
          IsPullback φ p X.hom j → ∀ f g : X ⟶ Y, φ ≫ f.left = φ ≫ g.left → f = g) ∧
      ((∀ (G H : Over S) [GrpObj G] [GrpObj H] [Flat G.hom] [IsSeparated H.hom] (f : G ⟶ H),
          IsMonHom ((Over.pullback j).map f) → IsMonHom f) ∧
        ∀ (G H : Over S) [GrpObj G] [GrpObj H] [Flat G.hom] [IsSeparated H.hom] (G' H' : Over U) [GrpObj G']
          [GrpObj H'] (φ : G'.left ⟶ G.left) (ψ : H'.left ⟶ H.left),
          IsGrpPullback G' G j φ → IsGrpPullback H' H j ψ → ∀ (f' : G' ⟶ H') (f : G ⟶ H), IsMonHom f' →
          f'.left ≫ ψ = φ ≫ f.left → IsMonHom f) ∧
      (∀ (G H : Grp (Over S)) [Flat G.X.hom] [IsSeparated H.X.hom],
          Function.Injective ((Over.pullback j).mapGrp.map : (G ⟶ H) → _)) ∧
      ((∀ (O : Type) [CommRing O] (G : Over S) [GrpObj G] [IsCommMonObj G] [Flat G.hom] [IsSeparated G.hom]
          (i : OAct O ((Over.pullback j).obj G)), (∀ x, ∃ f : G ⟶ G, (Over.pullback j).map f = i.act x) →
          ∃! a : OAct O G, OAct.pullback j G a = i) ∧
        ∀ (O : Type) [CommRing O] (G : Over S) [GrpObj G] [Flat G.hom] [IsSeparated G.hom] (G' : Over U)
          [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G j φ → ∀ i : OAct O G',
          (∀ x, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) →
          ∃! a : OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left) ∧
      ((∀ (X Y : Over S) [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom]
          (e : (Over.pullback j).obj X ≅ (Over.pullback j).obj Y) (f : X ⟶ Y) (g : Y ⟶ X),
          (Over.pullback j).map f = e.hom → (Over.pullback j).map g = e.inv →
          IsIso f ∧ f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y) ∧
        ∀ (X Y : Over S) [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom] (X' Y' : Over U)
          (φ : X'.left ⟶ X.left) (ψ : Y'.left ⟶ Y.left), IsPullback φ X'.hom X.hom j →
          IsPullback ψ Y'.hom Y.hom j → ∀ (e : X' ≅ Y') (f : X ⟶ Y) (g : Y ⟶ X),
          e.hom.left ≫ ψ = φ ≫ f.left → e.inv.left ≫ φ = ψ ≫ g.left →
          IsIso f ∧ f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y) :=
  ⟨fun _ _ _ U hU => dense_open U hU, fun R K _ _ _ _ => spec_fractionRing R K, fun _ _ j _ _ =>
    ⟨⟨fun X Y _ _ _ _ h => pullback_map_injective j X Y h,
      fun _ _ _ _ _ _ _ h _ _ e => over_hom_ext_of_isPullback h e⟩,
    ⟨fun _ _ _ _ _ _ f h => isMonHom_of_pullback j f h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ hG hH f' f _ e => isMonHom_of_isGrpPullback hG hH f' f e⟩,
    fun G H _ _ => mapGrp_map_injective j G H,
    ⟨fun _ _ _ _ _ _ _ i hi => existsUnique_oAct_pullback j i hi,
      fun _ _ _ _ _ _ _ _ _ hG i hi => existsUnique_oAct_of_isGrpPullback hG i hi⟩,
    ⟨fun _ _ _ _ _ _ e f g hf hg => ⟨isIso_of_pullback j e f g hf hg, comp_eq_id_of_pullback j e f g hf hg⟩,
      fun _ _ _ _ _ _ _ _ _ _ hX hY e f g hf hg =>
        ⟨isIso_of_isPullback hX hY e f g hf hg, comp_eq_id_of_isPullback hX hY e f g hf hg⟩⟩⟩⟩

end GlobalTheory
