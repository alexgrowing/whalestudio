import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd

private theorem torusHomOf_iff_appTop₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

private theorem torus_eq₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) {s s' : splitTorus S X ⟶ splitTorus S X'} (hs : TorusHomOf h s) (hs' : TorusHomOf h s') :
    s = s' := by
  apply (GlobalTheory.splitTorusPointsEquiv S X' (splitTorus S X)).injective
  refine MonoidHom.ext fun χ => Units.ext ?_
  rw [show χ = Multiplicative.ofAdd χ.toAdd from rfl, GlobalTheory.splitTorusPointsEquiv_val,
    GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop₂ h s).1 hs, (torusHomOf_iff_appTop₂ h s').1 hs']

private theorem torus_eq_one₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    {s : splitTorus S X ⟶ splitTorus S X'} (hs : TorusHomOf (fun _ => (0 : X)) s) :
    s = toUnit _ ≫ η[splitTorus S X'] := by
  have h0 : (charUnit S X 0).val = 1 := by
    have k := GlobalTheory.splitTorusPointsEquiv_val S X (splitTorus S X) (𝟙 _) 0
    rw [ofAdd_zero, map_one, Units.val_one] at k
    rw [k]
    simp
  have : s = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv S X' (splitTorus S X)).injective
    rw [map_one]
    refine MonoidHom.ext fun χ => Units.ext ?_
    rw [show χ = Multiplicative.ofAdd χ.toAdd from rfl, GlobalTheory.splitTorusPointsEquiv_val,
      (torusHomOf_iff_appTop₂ _ s).1 hs, h0]
    rfl
  rw [this, Hom.one_def]

private theorem pullback_prod_ext₂ {S₀ C : Scheme.{0}} (f : C ⟶ S₀) {X Y : Over S₀} {Z : Over C}
    {a b : Z ⟶ (Over.pullback f).obj (X ⊗ Y)}
    (h₁ : a ≫ (Over.pullback f).map (fst X Y) = b ≫ (Over.pullback f).map (fst X Y))
    (h₂ : a ≫ (Over.pullback f).map (snd X Y) = b ≫ (Over.pullback f).map (snd X Y)) : a = b :=
  (isLimitOfPreserves (Over.pullback f) (tensorProductIsBinaryProduct X Y)).hom_ext (by
    rintro ⟨⟨⟩⟩
    · exact h₁
    · exact h₂)

private theorem map_eta₂ {S₀ C : Scheme.{0}} (f : C ⟶ S₀) (G : Over S₀) [MonObj G] :
    (Over.pullback f).map η[G] = toUnit _ ≫ η[(Over.pullback f).obj G] := by
  rw [Functor.obj.η_def, ← Category.assoc]
  have : toUnit ((Over.pullback f).obj (𝟙_ _)) ≫ Functor.LaxMonoidal.ε (Over.pullback f) = 𝟙 _ :=
    (IsTerminal.isTerminalObj (Over.pullback f) _ isTerminalTensorUnit).hom_ext _ _
  rw [this, Category.id_comp]

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem linHom_lift_one_id : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → LinHom U₂ U i₂ q₂ (lift 1 (𝟙 G₂)) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hS hU i₂ hi₁ hi₂
  have := hS.lim
  let xe : D.toPre.X ≃+ D₁.toPre.X × D₂.toPre.X := AddEquiv.ofBijective (q₁.prod q₂) hS.xsum
  have hxe : ∀ x, xe x = (q₁ x, q₂ x) := fun x => rfl
  let j₁ : D₁.toPre.X → D.toPre.X := fun y => xe.symm (y, 0)
  let j₂ : D₂.toPre.X → D.toPre.X := fun y => xe.symm (0, y)
  have hj₁ : ∀ y, q₁ (j₁ y) = y ∧ q₂ (j₁ y) = 0 := fun y => by
    have k := hxe (j₁ y); simp only [j₁, AddEquiv.apply_symm_apply] at k
    exact ⟨(congrArg Prod.fst k).symm, (congrArg Prod.snd k).symm⟩
  have hj₂ : ∀ y, q₁ (j₂ y) = 0 ∧ q₂ (j₂ y) = y := fun y => by
    have k := hxe (j₂ y); simp only [j₂, AddEquiv.apply_symm_apply] at k
    exact ⟨(congrArg Prod.fst k).symm, (congrArg Prod.snd k).symm⟩
  have hone : IsMonHom (1 : G₂ ⟶ G₁) := by rw [Hom.one_def]; infer_instance
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  ·
    have hq₁ := (U₁.gt e).q_hom
    have hq₂ := (U₂.gt e).q_hom
    have hiso : IsIso ((Over.pullback (thick R I e)).map (lift p₁ p₂)) := inferInstance
    rw [← cancel_mono ((Over.pullback (thick R I e)).map (lift p₁ p₂))]
    apply pullback_prod_ext₂
    · simp only [Category.assoc, ← Functor.map_comp, lift_fst]
      rw [hU.q_pr₁ e, ← Category.assoc, ← Functor.map_comp, lift_fst, hi₁, Hom.one_def]
      simp only [Functor.map_comp, map_eta₂, Category.assoc, IsMonHom.one_hom, comp_toUnit_assoc]
    · simp only [Category.assoc, ← Functor.map_comp, lift_snd]
      rw [hU.q_pr₂ e, ← Category.assoc, ← Functor.map_comp, lift_snd, hi₂]
      simp
  ·
    refine ⟨GlobalTheory.SplitTorusPow.torusMap _ q₂, (torusHomOf_iff_appTop₂ _ _).2 fun χ =>
      GlobalTheory.SplitTorusPow.torusMap_char q₂ χ, ?_⟩
    have hT : TorusHomOf q₂ (GlobalTheory.SplitTorusPow.torusMap (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) q₂) :=
      (torusHomOf_iff_appTop₂ _ _).2 fun χ => GlobalTheory.SplitTorusPow.torusMap_char q₂ χ
    obtain ⟨t₁, ht₁, e₁⟩ := hU.i_pr₁ e j₁ (fun y => (hj₁ y).1) (fun y => (hj₁ y).2)
    obtain ⟨t₂, ht₂, e₂⟩ := hU.i_pr₂ e j₂ (fun y => (hj₂ y).1) (fun y => (hj₂ y).2)
    have c₁ : GlobalTheory.SplitTorusPow.torusMap _ q₂ ≫ t₁ = toUnit _ ≫ η[splitTorus _ D₁.toPre.X] := by
      refine torus_eq_one₂ ?_
      have k := TorusHomOf.comp hT ht₁
      simp only [(hj₁ _).2] at k
      exact k
    have c₂ : GlobalTheory.SplitTorusPow.torusMap _ q₂ ≫ t₂ = 𝟙 _ := by
      refine torus_eq₂ (fun χ => χ) ?_ (TorusHomOf.id _)
      have k := TorusHomOf.comp hT ht₂
      simp only [(hj₂ _).2] at k
      exact k
    have hi₁' := (U₁.gt e).i_hom
    apply pullback_prod_ext₂
    · simp only [Category.assoc]
      rw [e₁, ← Category.assoc _ t₁, c₁, ← Functor.map_comp, lift_fst, Hom.one_def]
      simp only [Functor.map_comp, map_eta₂, Category.assoc, IsMonHom.one_hom, comp_toUnit_assoc]
    · simp only [Category.assoc]
      rw [e₂, ← Category.assoc _ t₂, c₂, ← Functor.map_comp, lift_snd]
      simp

end GlobalTheory.MumProd
