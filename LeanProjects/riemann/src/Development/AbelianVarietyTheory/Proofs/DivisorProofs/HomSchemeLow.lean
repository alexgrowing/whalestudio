import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyModuliOfRankZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapUniqueOfNilpotentNilradicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionShimuraObjectAbelianSchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorObjDualRepresents
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanonHom

theorem pullSec : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (O : Type) [CommRing O] (a' : OAct O G') (a : OAct O G), (∀ r, (a'.act r).left ≫ φ = φ ≫ (a.act r).left) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (T : Over S') (x₀ : X → (Over.mk (T.hom ≫ f) ⟶ G)),
    (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (r : O) y, x₀ (r • y) = x₀ y ≫ a.act r) →
    ∃ x : X → (T ⟶ G'), (∀ y, (x y).left ≫ φ = (x₀ y).left) ∧ (∀ y z, x (y + z) = x y * x z) ∧
      ∀ (r : O) y, x (r • y) = x y ≫ a'.act r := by
  intro S S' G' _ G _ f φ hφ O _ a' a ha X _ _ T x₀ hadd hlin
  have hw : ∀ y, (x₀ y).left ≫ G.hom = T.hom ≫ f := fun y => Over.w (x₀ y)
  let x : X → (T ⟶ G') := fun y => Over.homMk (hφ.1.lift (x₀ y).left T.hom (hw y)) (hφ.1.lift_snd _ _ _)
  have hx : ∀ y, (x y).left ≫ φ = (x₀ y).left := fun y => hφ.1.lift_fst _ _ _
  have uniq : ∀ (p q : T ⟶ G'), p.left ≫ φ = q.left ≫ φ → p = q := fun p q h => by
    ext; apply hφ.1.hom_ext h; rw [Over.w p, Over.w q]
  refine ⟨x, hx, fun y z => uniq _ _ ?_, fun r y => uniq _ _ ?_⟩
  · rw [hx, hadd, hφ.2 T (x y) (x z) (x₀ y) (x₀ z) (hx y).symm (hx z).symm]
  · rw [hx, hlin, Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hx]

theorem pushSec : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (O : Type) [CommRing O] (a' : OAct O G') (a : OAct O G), (∀ r, (a'.act r).left ≫ φ = φ ≫ (a.act r).left) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (T : Over S') (x : X → (T ⟶ G')),
    (∀ y z, x (y + z) = x y * x z) → (∀ (r : O) y, x (r • y) = x y ≫ a'.act r) →
    ∃ x₀ : X → (Over.mk (T.hom ≫ f) ⟶ G), (∀ y, (x₀ y).left = (x y).left ≫ φ) ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧
      ∀ (r : O) y, x₀ (r • y) = x₀ y ≫ a.act r := by
  intro S S' G' _ G _ f φ hφ O _ a' a ha X _ _ T x hadd hlin
  have hw : ∀ y, ((x y).left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := fun y => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (x y)]; rfl
  refine ⟨fun y => Over.homMk ((x y).left ≫ φ) (hw y), fun y => rfl, fun y z => ?_, fun r y => ?_⟩
  · ext
    change (x (y + z)).left ≫ φ = _
    rw [hadd]
    exact (hφ.2 T (x y) (x z) (Over.homMk _ (hw y)) (Over.homMk _ (hw z)) rfl rfl).symm
  · ext
    simp only [Over.homMk_left, Over.comp_left, hlin, Category.assoc, ha]

theorem objMap_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} {o' : Obj D l b' s'} {o : Obj D l b s} {f f' : S' ⟶ S}
    (h : f = f') (m : ObjMap o' o f) : ∃ m' : ObjMap o' o f', m'.toSABMap.φ = m.toSABMap.φ := by
  subst h; exact ⟨m, rfl⟩

theorem obj_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s₁ s₂ : S ⟶ Sp B}
    (h : s₁ = s₂) (o : Obj D l b s₁) : ∃ o₂ : Obj D l b s₂, ∀ {S₀ : Scheme.{0}} {B₀ : Type} [CommRing B₀] {b₀ : Base l B₀}
      {s₀ : S₀ ⟶ Sp B₀} (o₀ : Obj D l b₀ s₀) (f : S ⟶ S₀), Nonempty (ObjMap o o₀ f) → Nonempty (ObjMap o₂ o₀ f) := by
  subst h; exact ⟨o, fun _ _ h => h⟩

theorem homScheme_low : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F) (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F))) (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)), SmoothOfRelativeDimension (D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) g ∧ (∀ y z, u (y + z) = u y * u z) ∧ (∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a) ∧ (∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV) (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v), v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left) ∧ (∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g → ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂) ∧ (∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v) (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v) := by
  intro E _ _ _ H D' l c X _ _ _ _
  have hXo : Nonempty (Moduli D' (LowDat.lowLevel l)) := by
    by_cases hpq : 1 ≤ D'.p + D'.q
    · exact GlobalTheory.Moduli.moduli_scheme_exists E H D' _ hpq
    · exact GlobalTheory.T.nonempty_moduli_of_rank_zero H D' _ (by omega)
  obtain ⟨Xo⟩ := hXo
  set sF : Sp c.F ⟶ Sp (KA (LowDat.lowLevel l)) := lowMap c (RingHom.id c.F) with hsF
  have P := GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := LowDat.lowLevel l)
  obtain ⟨oY, ⟨mY⟩⟩ := P.1 Xo.s Xo.univ (pullback.fst Xo.s sF) (pullback.snd Xo.s sF ≫ sF) pullback.condition.symm
  have hB : IsAbelianScheme oY.t.G := ⟨inferInstance, oY.t.semi.smooth, oY.proper, oY.t.semi.geomConnected⟩
  have hg := GlobalTheory.T.smoothOfRelativeDimension_shimuraObject_abelianScheme D' (LowDat.lowLevel l) (pullback.snd Xo.s sF ≫ sF) oY
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Projective (𝓞 E) X := GlobalTheory.Forms.projective_of_int _ _
  obtain ⟨C, _, u, -, hCsm, -, hadd, hlin, huniv⟩ :=
    GlobalTheory.HomScheme.exists_homObj_relDim _ oY.t.G hB _ hg oY.t.act X
  obtain ⟨oC, ⟨mC⟩⟩ := P.1 (pullback.snd Xo.s sF ≫ sF) oY C.hom ((C.hom ≫ pullback.snd Xo.s sF) ≫ sF)
    (Category.assoc _ _ _)
  obtain ⟨u', hu'φ, hu'add, hu'lin⟩ := pullSec oC.t.G oY.t.G C.hom mC.toSABMap.φ mC.cart (𝓞 E) oC.t.act oY.t.act mC.act X
    (𝟙_ (Over C.left)) (fun y => Over.homMk (𝟙 C.left) (by simp) ≫ u y) (fun y z => by rw [hadd, comp_mul])
    (fun r y => by rw [hlin, Category.assoc])
  have key : ∀ {T : Scheme.{0}} (v₁ v₂ : T ⟶ C.left), v₁ ≫ C.hom = v₂ ≫ C.hom →
      (∀ y, v₁ ≫ (u y).left = v₂ ≫ (u y).left) → v₁ = v₂ := by
    intro T v₁ v₂ hw hu
    obtain ⟨c0, -, huq⟩ := huniv (Over.mk (v₁ ≫ C.hom)) (fun y => Over.homMk v₁ rfl ≫ u y)
      (fun y z => by rw [hadd, comp_mul]) (fun r y => by rw [hlin, Category.assoc])
    have e1 := huq (Over.homMk v₁ rfl) (fun y => rfl)
    have e2 := huq (Over.homMk v₂ hw.symm) (fun y => by ext; simpa using (hu y).symm)
    simpa using congrArg CommaMorphism.left (e1.trans e2.symm)
  have hu'l : ∀ y, (u' y).left ≫ mC.toSABMap.φ = (u y).left := fun y => by rw [hu'φ]; simp
  have key2 : ∀ (A : Type) [CommRing A], IsNilpotent (nilradical A) → ∀ (v₁ v₂ : Sp A ⟶ C.left)
      (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s')
      (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), v₁ ≫ C.hom = v₂ ≫ C.hom →
      (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u' y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u' y).left) → v₁ = v₂ := by
    intro A _ hA v₁ v₂ s' o'' m₁ m₂ z hw hz₁ hz₂
    obtain ⟨k₁, hk₁⟩ := (P.2 _ _ s' oY oC o'' C.hom v₁ mC).1 m₁
    obtain ⟨k₂, hk₂⟩ := (P.2 _ _ s' oY oC o'' C.hom v₂ mC).1 m₂
    obtain ⟨k₂', hk₂'⟩ := objMap_congr hw.symm k₂
    have hφ := GlobalTheory.T.objMap_unique_of_nilpotent_nilradical' A hA s' _ o'' oY (v₁ ≫ C.hom) k₁ k₂'
    refine key v₁ v₂ hw fun y => ?_
    calc v₁ ≫ (u y).left = z y ≫ k₁.toSABMap.φ := by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hu'l]
      _ = z y ≫ k₂'.toSABMap.φ := by rw [hφ]
      _ = v₂ ≫ (u y).left := by rw [hk₂', hk₂, ← Category.assoc, hz₂, Category.assoc, hu'l]
  refine ⟨C.left, C.hom ≫ pullback.snd Xo.s sF, oC, u', ?_, hu'add, hu'lin, ?_, ?_, ?_⟩
  · haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := D'.dim)
    haveI h1 : SmoothOfRelativeDimension D'.dim (pullback.snd Xo.s sF) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @SmoothOfRelativeDimension D'.dim)
        (IsPullback.of_hasPullback Xo.s sF) Xo.smooth
    haveI := hCsm
    rw [add_comm]
    infer_instance
  · intro V _ _ bV o' x hxadd hxlin
    obtain ⟨f, ⟨hf, ⟨k⟩⟩, -⟩ := Xo.rep (Sp V) (lowMap c bV) inferInstance o'
    have hlow : lowMap c bV = spMap bV ≫ sF := by simp only [hsF, lowMap, spMap, ← Spec.map_comp]; rfl
    let fY : Sp V ⟶ pullback Xo.s sF := pullback.lift f (spMap bV) (hf.trans hlow)
    obtain ⟨k', -⟩ := objMap_congr (pullback.lift_fst f (spMap bV) (hf.trans hlow)).symm k
    obtain ⟨n, -⟩ := (P.2 Xo.s (pullback.snd Xo.s sF ≫ sF) (lowMap c bV) Xo.univ oY o' (pullback.fst _ _) fY mY).2 k'
    obtain ⟨x₀, hx₀, hx₀add, hx₀lin⟩ := pushSec o'.t.G oY.t.G fY n.toSABMap.φ n.cart (𝓞 E) o'.t.act oY.t.act n.act X
      (𝟙_ (Over (Sp V))) x hxadd hxlin
    obtain ⟨cc, hcc, -⟩ := huniv (Over.mk ((𝟙_ (Over (Sp V))).hom ≫ fY)) x₀ hx₀add hx₀lin
    have hccw : cc.left ≫ C.hom = fY := by simpa using Over.w cc
    obtain ⟨n', hn'⟩ := objMap_congr hccw.symm n
    obtain ⟨m, hm⟩ := (P.2 _ _ (lowMap c bV) oY oC o' C.hom cc.left mC).2 n'
    refine ⟨cc.left, m, ?_, fun y => ?_⟩
    · rw [← Category.assoc, hccw, pullback.lift_snd]
    · apply mC.cart.1.hom_ext
      · rw [Category.assoc, ← hm, hn', Category.assoc, hu'l, ← hx₀, ← hcc y]
        rfl
      · rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w (x y), Category.assoc, Over.w (u' y)]
        simp
  · intro A _ _ v₁ v₂ hv s' o'' m₁ m₂ z hs' hz₁ hz₂
    refine key2 A (by rw [nilradical_eq_zero]; exact IsNilpotent.zero) v₁ v₂ s' o'' m₁ m₂ z ?_ hz₁ hz₂
    obtain ⟨k₁, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v₁ mC).1 m₁
    obtain ⟨K₁, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v₁ ≫ C.hom) mY).1 k₁
    obtain ⟨k₂, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v₂ mC).1 m₂
    obtain ⟨K₂, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v₂ ≫ C.hom) mY).1 k₂
    have hv' := hv =≫ sF
    simp only [Category.assoc] at hv'
    have hs₁ : ((v₁ ≫ C.hom) ≫ pullback.fst Xo.s sF) ≫ Xo.s = s' := by
      rw [hs']; simp only [Category.assoc, pullback.condition]
    have hs₂ : ((v₂ ≫ C.hom) ≫ pullback.fst Xo.s sF) ≫ Xo.s = s' := by
      rw [hs']; simp only [Category.assoc, pullback.condition]; exact hv'.symm
    have hfst := (Xo.rep (Sp A) s' inferInstance o'').unique ⟨hs₁, ⟨K₁⟩⟩ ⟨hs₂, ⟨K₂⟩⟩
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simpa only [Category.assoc] using hv
  · intro k _ v s' o'' m₁ m₂ z hs' hz₁ hz₂
    refine key2 (DualNumber k) (IsNoetherianRing.isNilpotent_nilradical _) v (constPt v) s' o'' m₁ m₂ z ?_ hz₁ hz₂
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : Algebra.IsAlgebraic ℚ c.F := Algebra.IsAlgebraic.of_finite ℚ c.F
    have hcp : ∀ {W : Scheme.{0}} (w : C.left ⟶ W), constPt v ≫ w = constPt (v ≫ w) := fun w => by simp [constPt]
    obtain ⟨k₁, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v mC).1 m₁
    obtain ⟨K₁, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v ≫ C.hom) mY).1 k₁
    obtain ⟨k₂, -⟩ := (P.2 _ _ s' oY oC o'' C.hom (constPt v) mC).1 m₂
    obtain ⟨K₂, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (constPt v ≫ C.hom) mY).1 k₂
    obtain ⟨K₁', -⟩ := objMap_congr (Category.assoc v C.hom (pullback.fst Xo.s sF)) K₁
    obtain ⟨K₂', -⟩ := objMap_congr (show (constPt v ≫ C.hom) ≫ pullback.fst Xo.s sF =
      constPt (v ≫ C.hom ≫ pullback.fst Xo.s sF) by simp [constPt]) K₂
    have hs₁ : s' = (v ≫ C.hom ≫ pullback.fst Xo.s sF) ≫ Xo.s := by
      rw [hs']; simp only [Category.assoc, pullback.condition]
    obtain ⟨o₂, ho₂⟩ := obj_congr hs₁ o''
    have hfst := Xo.unram k _ o₂ (ho₂ Xo.univ _ ⟨K₁'⟩) (ho₂ Xo.univ _ ⟨K₂'⟩)
    apply pullback.hom_ext
    · simp only [Category.assoc]; rw [hcp]; exact hfst
    · simp only [Category.assoc]; rw [hcp]; exact GlobalTheory.Models.RankZero.eq_constPt_field _

end GlobalTheory.UCanonHom
