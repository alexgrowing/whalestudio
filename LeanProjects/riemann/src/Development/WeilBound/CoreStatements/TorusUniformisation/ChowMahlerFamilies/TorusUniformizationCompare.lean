import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.TorusUniformizationCompare

section Alg

variable {k : Type} [Field k] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

theorem half [Module.Free ℤ X] [Module.Finite ℤ X]
    (P : ∀ (A : Type) [CommRing A], (k →+* A) → (Multiplicative X →* A) → (Multiplicative Y →* A) → Prop)
    (hex : ∀ (A : Type) [CommRing A] (g : k →+* A) θ, ∃ θ', P A g θ θ')
    (hun : ∀ (A : Type) [CommRing A] (g : k →+* A) θ θ' θ'', P A g θ θ' → P A g θ θ'' → θ' = θ'')
    (hnat : ∀ (A B : Type) [CommRing A] [CommRing B] (g : k →+* A) (h : A →+* B) θ θ', P A g θ θ' →
      P B (h.comp g) ((h : A →* B).comp θ) ((h : A →* B).comp θ'))
    (h1 : P k (RingHom.id k) 1 1) :
    ∃ φ : Y →+ X, ∀ (A : Type) [CommRing A] (g : k →+* A) θ,
      P A g θ (θ.comp (AddMonoidHom.toMultiplicative φ)) := by
  classical
  obtain ⟨ρ, hρ⟩ := hex (AddMonoidAlgebra k X) (algebraMap k _) (AddMonoidAlgebra.of k X)
  have key : ∀ (A : Type) [CommRing A] [Algebra k A] (θ : Multiplicative X →* A),
      P A (algebraMap k A) θ ((((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) :
        AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp ρ) := by
    intro A _ _ θ
    have h := hnat _ A _ ((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) :
        AddMonoidAlgebra k X →+* A) _ _ hρ
    have e1 : (((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) :
        AddMonoidAlgebra k X →+* A)).comp (algebraMap k _) = algebraMap k A := AlgHom.comp_algebraMap _
    have e2 : (((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) :
        AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp (AddMonoidAlgebra.of k X) = θ := by
      refine MonoidHom.ext fun y => ?_
      simp
    rwa [e1, e2] at h
  have h2 := hun k _ _ _ _ h1 (key k 1)
  have h3 : ∀ y : Y, ∃ a : X, (ρ (Multiplicative.ofAdd y) : AddMonoidAlgebra k X) = AddMonoidAlgebra.single a 1 := by
    intro y
    obtain ⟨a, c, -, e⟩ := Rosenlicht.isUnit_eq_single ((Group.isUnit (Multiplicative.ofAdd y)).map ρ)
    have h4 := congrArg (fun f : Multiplicative Y →* k => f (Multiplicative.ofAdd y)) h2
    simp [e] at h4
    exact ⟨a, by rw [e, ← h4]⟩
  choose φ hφ using h3
  have hadd : ∀ a b, φ (a + b) = φ a + φ b := by
    intro a b
    have h5 := hφ (a + b)
    rw [ofAdd_add, map_mul, hφ, hφ, AddMonoidAlgebra.single_mul_single, _root_.mul_one] at h5
    by_contra hne
    have := congrArg (fun f => AddMonoidAlgebra.coeff f (φ (a + b))) h5
    simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne] at this
  refine ⟨AddMonoidHom.mk' φ hadd, fun A _ g θ => ?_⟩
  letI : Algebra k A := g.toAlgebra
  have h := key A θ
  have e : (((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) :
        AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp ρ =
      θ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.mk' φ hadd)) := by
    refine MonoidHom.ext fun y => ?_
    have := hφ y.toAdd
    rw [ofAdd_toAdd] at this
    simp [this]
  rw [e] at h
  exact h

theorem of_inj {a b : X} (h : AddMonoidAlgebra.of k X (Multiplicative.ofAdd a) =
    AddMonoidAlgebra.of k X (Multiplicative.ofAdd b)) : a = b := by
  classical
  by_contra hne
  have := congrArg (fun f => AddMonoidAlgebra.coeff f a) h
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne] at this

theorem full [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : ∀ (A : Type) [CommRing A], (k →+* A) → (Multiplicative X →* A) → (Multiplicative Y →* A) → Prop)
    (hex : ∀ (A : Type) [CommRing A] (g : k →+* A) θ, ∃ θ', P A g θ θ')
    (hun : ∀ (A : Type) [CommRing A] (g : k →+* A) θ θ' θ'', P A g θ θ' → P A g θ θ'' → θ' = θ'')
    (hex' : ∀ (A : Type) [CommRing A] (g : k →+* A) θ', ∃ θ, P A g θ θ')
    (hun' : ∀ (A : Type) [CommRing A] (g : k →+* A) θ θ' θ'', P A g θ' θ → P A g θ'' θ → θ' = θ'')
    (hnat : ∀ (A B : Type) [CommRing A] [CommRing B] (g : k →+* A) (h : A →+* B) θ θ', P A g θ θ' →
      P B (h.comp g) ((h : A →* B).comp θ) ((h : A →* B).comp θ'))
    (h1 : P k (RingHom.id k) 1 1) :
    ∃ e : Y ≃+ X, ∀ (A : Type) [CommRing A] (g : k →+* A) θ,
      P A g θ (θ.comp (AddMonoidHom.toMultiplicative e.toAddMonoidHom)) := by
  obtain ⟨φ, hφ⟩ := half P hex hun hnat h1
  obtain ⟨φ', hφ'⟩ := half (fun A _ g θ' θ => P A g θ θ') hex' hun'
    (fun A B _ _ g h θ θ' H => hnat A B g h θ' θ H) h1
  have a1 : ∀ a, φ (φ' a) = a := by
    intro a
    have h := hun' _ (algebraMap k _) _ _ _ (hφ' _ _ _) (hφ _ _ (AddMonoidAlgebra.of k X))
    exact of_inj (k := k) (congrArg (fun f : Multiplicative X →* AddMonoidAlgebra k X =>
      f (Multiplicative.ofAdd a)) h)
  have a2 : ∀ a, φ' (φ a) = a := by
    intro a
    have h := hun _ (algebraMap k _) _ _ _ (hφ _ _ _) (hφ' _ _ (AddMonoidAlgebra.of k Y))
    exact of_inj (k := k) (congrArg (fun f : Multiplicative Y →* AddMonoidAlgebra k Y =>
      f (Multiplicative.ofAdd a)) h)
  exact ⟨{ toFun := φ, invFun := φ', left_inv := a2, right_inv := a1, map_add' := φ.map_add }, hφ⟩

end Alg

section Pts

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A]

noncomputable def cv {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) : Multiplicative X →* A where
  toFun χ := charVal t χ.toAdd
  map_one' := ((GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.1 t).1
  map_mul' χ χ' := ((GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.1 t).2 _ _

theorem cv_inj {a : Sp A ⟶ S} {t t' : Over.mk a ⟶ splitTorus S X} (h : cv t = cv t') : t = t' :=
  (GlobalTheory.T.charVal_multiplicative S X A a).1 t t' fun χ =>
    congrArg (fun f : Multiplicative X →* A => f (Multiplicative.ofAdd χ)) h

theorem cv_surj (a : Sp A ⟶ S) (θ : Multiplicative X →* A) : ∃ t : Over.mk a ⟶ splitTorus S X, cv t = θ := by
  obtain ⟨t, ht⟩ := (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.1 θ
  exact ⟨t, MonoidHom.ext fun χ => ht χ.toAdd⟩

theorem cv_one (a : Sp A ⟶ S) : cv (1 : Over.mk a ⟶ splitTorus S X) = 1 :=
  MonoidHom.ext fun χ => (GlobalTheory.T.charVal_multiplicative S X A a).2.2.1 χ.toAdd

theorem cv_nat {a : Sp A ⟶ S} {B : Type} [CommRing B] (h : A →+* B) {b : Sp B ⟶ S} (hb : spMap h ≫ a = b)
    (t : Over.mk a ⟶ splitTorus S X) :
    ∃ t' : Over.mk b ⟶ splitTorus S X, t'.left = spMap h ≫ t.left ∧ cv t' = (h : A →* B).comp (cv t) := by
  subst hb
  let t' : Over.mk (spMap h ≫ a) ⟶ splitTorus S X :=
    Over.homMk (spMap h ≫ t.left) (by rw [Category.assoc, Over.w t]; rfl)
  exact ⟨t', rfl, MonoidHom.ext fun χ => (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.2 B h t t' rfl χ.toAdd⟩

end Pts

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (h : B →+* C) :
    spMap (h.comp g) = spMap h ≫ spMap g := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_pullback_ext {k Ω : Type} [Field k] [Field Ω] (f : Sp Ω ⟶ Sp k)
    (G : Over (Sp k)) [GrpObj G] (T : TorusExtension G) :
    ∃ T' : TorusExtension ((Over.pullback f).obj G), ∀ (W : Over (Sp Ω)) (p : W ⟶ (Over.pullback f).obj G)
      (p₀ : Over.mk (W.hom ≫ f) ⟶ G), p₀.left = p.left ≫ pullback.fst G.hom f →
      ((letI := T'.grpB; p ≫ T'.q = 1) ↔ (letI := T.grpB; p₀ ≫ T.q = 1)) := by
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X
  have hq := GlobalTheory.SS.isPullback_overPullback_map_left f T.q
  refine ⟨{ X := T.X
            addCommGroup := T.addCommGroup
            free := T.free
            finite := T.finite
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.hom ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }, ?_⟩
  · have hk := T.isKernel.map (Over.pullback f)
    refine IsPullback.of_iso hk e.symm (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · exact toUnit_unique _ _
    · simp
    · simp
  · intro W p p₀ hp
    have hB := isGrpPullback_pullback T.B f
    have e1 : LiePull.pts hB (T := W) rfl (p ≫ (Over.pullback f).map T.q) = p₀ ≫ T.q := by
      apply Over.OverMorphism.ext
      change (p.left ≫ ((Over.pullback f).map T.q).left) ≫ pullback.fst T.B.hom f = p₀.left ≫ T.q.left
      rw [hp, Category.assoc, Category.assoc, hq.w]
    change p ≫ (Over.pullback f).map T.q = 1 ↔ p₀ ≫ T.q = 1
    rw [← e1]
    exact (MulEquiv.map_eq_one_iff _).symm

theorem ker_iff {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G) {W : Over (Sp k)}
    (p : W ⟶ G) : (letI := T.grpB; p ≫ T.q = 1) ↔
      (letI := T.addCommGroup; ∃ t : W ⟶ splitTorus (Sp k) T.X, t ≫ T.i = p) := by
  letI := T.grpB
  letI := T.addCommGroup
  constructor
  · intro hp
    exact ⟨T.isKernel.lift p (toUnit _) hp, T.isKernel.lift_fst _ _ _⟩
  · rintro ⟨t, rfl⟩
    rw [Category.assoc, T.isKernel.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _

theorem left_cancel {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {W : Over S'} {p q : W ⟶ G'} (e : p.left ≫ φ = q.left ≫ φ) : p = q := by
  apply Over.OverMorphism.ext
  exact h.hom_ext e ((Over.w p).trans (Over.w q).symm)

end PositivityTheory.Xgn.TorusUniformizationCompare

open PositivityTheory.Xgn.TorusUniformizationCompare in
theorem PositivityTheory.Xgn.torus_uniformization_compare : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  intro X Z' G _ G' _ ρ Φ hΦ Xc _ _ _ u _ L k _ _ _ x zL hx GK _ φ hφ τ hinj hker
  letI := τ.addCommGroup
  letI := τ.grpB
  haveI := τ.free
  haveI := τ.finite
  haveI := τ.i_hom
  have hm : Mono τ.i := ⟨fun a b hab => τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  let s : Sp k ⟶ Sp L := spMap (algebraMap L k)
  have hπ := isGrpPullback_pullback GK s
  let ψ : ((Over.pullback s).obj GK).left ⟶ G'.left :=
    hΦ.1.lift (pullback.fst GK.hom s ≫ φ) (((Over.pullback s).obj GK).hom ≫ x) (by
      rw [Category.assoc, hφ.1.w, ← Category.assoc, hπ.1.w, Category.assoc, Category.assoc, hx])
  have hψ1 : ψ ≫ Φ = pullback.fst GK.hom s ≫ φ := hΦ.1.lift_fst _ _ _
  have hψ2 : ψ ≫ G'.hom = ((Over.pullback s).obj GK).hom ≫ x := hΦ.1.lift_snd _ _ _
  have hψ : IsGrpPullback ((Over.pullback s).obj GK) G' x ψ :=
    hΦ.cancel ((hπ.comp hφ).congr hx.symm hψ1.symm) hψ2
  obtain ⟨τ', hτ'⟩ := exists_pullback_ext s GK τ
  have hk := hker _ ψ hψ τ'
  let P : ∀ (A : Type) [CommRing A], (k →+* A) → (Multiplicative Xc →* A) → (Multiplicative τ.X →* A) → Prop :=
    fun A _ g θ θ' => ∃ (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc)
      (t' : Over.mk (spMap g ≫ s) ⟶ splitTorus (Sp L) τ.X), cv t = θ ∧ cv t' = θ' ∧
        (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ
  obtain ⟨e, he⟩ := full (k := k) P
    (by
      intro A _ g θ
      obtain ⟨t, rfl⟩ := cv_surj (spMap g ≫ x) θ
      let p : Over.mk (spMap g) ⟶ (Over.pullback s).obj GK :=
        LiePull.pull hψ (T := Over.mk (spMap g)) (g := spMap g ≫ x) rfl (t ≫ u)
      have hp : p.left ≫ ψ = (t ≫ u).left := hψ.1.lift_fst _ _ _
      have h1 := (hk A g p).2 ⟨t, hp.symm⟩
      let p₀ : Over.mk (spMap g ≫ s) ⟶ GK := LiePull.push hπ (T := Over.mk (spMap g)) rfl p
      have hp₀ : p₀.left = p.left ≫ pullback.fst GK.hom s := rfl
      obtain ⟨t', ht'⟩ := (ker_iff τ p₀).1 ((hτ' _ p p₀ hp₀).1 h1)
      refine ⟨cv t', t, t', rfl, rfl, ?_⟩
      rw [ht', hp₀, ← hp, Category.assoc, Category.assoc, hψ1])
    (by
      rintro A _ g θ θ' θ'' ⟨t₁, t₁', h₁, rfl, e₁⟩ ⟨t₂, t₂', h₂, rfl, e₂⟩
      obtain rfl : t₁ = t₂ := cv_inj (h₁.trans h₂.symm)
      have := left_cancel hφ.1 (e₁.symm.trans e₂)
      rw [(cancel_mono τ.i).1 this])
    (by
      intro A _ g θ'
      obtain ⟨t', rfl⟩ := cv_surj (spMap g ≫ s) θ'
      let p : Over.mk (spMap g) ⟶ (Over.pullback s).obj GK :=
        LiePull.pull hπ (T := Over.mk (spMap g)) (g := spMap g ≫ s) rfl (t' ≫ τ.i)
      have hp : p.left ≫ pullback.fst GK.hom s = (t' ≫ τ.i).left := hπ.1.lift_fst _ _ _
      have h1 := (hτ' _ p (t' ≫ τ.i) hp.symm).2 ((ker_iff τ _).2 ⟨t', rfl⟩)
      obtain ⟨t, ht⟩ := (hk A g p).1 h1
      refine ⟨cv t, t, t', rfl, rfl, ?_⟩
      rw [ht, ← hp, Category.assoc, Category.assoc, hψ1])
    (by
      rintro A _ g θ θ' θ'' ⟨t₁, t₁', rfl, h₁, e₁⟩ ⟨t₂, t₂', rfl, h₂, e₂⟩
      obtain rfl : t₁' = t₂' := cv_inj (h₁.trans h₂.symm)
      have h3 : t₁ ≫ u = t₂ ≫ u := left_cancel hΦ.1 (e₁.trans e₂.symm)
      have h4 : t₁ = t₂ := (injective_iff_map_eq_one (IsMonHom.monoidHom u _)).2 (hinj A g) h3
      rw [h4])
    (by
      rintro A B _ _ g h θ θ' ⟨t, t', rfl, rfl, e⟩
      obtain ⟨r, hr, hr1⟩ := cv_nat h (b := spMap (h.comp g) ≫ x) (by rw [spMap_comp', Category.assoc]) t
      obtain ⟨r', hr', hr1'⟩ := cv_nat h (b := spMap (h.comp g) ≫ s) (by rw [spMap_comp', Category.assoc]) t'
      refine ⟨r, r', hr1, hr1', ?_⟩
      change (r.left ≫ u.left) ≫ Φ = (r'.left ≫ τ.i.left) ≫ φ
      change (t.left ≫ u.left) ≫ Φ = (t'.left ≫ τ.i.left) ≫ φ at e
      rw [hr, hr']
      simp only [Category.assoc] at e ⊢
      rw [e])
    (by
      refine ⟨1, 1, cv_one _, cv_one _, ?_⟩
      rw [MonObj.one_comp, MonObj.one_comp, LiePull.one_left hΦ, LiePull.one_left hφ]
      have : ∀ a b : Sp k ⟶ X, a = b → (1 : Over.mk a ⟶ G).left = (1 : Over.mk b ⟶ G).left := by
        rintro a b rfl; rfl
      exact this _ _ (by rw [Category.assoc, Category.assoc, hx]))
  refine ⟨e, ?_⟩
  intro A _ g b hb b' hb' t t' h
  rw [spMap_comp'] at hb'
  subst hb hb'
  obtain ⟨r, r', hr, hr', H⟩ := he A g (cv t)
  obtain rfl : r = t := cv_inj hr
  obtain rfl : r' = t' := cv_inj (hr'.trans (MonoidHom.ext fun χ => (h χ.toAdd).symm))
  exact H
