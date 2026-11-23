import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FullLevelModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelChangeActsOnUnitaryFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Models GlobalTheory.IndefiniteRowSideFullHecke.FullLevelModel

noncomputable section

namespace GlobalTheory.ModelTypings

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem RZ_eq (H : Host E) (S A : ℕ) : RZ H S A = oRing H A S := by
  unfold RZ oRing w0C
  rw [Set.pair_comm]

section Models

variable {U U' : Scheme.{0}} {F F' : Type} [Field F] [Field F'] {c : U ⟶ Sp F} {c' : U' ⟶ Sp F'} {t₀ : SAB H U}
  {t₀' : SAB H U'} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* F} {β' : O' →+* F'}

def cptEquiv : Cpt c t₀ β ≃ ModelOf c t₀ β where
  toFun C := ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.t⟩, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.m, C.ab_gen⟩
  invFun Y := ⟨Y.X, Y.s, Y.normal, Y.proj, Y.flat, Y.jQ, Y.jQ_over, Y.jQ_open, Y.jQ_dense, Y.t, Y.m, Y.ab_gen⟩
  left_inv _ := rfl
  right_inv _ := rfl

def aboveEquiv (C' : Cpt c' t₀' β') (C : Cpt c t₀ β) (b : O →+* O') (r : U' ⟶ U) (ν : SABMap t₀' t₀ r) :
    C'.Above C b r ν ≃ {f : FinMap (cptEquiv C').toPModel (cptEquiv C).toPModel b //
      (cptEquiv C').j ≫ f.π = r ≫ (cptEquiv C).j ∧ (cptEquiv C').m.φ ≫ f.mu.φ = ν.φ ≫ (cptEquiv C).m.φ} where
  toFun A := ⟨⟨A.π, A.π_over, A.fin, A.mu⟩, A.j_comm, A.φ_comm⟩
  invFun f := ⟨f.1.π, f.1.overB, f.1.fin, f.1.mu, f.2.1, f.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Models

theorem splitFib_of_splitFibres {O : Type} [CommRing O] (Y : PModel H O) (h : Y.SplitFibres) : SplitFib Y.t.G := by
  intro x
  refine ⟨Y.X.residueField x, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have : Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField x) (Y.X.residueField x))) ≫
      Y.X.fromSpecResidueField x = Y.X.fromSpecResidueField x := by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField x) (Y.X.residueField x))) = 𝟙 _ from
      Spec.map_id _, Category.id_comp]
  have key : ∀ f : Sp (Y.X.residueField x) ⟶ Y.X, f = Y.X.fromSpecResidueField x →
      ∃ S : SplitExt (Sp (Y.X.residueField x)), S.IsGt ((Over.pullback f).obj Y.t.G) := by
    rintro f rfl
    exact h x
  exact key _ this

theorem hasTheta_of_pushInvertible {X : Scheme.{0}} {G : Over X} {L : LB G.left} (h : PushInvertible G L) :
    HasTheta G L := fun x =>
  let ⟨V, hV, θ, hθ, _, h⟩ := h x
  ⟨V, hV, θ, hθ, h⟩

theorem incl_self {R : Subring ℂ} (h : R ≤ R) : spMap (Subring.inclusion h) = 𝟙 _ := Spec.map_id _

theorem isIso_incl {R R' : Subring ℂ} (h : R = R') : IsIso (spMap (Subring.inclusion h.le)) := by
  subst h
  rw [incl_self]
  infer_instance

theorem isProjOver_incl {R R' : Subring ℂ} (h : R = R') {X : Scheme.{0}} {s : X ⟶ Sp R'} (hs : IsProjOver s) :
    IsProjOver (s ≫ spMap (Subring.inclusion h.le)) := by
  subst h
  rwa [incl_self, Category.comp_id]

theorem isQProjOver_incl {R R' : Subring ℂ} (h : R = R') {X : Scheme.{0}} {s : X ⟶ Sp R'} (hs : IsQProjOver s) :
    IsQProjOver (s ≫ spMap (Subring.inclusion h.le)) := by
  subst h
  rwa [incl_self, Category.comp_id]

theorem incl_incl {R R' : Subring ℂ} (h : R = R') :
    spMap (Subring.inclusion h.le) ≫ spMap (Subring.inclusion h.symm.le) = 𝟙 _ := by
  subst h
  rw [incl_self, Category.comp_id]

theorem isFinite_lift_iff {X X' B B' B₁ B₁' : Scheme.{0}} {π : X' ⟶ X} {s : X ⟶ B} {s' : X' ⟶ B'} {b : B' ⟶ B}
    (i : B ⟶ B₁) (i' : B' ⟶ B₁') [IsIso i] [IsIso i'] {b₁ : B₁' ⟶ B₁} (hb : b ≫ i = i' ≫ b₁) (h : π ≫ s = s' ≫ b)
    (h₁ : π ≫ s ≫ i = (s' ≫ i') ≫ b₁) : IsFinite (pullback.lift π _ h₁) ↔ IsFinite (pullback.lift π s' h) := by
  have e : pullback.lift π _ h₁ =
      pullback.lift π s' h ≫ pullback.map s b (s ≫ i) b₁ (𝟙 _) i' i (Category.id_comp _).symm hb := by
    apply pullback.hom_ext <;> simp
  refine ⟨fun hf => ?_, fun hf => by rw [e]; infer_instance⟩
  rw [(IsIso.comp_inv_eq _).2 e |>.symm]
  infer_instance

def sabCast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    SABMap t' t g := ⟨m.cm, h ▸ m.cart, m.base.trans h, m.act, m.lin⟩

def sabCmp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) : SABMap t'' t (g ≫ f) :=
  (sabComp pullCubComp E H _ _ _ t t' t'' f g m m').choose

theorem sabCmp_φ {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) : (sabCmp m' m).φ = m'.φ ≫ m.φ :=
  (sabComp pullCubComp E H _ _ _ t t' t'' f g m m').choose_spec

theorem sab_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n

section Rebase

variable {U : Scheme.{0}} {F : Type} [Field F] {c : U ⟶ Sp F} {t₀ : SAB H U} {R R' : Subring ℂ}
  {β : R →+* F} {β' : R' →+* F}

def genIso (h : R = R') (hβ : β'.comp (Subring.inclusion h.le) = β) {X : Scheme.{0}} (s : X ⟶ Sp R') :
    pullback s (spMap β') ⟶ pullback (s ≫ spMap (Subring.inclusion h.le)) (spMap β) :=
  pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (spMap (Subring.inclusion h.le)) (Category.id_comp _).symm
    (by rw [Category.id_comp, ← spMap_comp, hβ])

instance (h : R = R') (hβ : β'.comp (Subring.inclusion h.le) = β) {X : Scheme.{0}} (s : X ⟶ Sp R') :
    IsIso (genIso h hβ s) := by
  have := isIso_incl h
  unfold genIso
  infer_instance

@[reassoc] theorem genIso_fst (h : R = R') (hβ : β'.comp (Subring.inclusion h.le) = β) {X : Scheme.{0}} (s : X ⟶ Sp R') :
    genIso h hβ s ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [genIso]

theorem genIso_snd (h : R = R') (hβ : β'.comp (Subring.inclusion h.le) = β) {X : Scheme.{0}} (s : X ⟶ Sp R') :
    genIso h hβ s ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [genIso]

abbrev rebase (h : R = R') (hβ : β'.comp (Subring.inclusion h.le) = β) (Y : ModelOf c t₀ β') : Cpt c t₀ β where
  X := Y.X
  s := Y.s ≫ spMap (Subring.inclusion h.le)
  normal := Y.normal
  proj := isProjOver_incl h Y.proj
  flat := by
    have := isIso_incl h
    have := Y.flat
    infer_instance
  jQ := Y.jQ ≫ genIso h hβ Y.s
  jQ_over := by rw [Category.assoc, genIso_snd, Y.jQ_over]
  jQ_open := by
    have := Y.jQ_open
    infer_instance
  jQ_dense := by
    have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
    exact (Y.jQ ≫ genIso h hβ Y.s).denseRange
  t := Y.t
  m := sabCast Y.m (by rw [Category.assoc, genIso_fst])
  ab_gen := by
    ext x
    obtain ⟨y, rfl⟩ := (genIso h hβ Y.s).surjective x
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, genIso_fst, ← Set.mem_preimage, Y.ab_gen]
    refine exists_congr fun z => ?_
    rw [Scheme.Hom.comp_apply]
    exact (genIso h hβ Y.s).isOpenEmbedding.injective.eq_iff.symm

end Rebase

end GlobalTheory.ModelTypings

end
