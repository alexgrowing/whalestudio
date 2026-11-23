import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.ModuliEmbed

theorem mono_of_unramified_of_points {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (h : ∀ (k : Type) [Field k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y') : Mono f := by
  have hs : Surjective (pullback.diagonal f) := by
    exact ((tfae_universallyInjective f).out 1 3).1 fun (k : Type) [Field k] y y' e => h k y y' e
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem objMap_of_comp_eq {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S T Z : Scheme.{0}} {s : S ⟶ Sp B} {s' : T ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {t : SAB H Z}
    {f : S ⟶ Z} (ν : SABMap o.t t f) {u uA : D.La → (𝟙_ (Over Z) ⟶ t.G)}
    (h₁ : ∀ x, (o.eta x).left ≫ ν.φ = f ≫ (u x).left) (h₂ : ∀ x, (o.etaA x).left ≫ ν.φ = f ≫ (uA x).left)
    {y y' : T ⟶ S} (e : y ≫ f = y' ≫ f) (m : ObjMap o' o y) : Nonempty (ObjMap o' o y') := by
  have hn : ∃ n : SABMap o'.t t (y' ≫ f), n.φ = m.toSABMap.φ ≫ ν.φ := by
    rw [← e]; exact ObjMaps.exists_sab_comp ν m.toSABMap
  obtain ⟨n, hn⟩ := hn
  obtain ⟨m', hm'⟩ := ObjMaps.exists_sab_cancel ν n
  have k : m'.cm.F ≫ ν.cm.F = m.cm.F ≫ ν.cm.F := hm'.symm.trans hn
  exact ⟨⟨m', fun a => ObjComp.sec_cancel ν.cart.1 m'.cart.1.w (Over.w (o.eta a)) (Over.w (o'.eta a)) (h₁ a)
      (by rw [k, ← e]; exact ObjComp.sec_comp (h₁ a) (m.eta a)),
    fun a => ObjComp.sec_cancel ν.cart.1 m'.cart.1.w (Over.w (o.etaA a)) (Over.w (o'.etaA a)) (h₂ a)
      (by rw [k, ← e]; exact ObjComp.sec_comp (h₂ a) (m.etaA a))⟩⟩

end GlobalTheory.ModuliEmbed

namespace GlobalTheory

theorem moduli_isClosedImmersion : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (o : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)) (_ : ObjMap o Xo.univ (pullback.fst _ _)) (Z : Scheme.{0}) (sZ : Z ⟶ Sp c.F) (t : SAB H Z) (f : Xo.XF c ⟶ Z) (ν : SABMap o.t t f) (η' ηA : D.La → (𝟙_ (Over Z) ⟶ t.G)), f ≫ sZ = pullback.snd _ _ → (∀ x, (o.eta x).left ≫ ν.φ = f ≫ (η' x).left) → (∀ x, (o.etaA x).left ≫ ν.φ = f ≫ (ηA x).left) → IsFinite f → IsClosedImmersion f := by
  intro _ _ _ E _ _ _ H D l Xo c o m0 Z sZ t f ν u uA hf h₁ h₂ hfin
  have key : ∀ (T : Scheme.{0}) (y y' : T ⟶ Xo.XF c), y ≫ f = y' ≫ f →
      y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _ ∧
      ∃ o' : Obj D l (baseKA l) ((y ≫ pullback.fst _ _) ≫ Xo.s),
        Nonempty (ObjMap o' Xo.univ (y ≫ pullback.fst _ _)) ∧
        Nonempty (ObjMap o' Xo.univ (y' ≫ pullback.fst _ _)) := by
    intro T y y' e
    refine ⟨by rw [← hf, ← Category.assoc, e, Category.assoc], ?_⟩
    obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ T _
      ((y ≫ pullback.fst _ _) ≫ Xo.s) y rfl rfl
      ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).symm.trans
        (congrArg (((y ≫ pullback.fst _ _) ≫ Xo.s) ≫ ·) (Spec.map_id _).symm))) o
    obtain ⟨m'⟩ := ModuliEmbed.objMap_of_comp_eq ν h₁ h₂ e m
    exact ⟨o', ⟨(ObjComp.objMap_comp m0 m).choose⟩, ⟨(ObjComp.objMap_comp m0 m').choose⟩⟩
  have hu : FormallyUnramified f := by
    refine TangentCrit.formallyUnramified_of_tangent f fun k _ _ w hw => ?_
    obtain ⟨e, o', m, m'⟩ := key _ w (constPt w) (hw.trans (by simp only [constPt, Category.assoc]))
    refine pullback.hom_ext ?_ e
    have e' : constPt w ≫ pullback.fst _ _ = constPt (w ≫ pullback.fst _ _) := by
      simp only [constPt, Category.assoc]
    rw [e'] at m'
    exact (Xo.unram k _ o' m m').trans e'.symm
  have hm : Mono f := by
    refine ModuliEmbed.mono_of_unramified_of_points f fun k _ y y' e => ?_
    obtain ⟨e₂, o', m, m'⟩ := key _ y y' e
    refine pullback.hom_ext ?_ e₂
    refine (Xo.rep _ _ inferInstance o').unique ⟨rfl, m⟩ ⟨?_, m'⟩
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← e₂, Category.assoc]
  exact (IsClosedImmersion.iff_isFinite_and_mono f).2 ⟨hfin, hm⟩

end GlobalTheory
