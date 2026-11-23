import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChange
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafCore
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MvPolynomial
open GroundTheory.Arith.Etale (pullbackUnitApp)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}

variable (A) in

abbrev cmap :
    C(ProjectiveSpectrum.top (grading B n), ProjectiveSpectrum.top (grading A n)) :=
  ProjectiveSpectrum.comap (gradedMap A B n) (irrelevant_le_map A B n)

variable (A) in

abbrev pt (y : ProjectiveSpectrum (grading B n)) : ProjectiveSpectrum (grading A n) :=
  ProjectiveSpectrum.comapFun (gradedMap A B n) (irrelevant_le_map A B n) y

def locMap (y : ProjectiveSpectrum (grading B n)) :
    ProjTwist.Loc (grading A n) (pt A y) →+* ProjTwist.Loc (grading B n) y :=
  Localization.localRingHom _ _
    (gradedMap A B n : MvPolynomial (Fin (n + 1)) A →+* MvPolynomial (Fin (n + 1)) B) rfl

lemma locMap_mk (y : ProjectiveSpectrum (grading B n)) (r : MvPolynomial (Fin (n + 1)) A)
    (s : (pt A y).asHomogeneousIdeal.toIdeal.primeCompl) :
    locMap y (Localization.mk r s) =
      Localization.mk (gradedMap A B n r)
        (⟨gradedMap A B n s, s.2⟩ : y.asHomogeneousIdeal.toIdeal.primeCompl) :=
  Localization.localRingHom_mk _ _ _ _ _ _

variable (k : ℤ)

def twistPushSec {V : (projectiveSpace A n).Opens} (s : Γ(twistingSheaf (grading A n) k, V)) :
    Γ(twistingSheaf (grading B n) k, baseChangeMap A B n ⁻¹ᵁ V) :=
  ProjTwist.mkSection (fun y => locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩))
    (by
      intro y
      obtain ⟨W, hyW, iW, i, j, hij, r, t, hr, ht, htn, w⟩ :=
        ProjTwist.isLocallyFraction_val s ⟨pt A y.1, y.2⟩
      refine ⟨W.comap (cmap (B := B) A), hyW, homOfLE (fun z hz => (leOfHom iW) hz), i, j, hij,
        gradedMap A B n r, gradedMap A B n t, (gradedMap A B n).2 hr, (gradedMap A B n).2 ht,
        fun z => htn ⟨pt A z.1, z.2⟩, fun z => ?_⟩
      have e := w ⟨pt A z.1, z.2⟩
      change locMap z.1 (ProjTwist.val s ⟨pt A z.1, _⟩) = _
      change ProjTwist.val s ⟨pt A z.1, _⟩ = _ at e
      rw [e]
      exact locMap_mk _ _ _)

lemma val_app_apply {V : (projectiveSpace A n).Opens} (t : Γ(projectiveSpace A n, V))
    (y : baseChangeMap A B n ⁻¹ᵁ V) :
    ((((baseChangeMap A B n).app V t) : Γ(Proj (grading B n), _)).1 y).val =
      locMap y.1 ((t.1 ⟨pt A y.1, y.2⟩).val) := by
  have : y.1.asHomogeneousIdeal.toIdeal.IsPrime :=
    ProjectiveSpectrum.isPrime (y.1 : ProjectiveSpectrum (grading B n))
  show HomogeneousLocalization.val (HomogeneousLocalization.localRingHom (gradedMap A B n)
    (pt A y.1).asHomogeneousIdeal.toIdeal y.1.asHomogeneousIdeal.toIdeal rfl (t.1 ⟨pt A y.1, y.2⟩)) = _
  exact HomogeneousLocalization.val_localRingHom _

lemma twistPushSec_smul {V : (projectiveSpace A n).Opens} (t : Γ(projectiveSpace A n, V))
    (s : Γ(twistingSheaf (grading A n) k, V)) :
    twistPushSec (B := B) k (t • s) = (baseChangeMap A B n).app V t • twistPushSec (B := B) k s := by
  apply ProjTwist.ext
  funext y
  show locMap y.1 ((t.1 ⟨pt A y.1, y.2⟩).val * ProjTwist.val s ⟨pt A y.1, y.2⟩) =
    (((baseChangeMap A B n).app V t).1 y).val * locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩)
  exact (map_mul (locMap y.1) _ _).trans (congrArg (· * _) (val_app_apply t y).symm)

lemma twistPushSec_add {V : (projectiveSpace A n).Opens}
    (s s' : Γ(twistingSheaf (grading A n) k, V)) :
    twistPushSec (B := B) k (s + s') = twistPushSec k s + twistPushSec k s' := by
  apply ProjTwist.ext
  funext y
  show locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩ + ProjTwist.val s' ⟨pt A y.1, y.2⟩) =
    locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩) + locMap y.1 (ProjTwist.val s' ⟨pt A y.1, y.2⟩)
  exact map_add _ _ _

def twistToPushforward :
    twistingSheaf (grading A n) k ⟶
      (Scheme.Modules.pushforward (baseChangeMap A B n)).obj (twistingSheaf (grading B n) k) :=
  ⟨{ app V := ModuleCat.ofHom (X := (twistingSheaf (grading A n) k).val.obj V)
      (Y := ((Scheme.Modules.pushforward (baseChangeMap A B n)).obj
        (twistingSheaf (grading B n) k)).val.obj V)
      { toFun := fun s => twistPushSec k (V := V.unop) s
        map_add' := fun s s' => twistPushSec_add k s s'
        map_smul' := fun t s => twistPushSec_smul k t s }
     naturality := fun {V V'} i => by
      ext s
      exact ProjTwist.ext (funext fun y => rfl) }⟩

def pullbackTwistingSheafMap :
    (Scheme.Modules.pullback (baseChangeMap A B n)).obj (twistingSheaf (grading A n) k) ⟶
      twistingSheaf (grading B n) k :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap A B n)).homEquiv _ _).symm
    (twistToPushforward k)

lemma pullbackTwistingSheafMap_unit {V : (projectiveSpace A n).Opens}
    (s : Γ(twistingSheaf (grading A n) k, V)) :
    (pullbackTwistingSheafMap (B := B) k).app _ (pullbackUnitApp (baseChangeMap A B n) _ V s) =
      twistPushSec k s := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap A B n)).homEquiv_unit
    (twistingSheaf (grading A n) k) (twistingSheaf (grading B n) k)
    (pullbackTwistingSheafMap k))
  rw [pullbackTwistingSheafMap, Equiv.apply_symm_apply] at h
  have h2 := congrArg (fun g => (Scheme.Modules.Hom.app g V) s) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h2
  exact h2.symm

lemma twistPushSec_upow {u : MvPolynomial (Fin (n + 1)) A} (hu : u ∈ grading A n 1) :
    twistPushSec (B := B) k (ProjTwist.upow (grading A n) hu k) =
      ProjTwist.upow (grading B n) ((gradedMap A B n).2 hu) k := by
  apply ProjTwist.ext
  funext y
  change locMap y.1 (ProjTwist.val (ProjTwist.upow (grading A n) hu k) ⟨pt A y.1, y.2⟩) = _
  erw [ProjTwist.val_upow, ProjTwist.val_upow]
  unfold ProjTwist.twistFrac
  refine (locMap_mk _ _ _).trans ?_
  congr 1
  · exact map_pow (gradedMap A B n) u _
  · exact Subtype.ext (map_pow (gradedMap A B n) u _)

instance isIso_pullbackTwistingSheafMap :
    IsIso (pullbackTwistingSheafMap (A := A) (B := B) (n := n) k) := by
  apply isIso_of_isBasisOn
  intro y
  obtain ⟨j, hj⟩ := exists_mem_stdOpen_proj ((baseChangeMap A B n).base y)
  refine ⟨baseChangeMap A B n ⁻¹ᵁ stdOpen A n j, hj,
    pullbackUnitApp (baseChangeMap A B n) _ (stdOpen A n j)
      (ProjTwist.upow (grading A n) (X_mem j) k),
    isBasisOn_pullbackUnitApp _ (ProjTwist.isBasisOn_upow _ (X_mem j) k), ?_⟩
  have key : ((preMod _).map (pullbackTwistingSheafMap (B := B) k)).app _
      (pullbackUnitApp (baseChangeMap A B n) _ (stdOpen A n j)
        (ProjTwist.upow (grading A n) (X_mem j) k)) =
      ProjTwist.upow (grading B n) ((gradedMap A B n).2 (X_mem j)) k :=
    (pullbackTwistingSheafMap_unit k _).trans (twistPushSec_upow k _)
  rw [key]
  exact ProjTwist.isBasisOn_upow _ _ k

variable (A B n) in

def pullbackTwistingSheafIso :
    (Scheme.Modules.pullback (baseChangeMap A B n)).obj (twistingSheaf (grading A n) k) ≅
      twistingSheaf (grading B n) k :=
  asIso (pullbackTwistingSheafMap k)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
