import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.EFSymmCont
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PackageTie
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.PackageTie2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cols

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter)
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

theorem sharp_add (T T' : Cu X u hK) : sharp hK cs (T + T') = sharp hK cs T + sharp hK cs T' := by
  ext ρ
  simp [sharp, LinearMap.comp_add, map_add]

theorem sharp_smul (c : ℂ) (T : Cu X u hK) : sharp hK cs (c • T) = (starRingEnd ℂ c) • sharp hK cs T := by
  ext ρ
  simp [sharp, LinearMap.comp_smul, map_smul, map_smulₛₗ]

theorem sharp_zero : sharp hK cs 0 = 0 := by
  simpa using sharp_add X u hK cs 0 0

variable {X u hK cs}

def ColT (_hinj : Function.Injective (sharp hK cs)) : Type := Cu X u hK

variable (hinj : Function.Injective (sharp hK cs))

instance : AddCommGroup (ColT hinj) := inferInstanceAs (AddCommGroup (Cu X u hK))
instance : Module ℂ (ColT hinj) := inferInstanceAs (Module ℂ (Cu X u hK))

def shT : ColT hinj → CM cs := fun T => sharp hK cs T

theorem shT_add (T T' : ColT hinj) : shT hinj (T + T') = shT hinj T + shT hinj T' :=
  sharp_add X u hK cs T T'

theorem shT_smul (c : ℂ) (T : ColT hinj) : shT hinj (c • T) = (starRingEnd ℂ c) • shT hinj T :=
  sharp_smul X u hK cs c T

theorem shT_injective : Function.Injective (shT hinj) := hinj

theorem shT_zero : shT hinj 0 = 0 := sharp_zero X u hK cs

@[instance_reducible]
def colCore : InnerProductSpace.Core ℂ (ColT hinj) where
  inner T T' := inner ℂ (shT hinj T') (shT hinj T)
  conj_inner_symm T T' := by simp [inner_conj_symm]
  re_inner_nonneg T := inner_self_nonneg
  add_left T T' T'' := by
    show inner ℂ (shT hinj T'') (shT hinj (T + T')) = _
    rw [shT_add, inner_add_right]
  smul_left T T' c := by
    show inner ℂ (shT hinj T') (shT hinj (c • T)) = _
    rw [shT_smul, inner_smul_right]
  definite T h := by
    have h0 : shT hinj T = 0 := inner_self_eq_zero.1 h
    exact shT_injective hinj (h0.trans (shT_zero hinj).symm)

instance : NormedAddCommGroup (ColT hinj) := (colCore hinj).toNormedAddCommGroup
instance : InnerProductSpace ℂ (ColT hinj) := InnerProductSpace.ofCore (colCore hinj).toCore

theorem inner_colT (T T' : ColT hinj) : inner ℂ T T' = inner ℂ (shT hinj T') (shT hinj T) := rfl

end Cols

section Inv

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {hK : X.LevelSubgroupCharacter}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {cs : ColSys X u what₂}
  {hinj : Function.Injective (sharp hK cs)} (hb : Function.Bijective (shT hinj))

def shInv : CM cs → ColT hinj := (Equiv.ofBijective _ hb).symm

theorem shT_shInv (x : CM cs) : shT hinj (shInv hb x) = x :=
  (Equiv.ofBijective _ hb).apply_symm_apply x

theorem shInv_shT (T : ColT hinj) : shInv hb (shT hinj T) = T :=
  (Equiv.ofBijective _ hb).symm_apply_apply T

theorem shInv_add (x y : CM cs) : shInv hb (x + y) = shInv hb x + shInv hb y := by
  apply hb.1
  rw [shT_shInv, shT_add, shT_shInv, shT_shInv]

theorem shInv_smul (c : ℂ) (x : CM cs) : shInv hb (c • x) = (starRingEnd ℂ c) • shInv hb x := by
  apply hb.1
  rw [shT_shInv, shT_smul, shT_shInv, starRingEnd_self_apply]

def shInvAdd : CM cs →+ ColT hinj := AddMonoidHom.mk' (shInv hb) (shInv_add hb)

include hb in

theorem finiteDimensional_colT : FiniteDimensional ℂ (ColT hinj) := by
  classical
  let b := Module.finBasis ℂ (CM cs)
  refine ⟨⟨Finset.univ.image fun i => shInv hb (b i), ?_⟩⟩
  rw [eq_top_iff]
  intro T _
  rw [← shInv_shT hb T, ← b.sum_repr (shT hinj T)]
  show shInvAdd hb _ ∈ _
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  show shInv hb _ ∈ _
  rw [shInv_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)

end Inv

section Transport

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word} {hK : X.LevelSubgroupCharacter}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {cs : ColSys X u what₂} {cs' : ColSys X u' rows'}
  {hinj : Function.Injective (sharp hK cs)} {hinj' : Function.Injective (sharp hK cs')}
  (hb : Function.Bijective (shT hinj)) (hb' : Function.Bijective (shT hinj'))

def trL (A : CM cs' →L[ℂ] CM cs) : ColT hinj' →ₗ[ℂ] ColT hinj where
  toFun T' := shInv hb (A (shT hinj' T'))
  map_add' T T' := by rw [shT_add, map_add, shInv_add]
  map_smul' c T := by
    rw [shT_smul, map_smul, shInv_smul, starRingEnd_self_apply]
    rfl

include hb' in

def tr (A : CM cs' →L[ℂ] CM cs) : ColT hinj' →L[ℂ] ColT hinj :=
  haveI := finiteDimensional_colT hb'
  LinearMap.toContinuousLinearMap (trL hb A)

include hb' in
theorem tr_apply (A : CM cs' →L[ℂ] CM cs) (T' : ColT hinj') :
    tr hb hb' A T' = shInv hb (A (shT hinj' T')) := rfl

include hb' in
theorem shT_tr (A : CM cs' →L[ℂ] CM cs) (T' : ColT hinj') :
    shT hinj (tr hb hb' A T') = A (shT hinj' T') := by
  rw [tr_apply, shT_shInv]

end Transport

section Data

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D}

abbrev TT (Y : Full X) (u u' : D.what₂.Word) : Type :=
  GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')

abbrev RT (Y : Full X) (u u' : D.what₂.Word) : Type :=
  TermDef.Term D u u' (X.Fu u) (Y.what₂ u)

def fib (Y : Full X) {u u' : D.what₂.Word} (t : RT Y u u') : Type := {s : TT Y u u' // s.toTerm = t}

def liftScalar {Y : Full X} {u u' : D.what₂.Word} (s₁ s₂ : TT Y u u') : Prop :=
  Formalism.MainNotions.S.Lat.IsScalar s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹)

structure FinX (Y : Full X) : Prop where
  shInj : ∀ u, Function.Injective (sharp Y.hK (Y.cs u))
  shSurj : ∀ u, Function.Surjective (sharp Y.hK (Y.cs u))
  inHH : ∀ u, InHH X u Y.hK
  puLin : ∀ u, PuLinear X u Y.hK (Y.Dt u)
  finHH : FiniteDimensional ℂ (HHX X)
  fibFin : ∀ u u' (t : RT Y u u'), Finite (fib Y t)

  pairIndep : ∀ u u' (s₁ s₂ s₁' s₂' : TT Y u u'), s₁.toTerm = s₁'.toTerm → s₂.toTerm = s₂'.toTerm →
    rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ →
    rowOf Y.TR (Y.cs u) (Y.cs u') s₁' = rowOf Y.TR (Y.cs u) (Y.cs u') s₂' →
    s0T s₁ s₂ = s0T s₁' s₂' ∧ (liftScalar s₁ s₂ ↔ liftScalar s₁' s₂')
  Greal : ∀ u u' (t : RT Y u u'), t.G ∈ D.host.F
  cdEx : Formalism.L2.SG.PairVal.CdScaleExists D
  volPos : ∀ u, 0 < Y.volN u ∧ 0 < Y.volH u

variable {Y : Full X}

theorem FinX.shBij (hF : FinX Y) (u : D.what₂.Word) : Function.Bijective (shT (hF.shInj u)) :=
  ⟨hF.shInj u, hF.shSurj u⟩

variable (Y) in

def RP (u u' : D.what₂.Word) : Type :=
  {q : RT Y u u' × RT Y u u' // ∃ (s₁ : fib Y q.1) (s₂ : fib Y q.2),
    rowOf Y.TR (Y.cs u) (Y.cs u') s₁.1 = rowOf Y.TR (Y.cs u) (Y.cs u') s₂.1}

def RP.l1 {u u' : D.what₂.Word} (q : RP Y u u') : TT Y u u' := q.2.choose.1

def RP.l2 {u u' : D.what₂.Word} (q : RP Y u u') : TT Y u u' := q.2.choose_spec.choose.1

@[instance_reducible]
def FinX.fibFT (hF : FinX Y) {u u' : D.what₂.Word} (t : RT Y u u') : Fintype (fib Y t) :=
  @Fintype.ofFinite _ (hF.fibFin u u' t)

end Data

section SOf

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D} {Y : Full X} (hF : FinX Y)

def puL (u : D.what₂.Word) : ColT (hF.shInj u) →ₗ[ℂ] HHX X :=
  PoincareInHH.PoincareSetting.Pu X u Y.hK (Y.Dt u) (Y.reps u) (hF.inHH u) (hF.puLin u)

def puC (u : D.what₂.Word) : ColT (hF.shInj u) →L[ℂ] HHX X :=
  haveI := finiteDimensional_colT (hF.shBij u)
  LinearMap.toContinuousLinearMap (puL hF u)

def aT (u u' : D.what₂.Word) (s : TT Y u u') : ColT (hF.shInj u') →L[ℂ] ColT (hF.shInj u) :=
  tr (hF.shBij u) (hF.shBij u') (aTerm (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s)

def aR (u u' : D.what₂.Word) (t : RT Y u u') : ColT (hF.shInj u') →L[ℂ] ColT (hF.shInj u) :=
  haveI := hF.fibFT t
  ∑ s : fib Y t, aT hF u u' s.1

variable (Y) in

def vT (u u' : D.what₂.Word) (s : TT Y u u') : H1 X u u' (Y.what₂ u) (Y.what₂ u') :=
  vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s

def pvR (u u' : D.what₂.Word) (q : RP Y u u') : ℂ :=
  haveI := hF.fibFT q.1.1
  haveI := hF.fibFT q.1.2
  ∑ r : fib Y q.1.1 × fib Y q.1.2,
    if rowOf Y.TR (Y.cs u) (Y.cs u') r.1.1 = rowOf Y.TR (Y.cs u) (Y.cs u') r.2.1 then inner ℂ (vT Y u u' r.2.1) (vT Y u u' r.1.1) else 0

def sOf : Formalism.MainNotions.S.Draft.SData D.R D.host.F D.host.E D.conjF D.what₂.Word D.what₂.Tau D.hcW where
  cdScale := Formalism.L2.SG.PairVal.cdScaleOf D
  cdScale_pos n ε := (Formalism.L2.SG.PairVal.cdScaleOf_tie D hF.cdEx n ε).1
  Del := D.s.Del
  Del_pos := D.s.Del_pos
  cloud_gap := D.s.cloud_gap
  letter := D.s.letter
  letter_inj := D.s.letter_inj
  u_letter := D.s.u_letter
  HH := HHX X
  hhF := hF.finHH
  Cu u := ColT (hF.shInj u)
  cuF u := finiteDimensional_colT (hF.shBij u)
  Pu u := puC hF u
  volN := Y.volN
  volH := Y.volH
  volN_pos u := (hF.volPos u).1
  volH_pos u := (hF.volPos u).2
  Term u u' := RT Y u u'
  aTerm u u' t := aR hF u u' t
  isId t := Formalism.L2.SG.FourParts.termIsId t
  inS t := Formalism.L2.SG.FourParts.termInS t
  relevant t := t.relevant
  FeqF t := t.FeqF
  Gterm t := ⟨t.G, hF.Greal _ _ t⟩
  atP p := Formalism.L2.S.locC D p
  PlF := Formalism.MainNotions.S.LocalSplitGroups.PlF D
  BBne t p := Formalism.L2.SG.Saturated.termBBne t p
  generic t := t.generic
  Pair u u' := RP Y u u'
  pfst q := q.1.1
  psnd q := q.1.2
  s0 q := s0T q.l1 q.l2
  scalarPair q := liftScalar q.l1 q.l2
  pval {u u'} q := pvR hF u u' q
  ptOf t := Formalism.L2.SG.PairVal.ptOf t
  cTerm {u u'} t :=
    Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t
  massPair q := Formalism.L2.SG.PairVal.massTerm q.1.1
  meanCount u u' w := Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w

end SOf

section Iso

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {Word Tau : Type} {hc : Word → Tau → HCParam R}

structure SIso (s s' : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc) : Type 1 where
  cd : s.cdScale = s'.cdScale
  del : s.Del = s'.Del
  letter : s.letter = s'.letter
  eHH : s.HH ≃ₗᵢ[ℂ] s'.HH
  eCu : ∀ u, s.Cu u ≃ₗᵢ[ℂ] s'.Cu u
  Pu_eq : ∀ u (x : s.Cu u), eHH (s.Pu u x) = s'.Pu u (eCu u x)
  volN : s.volN = s'.volN
  volH : s.volH = s'.volH
  eT : ∀ u u', s.Term u u' ≃ s'.Term u u'
  aTerm_eq : ∀ u u' (t : s.Term u u') (x : s.Cu u'), eCu u (s.aTerm u u' t x) = s'.aTerm u u' (eT u u' t) (eCu u' x)
  isId : ∀ {u u'} (t : s.Term u u'), s.isId t ↔ s'.isId (eT u u' t)
  inS : ∀ {u u'} (t : s.Term u u'), s.inS t ↔ s'.inS (eT u u' t)
  relevant : ∀ {u u'} (t : s.Term u u'), s.relevant t ↔ s'.relevant (eT u u' t)
  FeqF : ∀ {u u'} (t : s.Term u u'), s.FeqF t ↔ s'.FeqF (eT u u' t)
  Gterm : ∀ {u u'} (t : s.Term u u'), s.Gterm t = s'.Gterm (eT u u' t)
  atP : ∀ p, Formalism.L2.S.LocIso (s.atP p) (s'.atP p)
  ePl : s.PlF ≃ s'.PlF
  BBne : ∀ {u u'} (t : s.Term u u') (q : s.PlF), s.BBne t q ↔ s'.BBne (eT u u' t) (ePl q)
  generic : ∀ {u u'} (t : s.Term u u'), s.generic t ↔ s'.generic (eT u u' t)
  eP : ∀ u u', s.Pair u u' ≃ s'.Pair u u'
  pfst : ∀ {u u'} (p : s.Pair u u'), eT u u' (s.pfst p) = s'.pfst (eP u u' p)
  psnd : ∀ {u u'} (p : s.Pair u u'), eT u u' (s.psnd p) = s'.psnd (eP u u' p)
  s0 : ∀ {u u'} (p : s.Pair u u'), s.s0 p = s'.s0 (eP u u' p)
  scalarPair : ∀ {u u'} (p : s.Pair u u'), s.scalarPair p ↔ s'.scalarPair (eP u u' p)
  pval : ∀ {u u'} (p : s.Pair u u'), s.pval p = s'.pval (eP u u' p)
  ptOf : ∀ {u u'} (t : s.Term u u'), s.ptOf t = s'.ptOf (eT u u' t)
  cTerm : ∀ {u u'} (t : s.Term u u'), s.cTerm t = s'.cTerm (eT u u' t)
  massPair : ∀ {u u'} (p : s.Pair u u'), s.massPair p = s'.massPair (eP u u' p)
  meanCount : s.meanCount = s'.meanCount

end Iso

def SConc (D : D7) : Prop :=
  ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X) (hF : FinX Y),
    Formalism.MainNotions.S.AutTie D X.B X.pl ∧ X.LevelSubgroupNormalized ∧ (∀ u, ColsLink X u Y.hK) ∧
    X.MeasTie hb ∧ Formalism.L2.SG.MassDataConc.MeasCompat X ∧ Formalism.L2.SG.WuDecay.WuDecay X ∧
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ Nonempty (SIso D.s (sOf hF))

section Ties

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D} {Y : Full X} (hF : FinX Y)

theorem finrank_cols (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) :
    Module.finrank ℂ (ColT (hF.shInj u)) = D.duS u := by
  exact (hI.eCu u).toLinearEquiv.finrank_eq.symm.trans (D.s_Cu u).finrank_eq

def DimTie (u : D.what₂.Word) : Prop :=
  (Module.finrank ℂ (X.Vpi u) : ℝ) = Formalism.MainNotions.S.dimPi (hc := D.hcW) u

def KTie (u u' : D.what₂.Word) : Prop :=
  DimTie (X := X) u → DimTie (X := X) u' →
  Formalism.L2.SG.TermOp.KExpansion (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (Y.Dt u) (Y.Dt u') →
  Formalism.L2.SG.TermOp.AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
    Formalism.MainNotions.S.KExpansion (sOf hF) u u' ∧ Formalism.MainNotions.S.KAbsConv (sOf hF) u u'

def NormTie (u u' : D.what₂.Word) : Prop :=
  DimTie (X := X) u → DimTie (X := X) u' →
  Formalism.L2.SG.TermOp.KExpansion (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (Y.Dt u) (Y.Dt u') →
  Formalism.L2.SG.TermOp.AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
  (Y.tO u u').IdDegenerate → (Y.tO u u').part (Y.tO u u').degSet = 0 →
    ‖(Y.tO u u').K0‖ ^ 2 = Formalism.MainNotions.S.hsNormSq (Formalism.MainNotions.S.Kmat (sOf hF) u u')

def IsoNorm : Prop :=
  ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {Word Tau : Type} [Fintype Tau] {hc : Word → Tau → HCParam R}
    (s s' : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc), SIso s s' →
      ∀ u u', Formalism.MainNotions.S.hsNormSq (Formalism.MainNotions.S.Kmat s u u') = Formalism.MainNotions.S.hsNormSq (Formalism.MainNotions.S.Kmat s' u u')

end Ties

section Link

open Formalism.L2.SG.Full

def ParametersTermRelations (D : D7) (L : SizeData₂ D) : Prop :=
  0 ≤ L.sc.b → IsoNorm →
  ∀ (X : HidaSetting D) (Y : Full X) (hF : FinX Y), Nonempty (SIso D.s (sOf hF)) →
  ∀ u u', u ≠ u' →
    DimTie (X := X) u → DimTie (X := X) u' →
    Formalism.L2.SG.TermOp.KExpansion (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (Y.Dt u) (Y.Dt u') →
    Formalism.L2.SG.TermOp.AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
    (Y.tO u u').IdDegenerate → (Y.tO u u').part (Y.tO u u').degSet = 0 →
    NormTie hF u u' →
    (∃ (ι : Type) (_ : Fintype ι) (G : Formalism.FourierDecayAlt.Sz.Glob ι) (de : ℕ → ℝ) (T : ℕ) (du du' : ℝ),
      Formalism.L2.SG.PackageTie.SizeTie D L u u' G de T L.sc.b du du' ∧
      ‖(Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * (du * du' / (G.size de T du).Dstar)) →
    L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar

theorem packageTieConc (D : D7) (L : SizeData₂ D) : ParametersTermRelations D L := by
  intro hb hIso X Y hF hI u u' _ hDu hDu' hKE hAC hId hdeg hNT hSz
  obtain ⟨hI⟩ := hI
  obtain ⟨ι, _, G, de, T, du, du', ⟨_, hdu, hdu', hDs⟩, hK0⟩ := hSz
  have h1 : L.hsSq u u' = ‖(Y.tO u u').K0‖ ^ 2 := by
    rw [hNT hDu hDu' hKE hAC hId hdeg]
    exact hIso D.s (sOf hF) hI u u'
  rw [h1]
  rw [hDs, hdu, hdu'] at hK0
  have hbpow : L.sc.b ^ (-(6 : ℝ)) = (L.sc.b ^ 6)⁻¹ := by
    rw [Real.rpow_neg hb, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hbpow]
  exact hK0.trans_eq (by ring)

end Link

end Formalism.L2.SG.PackageTie2
