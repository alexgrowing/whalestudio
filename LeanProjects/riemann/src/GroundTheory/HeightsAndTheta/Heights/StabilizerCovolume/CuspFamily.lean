import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CuspData
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

structure CuspDataOn (D : ComponentData II Ψ K ι Ω E) (S : Set ((Σ k, ι k) → ℂ)) (O : Type) [CommRing O]
    (abelian₂ : Type) [AddCommGroup abelian₂] [Module O abelian₂] where

  rank : ℕ
  basis : Module.Basis (Fin rank) ℤ abelian₂

  form : abelian₂ →ₗ[ℤ] abelian₂ →ₗ[ℤ] ℤ
  alt : ∀ v, form v v = 0
  unimod : IsUnit (Matrix.of fun a b => form (basis a) (basis b)).det

  emb : Ψ → O →+* ℂ

  normSq : ((Σ k, ι k) → ℂ) → abelian₂ → ℝ
  normSq_pos : ∀ z ∈ S, ∀ v, v ≠ 0 → 0 < normSq z v
  form_le : ∀ z ∈ S, ∀ v w, ((form v w : ℤ) : ℝ) ^ 2 ≤ normSq z v * normSq z w

  lie : ((Σ k, ι k) → ℂ) → Ψ → abelian₂ → Fin (D.N - D.j) → ℂ
  lie_add : ∀ z τ v w, lie z τ (v + w) = lie z τ v + lie z τ w
  lie_smul : ∀ z τ (a : O) v, lie z τ (a • v) = emb τ a • lie z τ v
  lie_le : ∀ z ∈ S, ∀ v, ∑ τ, ∑ c, ‖lie z τ v c‖ ^ 2 ≤ normSq z v
  inj : ∀ z ∈ S, ∀ τ (I : Submodule O abelian₂), IsIsoSub form I → ∀ (ρ : ℕ) (v : Fin ρ → abelian₂),
    (∀ a, v a ∈ I) → LinearIndependent O v → LinearIndependent ℂ fun a => lie z τ (v a)
  torus : ∀ z ∈ S, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
    normSq (torusSmul c z) = normSq z ∧ lie (torusSmul c z) = lie z

namespace CuspDataOn

variable {D : ComponentData II Ψ K ι Ω E} {S T : Set ((Σ k, ι k) → ℂ)} {O abelian₂ : Type} [CommRing O]
  [AddCommGroup abelian₂] [Module O abelian₂] (C : CuspDataOn D S O abelian₂)

def restrict (hT : T ⊆ S) : CuspDataOn D T O abelian₂ where
  rank := C.rank
  basis := C.basis
  form := C.form
  alt := C.alt
  unimod := C.unimod
  emb := C.emb
  normSq := C.normSq
  normSq_pos z hz := C.normSq_pos z (hT hz)
  form_le z hz := C.form_le z (hT hz)
  lie := C.lie
  lie_add := C.lie_add
  lie_smul := C.lie_smul
  lie_le z hz := C.lie_le z (hT hz)
  inj z hz := C.inj z (hT hz)
  torus z hz := C.torus z (hT hz)

def gramLie (z : (Σ k, ι k) → ℂ) (τ : Ψ) {ρ : ℕ} (v : Fin ρ → abelian₂) : Matrix (Fin ρ) (Fin ρ) ℂ :=
  Matrix.of fun a b => ∑ c, starRingEnd ℂ (C.lie z τ (v a) c) * C.lie z τ (v b) c

open Classical in

def Nz (z : (Σ k, ι k) → ℂ) (I : Submodule O abelian₂) : ℝ :=
  if h : ∃ ρ v, IsNzFamily I ρ v then
    (∏ τ, (C.gramLie z τ h.choose_spec.choose).det.re) /
      ((Submodule.span O (Set.range h.choose_spec.choose)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ)
  else 1

def cuspWeight (z : (Σ k, ι k) → ℂ) : ℝ :=
  max 0 (sSup {x | ∃ I : Submodule O abelian₂, I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub C.form I ∧
    x = -Real.log (C.Nz z I)})

theorem restrict_Nz (hT : T ⊆ S) : (C.restrict hT).Nz = C.Nz := rfl

theorem restrict_cuspWeight (hT : T ⊆ S) : (C.restrict hT).cuspWeight = C.cuspWeight := rfl

def toCuspData (C : CuspDataOn D D.Xo O abelian₂) : CuspData D O abelian₂ where
  rank := C.rank
  basis := C.basis
  form := C.form
  alt := C.alt
  unimod := C.unimod
  emb := C.emb
  normSq := C.normSq
  normSq_pos := C.normSq_pos
  form_le := C.form_le
  lie := C.lie
  lie_add := C.lie_add
  lie_smul := C.lie_smul
  lie_le := C.lie_le
  inj := C.inj
  torus := C.torus

end CuspDataOn

def CuspDataOn.ofCuspData {D : ComponentData II Ψ K ι Ω E} {O abelian₂ : Type}
    [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂) : CuspDataOn D D.Xo O abelian₂ where
  rank := Cd.rank
  basis := Cd.basis
  form := Cd.form
  alt := Cd.alt
  unimod := Cd.unimod
  emb := Cd.emb
  normSq := Cd.normSq
  normSq_pos := Cd.normSq_pos
  form_le := Cd.form_le
  lie := Cd.lie
  lie_add := Cd.lie_add
  lie_smul := Cd.lie_smul
  lie_le := Cd.lie_le
  inj := Cd.inj
  torus := Cd.torus

section Bridge

variable {D : ComponentData II Ψ K ι Ω E} {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂]

theorem CuspDataOn.toCuspData_ofCuspData (Cd : CuspData D O abelian₂) : (CuspDataOn.ofCuspData Cd).toCuspData = Cd := rfl

theorem CuspDataOn.ofCuspData_toCuspData (C : CuspDataOn D D.Xo O abelian₂) : CuspDataOn.ofCuspData C.toCuspData = C := rfl

theorem CuspDataOn.ofCuspData_Nz (Cd : CuspData D O abelian₂) : (CuspDataOn.ofCuspData Cd).Nz = Cd.Nz := rfl

theorem CuspDataOn.ofCuspData_cuspWeight (Cd : CuspData D O abelian₂) : (CuspDataOn.ofCuspData Cd).cuspWeight = Cd.cuspWeight := rfl

end Bridge

structure CuspFamily (D : ComponentData II Ψ K ι Ω E) where

  Comp : Type
  [fintype : Fintype Comp]

  comp : ((Σ k, ι k) → ℂ) → Comp
  comp_onto : ∀ c, ∃ z ∈ D.Xo, comp z = c
  comp_locConst : IsLocallyConstant fun z : D.Xo => comp z
  comp_torus : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → comp (torusSmul c z) = comp z

  O : Comp → Type

  abelian₂ : Comp → Type
  [commRing : ∀ c, CommRing (O c)]
  [addCommGroup : ∀ c, AddCommGroup (abelian₂ c)]
  [module : ∀ c, Module (O c) (abelian₂ c)]

  cusp : ∀ c, CuspDataOn D {z | z ∈ D.Xo ∧ comp z = c} (O c) (abelian₂ c)

attribute [instance] CuspFamily.fintype CuspFamily.commRing CuspFamily.addCommGroup CuspFamily.module

namespace CuspFamily

variable {D : ComponentData II Ψ K ι Ω E} (F : CuspFamily D)

def Nz (z : (Σ k, ι k) → ℂ) (I : Submodule (F.O (F.comp z)) (F.abelian₂ (F.comp z))) : ℝ :=
  (F.cusp (F.comp z)).Nz z I

def Uat (z : (Σ k, ι k) → ℂ) : ℝ := (F.cusp (F.comp z)).cuspWeight z

open Classical in

theorem Uat_eq_sum (z : (Σ k, ι k) → ℂ) :
    F.Uat z = ∑ c, if F.comp z = c then (F.cusp c).cuspWeight z else 0 := by
  rw [Finset.sum_eq_single (F.comp z) (fun c _ hc => if_neg (Ne.symm hc)) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl]
  rfl

variable (H : HodgeData D)

open Classical in

def vol (c : F.Comp) : ℝ :=
  ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) fun z => if F.comp z = c then 1 else 0

open Classical in

def meanUOn (c : F.Comp) : ℝ :=
  ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H)
      (fun z => if F.comp z = c then (F.cusp c).cuspWeight z else 0) / F.vol H c

def meanU : ℝ :=
  ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) F.Uat / degMu H

def cuspCorr (z : (Σ k, ι k) → ℂ) : ℝ := phMu H z + F.Uat z / 2

end CuspFamily

section Const

variable {D : ComponentData II Ψ K ι Ω E} {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂]

def CuspFamily.const (Cd : CuspData D O abelian₂) (hXo : D.Xo.Nonempty) : CuspFamily D where
  Comp := Unit
  comp _ := ()
  comp_onto _ := ⟨hXo.some, hXo.some_mem, rfl⟩
  comp_locConst := IsLocallyConstant.const ()
  comp_torus _ _ _ _ := rfl
  O _ := O
  abelian₂ _ := abelian₂
  cusp _ := (CuspDataOn.ofCuspData Cd).restrict fun _ hz => hz.1

variable (Cd : CuspData D O abelian₂) (hXo : D.Xo.Nonempty) (H : HodgeData D)

theorem CuspFamily.const_Uat : (CuspFamily.const Cd hXo).Uat = Cd.cuspWeight := rfl

theorem CuspFamily.const_meanU : (CuspFamily.const Cd hXo).meanU H = LowerBoundFree.meanU H Cd := rfl

theorem CuspFamily.const_cuspCorr : (CuspFamily.const Cd hXo).cuspCorr H = LowerBoundFree.cuspCorr H Cd := rfl

end Const

structure ComponentFamilySetting (D : ComponentData II Ψ K ι Ω E) where

  H : HodgeData D

  F : CuspFamily D

  M : XModel D

  S : LogLogRegularisationSetting M D.Xo (muLine H)
  S_tied : S.IsTied

  S' : BoundedRegularisationSetting M D.Xo H.aMu (F.cuspCorr H)
  S'_tied : S'.IsTied

  rd : ℝ

  Lval : ℝ

def CuspMeanFam {D : ComponentData II Ψ K ι Ω E} (Cu : ℝ) (X : ComponentFamilySetting D) : Prop :=
  1 ≤ D.j' → 3 * D.j' + 1 ≤ D.N → ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B →
    X.F.meanU X.H ≤ Cu * D.f * D.j' * abelian₂ B X.rd X.Lval

def StokesLimitFam.Hyp {D : ComponentData II Ψ K ι Ω E} (X : ComponentFamilySetting D) (B : ℕ) (a : ℝ) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ((D.n + 1 : ℕ) : ℝ) * (a - (p : ℝ) / q * D.KA) * geomDegMUc X.H X.S' B p q t' ≤
      topMUc X.H X.S' B p q t'

def StokesLimitFam.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D) (B : ℕ) (a : ℝ),
    IsIntersectionSystem II → 4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimitFam.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - X.F.meanU X.H / 2) * degMu X.H ≤ arLim X.H X.S B

section Bridge

variable [DecidableEq Ψ] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

def ComponentFamilySetting.componentFamilySetting_ofSetting (X : ComponentSetting D O Lt) (hXo : D.Xo.Nonempty) : ComponentFamilySetting D where
  H := X.H
  F := CuspFamily.const X.Cd hXo
  M := X.M
  S := X.S
  S_tied := X.S_tied
  S' := X.S'
  S'_tied := X.S'_tied
  rd := X.rd
  Lval := X.Lval

omit [DecidableEq Ψ] in
theorem CuspMean.iff_fam (Cu : ℝ) (X : ComponentSetting D O Lt) (hXo : D.Xo.Nonempty) :
    CuspMean Cu X ↔ CuspMeanFam Cu (ComponentFamilySetting.componentFamilySetting_ofSetting X hXo) := Iff.rfl

omit [DecidableEq Ψ] in
theorem StokesLimit.hyp_iff_fam (X : ComponentSetting D O Lt) (hXo : D.Xo.Nonempty) (B : ℕ) (a : ℝ) :
    StokesLimit.Hyp X B a ↔ StokesLimitFam.Hyp (ComponentFamilySetting.componentFamilySetting_ofSetting X hXo) B a := Iff.rfl

theorem StokesLimit.of_fam (h : StokesLimitFam.Statement) (X : ComponentSetting D O Lt) (hXo : D.Xo.Nonempty) (B : ℕ)
    (a : ℝ) (hII : IsIntersectionSystem II) (hB : 4 * D.f + 2 ≤ B) (hlim : ArLimExists X.H X.S B)
    (hyp : StokesLimit.Hyp X B a) :
    ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B :=
  h II Ψ K ι Ω E D (ComponentFamilySetting.componentFamilySetting_ofSetting X hXo) B a hII hB hlim hyp

end Bridge

namespace Line

open GroundTheory.Heights₂.Heights.LowerBoundFree.Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem lineData_Xo_nonempty : (lineData II hII).Xo.Nonempty :=
  ⟨fun _ => 1, mem_mcPts_line.2 ⟨0, one_ne_zero⟩, Set.notMem_empty _⟩

def planeFamily : CuspFamily (lineData II hII) :=
  CuspFamily.const (planeCusp II hII) (lineData_Xo_nonempty II hII)

theorem planeFamily_isotropic (z : (Σ _ : Unit, Fin 2) → ℂ) :
    ∃ I : Submodule ((planeFamily II hII).O ((planeFamily II hII).comp z))
        ((planeFamily II hII).abelian₂ ((planeFamily II hII).comp z)),
      I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub ((planeFamily II hII).cusp _).form I ∧ 0 < (planeFamily II hII).Nz z I :=
  ⟨planeLine, planeLine_ne_bot, planeLine_saturated, planeLine_isIso, planeCusp_Nz_pos II hII z⟩

end Line

end GroundTheory.Heights₂.Heights.NineStatements
