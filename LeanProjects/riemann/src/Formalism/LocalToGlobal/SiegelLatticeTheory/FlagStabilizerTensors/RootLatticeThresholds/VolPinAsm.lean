import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CovolIdx
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DiagMulOfBt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexFiniteNonzero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexAStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPinG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp

noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.VolPinAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def StG (w : Point D.host.E (D.R.rS + 1)) : Subgroup (Formalism.L2.SG.PairVal.GLR D) where
  carrier := Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w)
  one_mem' := (Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed D.host.E _ (ptMat w)).1
  mul_mem' := fun {a b} ha hb => (Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed D.host.E _ (ptMat w)).2.1 a ha b hb
  inv_mem' := fun {a} ha => (Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed D.host.E _ (ptMat w)).2.2 a ha

def bOf (w : Point D.host.E (D.R.rS + 1)) (β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D :=
  (ptMat w)⁻¹ * ((β⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w

variable {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

def phiV (X : HidaSetting D) (v : InfinitePlace X.B.I.F) : D.host.E →+* ℂ :=
  (X.B.I.φ v).comp (X.ιE.symm : D.host.E →+* X.B.I.E)

def DictProps (t : TT Y u u') (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : Formalism.L2.SG.PairVal.MatR D)
    (γw s c : X.B.I.Ginf) (Φ : StG w →* X.B.I.Ginf) : Prop :=
  Function.Injective Φ ∧ (∀ β, c⁻¹ * Φ β * c ∈ Formalism.L2.SG.TermOp.Vanish.Rset t) ∧
  (∀ y, (∃ β : StG w, (β : Formalism.L2.SG.PairVal.GLR D) ∈
      Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L ∧ Φ β = y) ↔
    ∃ r ∈ Formalism.L2.SG.TermOp.ROinf t, y = c * r * c⁻¹) ∧
  ∃ σ : Formalism.L2.SG.RealObj.FreeE w → ℂ, (∀ p, ‖σ p‖ = (D.host.rdE : ℝ) ^ (p.1.2.val - p.1.1.val)) ∧
    ∃ A : InfinitePlace X.B.I.F → (Formalism.L2.SG.RealObj.FreeE w → ℂ) →ₗ[ℂ] (Formalism.L2.SG.RealObj.FreeE w → ℂ),
      (∀ v x x' p, (∀ q : Formalism.L2.SG.RealObj.FreeE w, q.1.2.val - q.1.1.val < p.1.2.val - p.1.1.val → x q = x' q) →
        A v x p - x p = A v x' p - x' p) ∧
      ∀ (β : StG w) v, Formalism.L2.SG.RealObj.stCoord X u' w γw (s⁻¹ * (c⁻¹ * Φ β * c) * s) v =
        A v (fun p => σ p * phiV X v (((ptMat w)⁻¹ * ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) *
          ptMat w) p.1.1 p.1.2))

def DictC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w → ∀ (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U → ∀ (γw s s' : X.B.I.Ginf),
      Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t.pt.1 = s * γw * s'⁻¹ →
      ∃ (c : X.B.I.Ginf) (Φ : StG w →* X.B.I.Ginf), DictProps t w F' L γw s c Φ

def CovolOneC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w → ∀ (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U → ∀ (γw s s' : X.B.I.Ginf) (μw : Measure X.B.I.Ginf),
      Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t.pt.1 = s * γw * s'⁻¹ →
      IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw →
      μw.map (Formalism.L2.SG.RealObj.stCoord X u' w γw) = Formalism.L2.SG.RealObj.muStab X w →
      ∀ (c : X.B.I.Ginf) (Φ : StG w →* X.B.I.Ginf), DictProps t w F' L γw s c Φ →
      ∃ KA : Set X.B.I.Ginf, MeasurableSet KA ∧
        (∀ y, c⁻¹ * y * c ∈ Formalism.L2.SG.TermOp.Vanish.Rset t → ∃! x, x ∈
          ((Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w).subgroupOf (StG w)).map Φ ∧ x * y ∈ KA) ∧
        ((μw.map (fun y => s * y * s⁻¹)).map (fun y => c * y * c⁻¹)) KA = 1

def CovolOne3C : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ i, 3 ≤ D.host.g i) → PrimeHyp D u (Tu D u') →
    ∀ (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w → ∀ (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U → ∀ (γw s s' : X.B.I.Ginf) (μw : Measure X.B.I.Ginf),
      Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t.pt.1 = s * γw * s'⁻¹ →
      IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw →
      μw.map (Formalism.L2.SG.RealObj.stCoord X u' w γw) = Formalism.L2.SG.RealObj.muStab X w →
      ∀ (c : X.B.I.Ginf) (Φ : StG w →* X.B.I.Ginf), DictProps t w F' L γw s c Φ →
      ∃ KA : Set X.B.I.Ginf, MeasurableSet KA ∧
        (∀ y, c⁻¹ * y * c ∈ Formalism.L2.SG.TermOp.Vanish.Rset t → ∃! x, x ∈
          ((Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w).subgroupOf (StG w)).map Φ ∧ x * y ∈ KA) ∧
        ((μw.map (fun y => s * y * s⁻¹)).map (fun y => c * y * c⁻¹)) KA = 1

section Assembly

instance countable_hostE (D : D7) : Countable D.host.E := by
  let b := Module.finBasis ℚ D.host.E
  exact Function.Injective.countable b.equivFun.injective

instance countable_GLR (D : D7) : Countable (Formalism.L2.SG.PairVal.GLR D) :=
  Function.Injective.countable
    (f := fun g : Formalism.L2.SG.PairVal.GLR D => fun i j => (g : Formalism.L2.SG.PairVal.MatR D) i j)
    (fun a b h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))

private theorem isHaarOnSet_conj {I : Formalism.MainNotions.S.AutInst} {S : Set I.Ginf} {μ : Measure I.Ginf}
    (h : IsHaarOnSet I S μ) (c : I.Ginf) :
    IsHaarOnSet I {y | c⁻¹ * y * c ∈ S} (μ.map (fun y => c * y * c⁻¹)) := by
  obtain ⟨hσ, h0, hS, hinv⟩ := h
  have hm : Measurable (fun y : I.Ginf => c * y * c⁻¹) := (measurable_const_mul c).mul_const c⁻¹
  let e : I.Ginf ≃ᵐ I.Ginf := (MeasurableEquiv.mulLeft c).trans (MeasurableEquiv.mulRight c⁻¹)
  have he : (fun y : I.Ginf => c * y * c⁻¹) = ⇑e := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI := hσ
    rw [he]
    exact e.sigmaFinite_map
  · intro h'
    exact h0 ((Measure.map_eq_zero_iff hm.aemeasurable).mp h')
  · rw [he, e.map_apply]
    convert hS using 2
    ext y
    simp [e, mul_assoc]
  · intro s hs
    rw [Measure.map_map (measurable_const_mul s) hm]
    have hc : (fun x => s * x) ∘ (fun y : I.Ginf => c * y * c⁻¹) =
        (fun y : I.Ginf => c * y * c⁻¹) ∘ (fun x => (c⁻¹ * s * c) * x) := by
      funext y
      simp only [Function.comp]
      group
    rw [hc, ← Measure.map_map hm (measurable_const_mul _), hinv _ hs]

theorem pinned_haar (t : TT Y u u') (w : Point D.host.E (D.R.rS + 1)) (γw s s' : X.B.I.Ginf) (μw : Measure X.B.I.Ginf)
    (hs : s ∈ X.SinfU u) (hs' : s' ∈ X.SinfU u') (hdec : t.pt.1 = s * γw * s'⁻¹)
    (hμw : IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw) :
    IsHaarOnSet X.B.I (Formalism.L2.SG.TermOp.Vanish.Rset t) (μw.map (fun y => s * y * s⁻¹)) := by
  have hset : Formalism.L2.SG.TermOp.Vanish.Rset t = {y | s⁻¹ * y * s ∈ Formalism.L2.SG.RealObj.StInf X u u' γw} := by
    ext y
    have e1 : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
    have e2 : t.pt.1⁻¹ * y * t.pt.1 = s' * (γw⁻¹ * (s⁻¹ * y * s) * γw) * s'⁻¹ := by rw [hdec]; group
    have h1 := Formalism.L2.SG.Pf.FormTranspose.sinf_conj_iff (X := X) u hs (s⁻¹ * y * s)
    have h2 := Formalism.L2.SG.Pf.FormTranspose.sinf_conj_iff (X := X) u' hs' (γw⁻¹ * (s⁻¹ * y * s) * γw)
    rw [e1] at h1
    show (y ∈ X.NinfU u ∧ t.pt.1⁻¹ * y * t.pt.1 ∈ X.NinfU u') ↔
      (s⁻¹ * y * s ∈ X.NinfU u ∧ γw⁻¹ * (s⁻¹ * y * s) * γw ∈ X.NinfU u')
    rw [e2, h1, h2]
  rw [hset]
  exact isHaarOnSet_conj hμw s

theorem rset_mul (t : TT Y u u') {a b : X.B.I.Ginf} (ha : a ∈ Formalism.L2.SG.TermOp.Vanish.Rset t)
    (hb : b ∈ Formalism.L2.SG.TermOp.Vanish.Rset t) : a * b ∈ Formalism.L2.SG.TermOp.Vanish.Rset t := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  show a * b ∈ X.NinfU u ∧ t.pt.1⁻¹ * (a * b) * t.pt.1 ∈ X.NinfU u'
  refine ⟨Formalism.L2.SG.Pf.FormTranspose.ninf_mul (X := X) u ha1 hb1, ?_⟩
  have e : t.pt.1⁻¹ * (a * b) * t.pt.1 = (t.pt.1⁻¹ * a * t.pt.1) * (t.pt.1⁻¹ * b * t.pt.1) := by group
  rw [e]
  exact Formalism.L2.SG.Pf.FormTranspose.ninf_mul (X := X) u' ha2 hb2

theorem gval_of_normRep (t : TT Y u u') (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hN : Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U) (hG : t.G ≠ 0) : Gval (lf D (X.Fu u)) F' ≠ 0 := by
  obtain ⟨⟨h, hmk⟩, -⟩ := hN
  have hGF := PI.TermAttrConst.UnitaryGroupMassFormula.termGFun_holds D u u' (X.Fu u) t.toTerm.lam ((Y.rowsOK u).1 t.lam t.mem)
  have e : t.G = Gval (lf D (X.Fu u)) F' := by
    show Formalism.L2.SG.TermDef.Gt _ _ _ t.toTerm.cls = _
    rw [← hmk]
    first
    | exact Formalism.L2.SG.TermDef.Gt_mk _ _ _ hGF _
    | exact Formalism.L2.SG.TermDef.Gt_mk hGF _
  rw [e] at hG
  exact hG

private theorem relIndex_map_of_injective' {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (H K : Subgroup G) : (H.map f).relIndex (K.map f) = H.relIndex K := by
  first
  | exact Subgroup.relIndex_map_map_of_injective f hf
  | exact Subgroup.relIndex_map_map_of_injective hf
  | exact Subgroup.relIndex_map_map_of_injective H K hf
  | (rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective hf])
  | exact Subgroup.relindex_map_map_of_injective f hf

private theorem H_affine_combination_eq_of_quadratic_relation (t : TT Y u u') (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : Formalism.L2.SG.PairVal.MatR D)
    (γw s c : X.B.I.Ginf) (Φ : StG w →* X.B.I.Ginf) (hDict : DictProps t w F' L γw s c Φ)
    (μR : Measure X.B.I.Ginf) (hH : IsHaarOnSet X.B.I (Formalism.L2.SG.TermOp.Vanish.Rset t) μR)
    (KA : Set X.B.I.Ginf) (hKA : MeasurableSet KA)
    (hKAu : ∀ y, c⁻¹ * y * c ∈ Formalism.L2.SG.TermOp.Vanish.Rset t → ∃! x, x ∈
      ((Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w).subgroupOf (StG w)).map Φ ∧ x * y ∈ KA)
    (hKA1 : (μR.map (fun y => c * y * c⁻¹)) KA = 1)
    (K : Set X.B.I.Ginf) (hK : MeasurableSet K)
    (hKu : ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ Formalism.L2.SG.TermOp.ROinf t ∧ s * r ∈ K)
    (hAut : Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L ≤ StG w)
    (hInt : Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w ≤ StG w)
    (hf1 : (Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L).relIndex
      (Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w) ≠ 0)
    (hf2 : (Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w).relIndex
      (Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L) ≠ 0) :
    (μR K).toReal = Formalism.L2.SG.PairVal.volIdx D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm w F' L := by
  classical
  set Rs := Formalism.L2.SG.TermOp.Vanish.Rset t with hRs
  set R' : Set X.B.I.Ginf := {y | c⁻¹ * y * c ∈ Rs} with hR'
  set A := ((Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w).subgroupOf (StG w)).map Φ with hA
  set B := ((Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L).subgroupOf
    (StG w)).map Φ with hB
  obtain ⟨-, -, hc0, hinv⟩ := isHaarOnSet_conj hH c
  have hAsub : ∀ x ∈ A, x ∈ R' := by
    intro x hx
    obtain ⟨β, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hDict.2.1 β
  have hBsub : ∀ x ∈ B, x ∈ R' := by
    intro x hx
    obtain ⟨β, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hDict.2.1 β
  have hmulR : ∀ x ∈ R', ∀ r ∈ R', x * r ∈ R' := by
    intro x hx r hr
    have h2 := rset_mul t hx hr
    show c⁻¹ * (x * r) * c ∈ Rs
    have e : c⁻¹ * (x * r) * c = (c⁻¹ * x * c) * (c⁻¹ * r * c) := by group
    rw [e]
    exact h2
  haveI : Countable A := Set.Countable.to_subtype (s := (A : Set X.B.I.Ginf))
    (by rw [hA, Subgroup.coe_map]; exact (Set.to_countable _).image _)
  haveI : Countable B := Set.Countable.to_subtype (s := (B : Set X.B.I.Ginf))
    (by rw [hB, Subgroup.coe_map]; exact (Set.to_countable _).image _)
  set KB : Set X.B.I.Ginf := {y | c⁻¹ * y * c ∈ K} with hKBdef
  have hKB : MeasurableSet KB := hK.preimage ((measurable_const_mul c⁻¹).mul_const c)
  have hKBu : ∀ r ∈ R', ∃! x, x ∈ B ∧ x * r ∈ KB := by
    intro r hr
    obtain ⟨s0, ⟨hs0, hs0K⟩, huniq⟩ := hKu _ hr
    refine ⟨c * s0 * c⁻¹, ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨β, hβ, hβe⟩ := (hDict.2.2.1 (c * s0 * c⁻¹)).mpr ⟨s0, hs0, rfl⟩
      exact Subgroup.mem_map.mpr ⟨β, Subgroup.mem_subgroupOf.mpr hβ, hβe⟩
    · show c⁻¹ * (c * s0 * c⁻¹ * r) * c ∈ K
      have e : c⁻¹ * (c * s0 * c⁻¹ * r) * c = s0 * (c⁻¹ * r * c) := by group
      rw [e]
      exact hs0K
    · rintro x ⟨hx, hxK⟩
      obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨r1, hr1, hr1e⟩ := (hDict.2.2.1 (Φ β)).mp ⟨β, Subgroup.mem_subgroupOf.mp hβ, rfl⟩
      have hr1s : r1 = s0 := by
        refine huniq r1 ⟨hr1, ?_⟩
        have e : r1 * (c⁻¹ * r * c) = c⁻¹ * (Φ β * r) * c := by rw [hr1e]; group
        rw [e]
        exact hxK
      rw [hr1e, hr1s]
  have hBA : B.relIndex A = (Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L).relIndex
      (Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w) := by
    rw [hA, hB, relIndex_map_of_injective' Φ hDict.1, Subgroup.relIndex_subgroupOf hInt]
  have hAB : A.relIndex B = (Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w).relIndex
      (Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L) := by
    rw [hA, hB, relIndex_map_of_injective' Φ hDict.1, Subgroup.relIndex_subgroupOf hAut]
  have hcomm := Formalism.L2.SG.Pf.CovolIdx.covol_commens (μR.map (fun y => c * y * c⁻¹)) R' hc0 A B
    (fun s hs => hinv s (hAsub s hs)) (fun s hs => hinv s (hBsub s hs))
    (fun s hs r hr => hmulR s (hAsub s hs) r hr) (fun s hs r hr => hmulR s (hBsub s hs) r hr)
    KA KB hKA hKB (fun r hr => hKAu r hr) hKBu (by rw [hBA]; exact hf1) (by rw [hAB]; exact hf2)
  have hνKB : (μR.map (fun y => c * y * c⁻¹)) KB = μR K := by
    rw [Measure.map_apply ((measurable_const_mul c).mul_const c⁻¹) hKB]
    congr 1
    ext y
    simp only [hKBdef, Set.mem_preimage, Set.mem_setOf_eq]
    have e : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    rw [e]
  rw [hKA1, hνKB, one_mul, hBA, hAB] at hcomm
  have h2 := congrArg ENNReal.toReal hcomm
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at h2
  unfold Formalism.L2.SG.PairVal.volIdx
  rw [eq_div_iff (by exact_mod_cast hf2)]
  exact h2.symm

theorem volPinGC_of (hD : DictC) (hC : CovolOneC)
    (hBin : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PrimeHyp D u (Tu D u') →
      ∀ (t : TT Y u u') (w : Point D.host.E (D.R.rS + 1)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
        (L U : Formalism.L2.SG.PairVal.MatR D), t.relevant → t.toTerm.generic →
        Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U → Gval (lf D (X.Fu u)) F' ≠ 0 →
        (Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L : Set (Formalism.L2.SG.PairVal.GLR D)) ⊆
          Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w))
    (hFin : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PrimeHyp D u (Tu D u') →
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.VolumeIndexFiniteNonzero D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) :
    Formalism.L2.SG.VolPin.VolPinGC := by
  intro D X Y u u' hP t hrel hgen hG w hw μR hpin K hK hKu F' L U hN
  obtain ⟨γw, s, s', μw, hpt, hs, hs', hdec, hμw, hmap, rfl⟩ := hpin
  obtain ⟨c, Φ, hDict⟩ := hD D X Y u u' t hrel hG w hw F' L U hN γw s s' hpt hs hs' hdec
  obtain ⟨KA, hKA, hKAu, hKA1⟩ :=
    hC D X Y u u' t hrel hG w hw F' L U hN γw s s' μw hpt hs hs' hdec hμw hmap c Φ hDict
  have hGv := gval_of_normRep t w F' L U hN hG
  have hAut : Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L ≤ StG w :=
    fun a ha => hBin D X Y u u' hP t w F' L U hrel hgen hN hGv ha
  have hInt : Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w ≤ StG w := by
    unfold Formalism.L2.SG.PairVal.stabInt
    refine (Subgroup.closure_le _).mpr ?_
    intro a ha
    obtain ⟨h1, b, hb, hwb, -⟩ := ha
    show a ∈ Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w)
    exact ⟨h1, b, hb, hwb⟩
  obtain ⟨hf1, hf2⟩ := hFin D X Y u u' hP Y.agree t.toTerm w F' L U hrel hgen hN hGv
  exact H_affine_combination_eq_of_quadratic_relation t w F' L γw s c Φ hDict _ (pinned_haar t w γw s s' μw hs hs' hdec hμw) KA hKA hKAu hKA1
    K hK hKu hAut hInt hf1 hf2

theorem volume_generic_odd_of (hD : DictC) (hC : CovolOne3C)
    (hBin : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PrimeHyp D u (Tu D u') →
      ∀ (t : TT Y u u') (w : Point D.host.E (D.R.rS + 1)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
        (L U : Formalism.L2.SG.PairVal.MatR D), t.relevant → t.toTerm.generic →
        Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U → Gval (lf D (X.Fu u)) F' ≠ 0 →
        (Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L : Set (Formalism.L2.SG.PairVal.GLR D)) ⊆
          Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w))
    (hFin : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PrimeHyp D u (Tu D u') →
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.VolumeIndexFiniteNonzero D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) :
    Formalism.L2.SG.VolPin.VolumeOddGeneric := by
  intro D X Y u u' h3 hP t hrel hgen hG w hw μR hpin K hK hKu F' L U hN
  obtain ⟨γw, s, s', μw, hpt, hs, hs', hdec, hμw, hmap, rfl⟩ := hpin
  obtain ⟨c, Φ, hDict⟩ := hD D X Y u u' t hrel hG w hw F' L U hN γw s s' hpt hs hs' hdec
  obtain ⟨KA, hKA, hKAu, hKA1⟩ :=
    hC D X Y u u' h3 hP t hrel hG w hw F' L U hN γw s s' μw hpt hs hs' hdec hμw hmap c Φ hDict
  have hGv := gval_of_normRep t w F' L U hN hG
  have hAut : Formalism.L2.SG.PairVal.stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L ≤ StG w :=
    fun a ha => hBin D X Y u u' hP t w F' L U hrel hgen hN hGv ha
  have hInt : Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w ≤ StG w := by
    unfold Formalism.L2.SG.PairVal.stabInt
    refine (Subgroup.closure_le _).mpr ?_
    intro a ha
    obtain ⟨h1, b, hb, hwb, -⟩ := ha
    show a ∈ Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w)
    exact ⟨h1, b, hb, hwb⟩
  obtain ⟨hf1, hf2⟩ := hFin D X Y u u' hP Y.agree t.toTerm w F' L U hrel hgen hN hGv
  exact H_affine_combination_eq_of_quadratic_relation t w F' L γw s c Φ hDict _ (pinned_haar t w γw s s' μw hs hs' hdec hμw) KA hKA hKAu hKA1
    K hK hKu hAut hInt hf1 hf2

end Assembly

end Formalism.L2.SG.Pf.VolPinAsm
