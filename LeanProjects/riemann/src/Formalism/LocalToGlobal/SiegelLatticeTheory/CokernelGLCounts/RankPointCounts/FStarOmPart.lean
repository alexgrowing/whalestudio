import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFwd

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace OmP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def OmV {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (v : S.V) : Prop :=
  v ∈ Submodule.span E (Set.range F'.fvec) ∧ ∀ a, S.hT (F.fvec a) v = if a = Fin.last r then 1 else 0

theorem fvec_cs {T : E} (F : FlagG S r T) (i : Fin r) : F.fvec i.castSucc = F.e i := by
  simp [FlagG.fvec]

theorem fvec_last {T : E} (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem hT_comb {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E) (a : Fin (r + 1)) :
    S.hT (F.fvec a) (∑ b, c b • F'.fvec b) = (Zhat F F' *ᵥ c) a := by
  rw [map_sum]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

theorem eq_zero_of_orth {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0)
    {d : S.V} (hd : d ∈ Submodule.span E (Set.range F'.fvec)) (h : ∀ a, S.hT (F.fvec a) d = 0) : d = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hd
  have hc : Zhat F F' *ᵥ c = 0 := funext fun a => by rw [← hT_comb]; exact h a
  rw [Matrix.eq_zero_of_mulVec_eq_zero hdet hc]
  simp

theorem exists_om {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) :
    ∃ v, OmV F F' v := by
  set c : Fin (r + 1) → E := (Zhat F F')⁻¹ *ᵥ Pi.single (Fin.last r) 1 with hc
  refine ⟨∑ b, c b • F'.fvec b, (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩, fun a => ?_⟩
  rw [hT_comb, hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  by_cases ha : a = Fin.last r
  · subst ha; simp
  · simp [ha]

theorem om_unique {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) {v w : S.V}
    (hv : OmV F F' v) (hw : OmV F F' w) : v = w := by
  have := eq_zero_of_orth F F' hdet (Submodule.sub_mem _ hv.1 hw.1) fun a => by
    rw [map_sub, hv.2, hw.2, sub_self]
  exact sub_eq_zero.1 this

theorem comb_eq {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) {Ω : S.V}
    (hΩ : OmV F F' Ω) (c : Fin (r + 1) → E) (hc : ∀ i : Fin r, S.hT (F.e i) (∑ b, c b • F'.fvec b) = 0) :
    ∑ b, c b • F'.fvec b = S.hT F.z (∑ b, c b • F'.fvec b) • Ω := by
  set v := ∑ b, c b • F'.fvec b with hv
  have hvs : v ∈ Submodule.span E (Set.range F'.fvec) := (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩
  have := eq_zero_of_orth F F' hdet (Submodule.sub_mem _ hvs (Submodule.smul_mem _ (S.hT F.z v) hΩ.1))
    fun a => by
      rw [map_sub, map_smul, hΩ.2, smul_eq_mul]
      refine Fin.lastCases ?_ (fun i => ?_) a
      · rw [fvec_last]; simp
      · rw [fvec_cs, hc i]; simp [Fin.castSucc_ne_last]
  exact sub_eq_zero.1 this

end OmP

open OmP

section Cls

variable {D : Formalism.BasicNotions.D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem omCls_of_om {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F'₂ F' : LFlag (VS D) D.R.rS T')
    (hZ : ZhatL (lf D F0) F'₂ = ZhatL (lf D F0) F') (hdet : (ZhatL (lf D F0) F'₂).det ≠ 0) {Ω₂ Ω' : (VS D).V}
    (h₂ : OmV F0 F'₂.fl Ω₂) (h' : OmV F0 F'.fl Ω') (hX : Ω' - Ω₂ ∈ Xsp (lf D F0)) : OmCls F0 F'₂ F' := by
  intro c hc
  have hZ' : Zhat F0 F'₂.fl = Zhat F0 F'.fl := hZ
  have hdet₂ : (Zhat F0 F'₂.fl).det ≠ 0 := hdet
  have hdet' : (Zhat F0 F'.fl).det ≠ 0 := by rw [← hZ']; exact hdet
  have hc₂ : ∀ i, (VS D).hT (F0.e i) (∑ b, c b • F'₂.fl.fvec b) = 0 := hc
  have hc' : ∀ i, (VS D).hT (F0.e i) (∑ b, c b • F'.fl.fvec b) = 0 := by
    intro i
    rw [← fvec_cs, hT_comb, ← hZ', ← hT_comb, fvec_cs]
    exact hc₂ i
  have hμ : (VS D).hT F0.z (∑ b, c b • F'.fl.fvec b) = (VS D).hT F0.z (∑ b, c b • F'₂.fl.fvec b) := by
    rw [← fvec_last, hT_comb, hT_comb, hZ']
  have e₂ := comb_eq F0 F'₂.fl hdet₂ h₂ c hc₂
  have e' := comb_eq F0 F'.fl hdet' h' c hc'
  have hs : ∑ b, c b • (frame F' b - frame F'₂ b) =
      ∑ b, c b • F'.fl.fvec b - ∑ b, c b • F'₂.fl.fvec b := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => smul_sub _ _ _
  rw [hs, e', e₂, hμ, ← smul_sub]
  exact Submodule.smul_mem _ _ hX

end Cls

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def OmDet : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → ∀ F', IsPartner γ Z F' →
        (ZhatL (lf D F0) (repF γ)).det ≠ 0 ∧ Matrix.det Z ≠ 0

def OmLoc : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → (ZhatL (lf D F0) (repF γ)).det ≠ 0 → Matrix.det Z ≠ 0 → ∀ Ω₂ Ωγ : (VS D).V, OmV F0 F'₂.fl Ω₂ → OmV F0 (repF γ).fl Ωγ →
        Ω₂ - Ωγ ∈ Xsp (lf D F0)

def OmRep : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    (ZhatL (lf D F0) (repF γ)).det ≠ 0 → Matrix.det Z ≠ 0 →
    ∀ F', IsPartner γ Z F' → ∀ Ω' Ωγ : (VS D).V, OmV F0 F'.fl Ω' → OmV F0 (repF γ).fl Ωγ →
      Ω' - Ωγ ∈ Xsp (lf D F0)

variable {u u' F0 what₂}

theorem omPart_of (h0 : OmDet Zd u u' F0 what₂) (h1 : OmLoc Zd u u' F0 what₂) (h2 : OmRep u u' F0 what₂) :
    OmPart Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'₂ φ φ' hS F' hP
  obtain ⟨hdγ, hdZ⟩ := h0 hrows γ Z hC F'₂ φ φ' hS F' hP
  have hZ₂ : ZhatL (lf D F0) F'₂ = Z := hS.1
  have hZ' : ZhatL (lf D F0) F' = Z := hP.1.2.2.2.2
  have hd₂ : (ZhatL (lf D F0) F'₂).det ≠ 0 := by rw [hZ₂]; exact hdZ
  have hd' : (ZhatL (lf D F0) F').det ≠ 0 := by rw [hZ']; exact hdZ
  obtain ⟨Ωγ, hγ⟩ := exists_om F0 (repF γ).fl hdγ
  obtain ⟨Ω₂, h₂⟩ := exists_om F0 F'₂.fl hd₂
  obtain ⟨Ω', h'⟩ := exists_om F0 F'.fl hd'
  have e1 := h1 hrows γ Z hC F'₂ φ φ' hS hdγ hdZ Ω₂ Ωγ h₂ hγ
  have e2 := h2 hrows γ Z hC hdγ hdZ F' hP Ω' Ωγ h' hγ
  refine omCls_of_om F0 F'₂ F' (hZ₂.trans hZ'.symm) hd₂ h₂ h' ?_
  have : Ω' - Ω₂ = (Ω' - Ωγ) - (Ω₂ - Ωγ) := by abel
  rw [this]
  exact Submodule.sub_mem _ e2 e1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
