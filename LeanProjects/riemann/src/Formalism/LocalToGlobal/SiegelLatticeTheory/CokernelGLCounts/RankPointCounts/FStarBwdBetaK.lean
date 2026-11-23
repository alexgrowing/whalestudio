import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaT
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfJ

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open BwdCut BwdBetaCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdBetaCut

variable (u u' F0 what₂) in

def BHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  CtxP u u' F0 what₂ ∧ Ctx γ Z ∧ StarHyp Zd γ Z F'₂ φ φ' ∧ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ' ∧
    (∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) ∧
    TermHyp (F0 := F0) Λ₂ F'₂ ∧ PD D γ.lam (lf D F0) u' (repF γ) ∧ Gval (lf D F0) (repF γ) ≠ 0

def OmB {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {T' : D.host.E} (F' F₂ : LFlag (VS D) D.R.rS T')
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  star (GDl (frame F) (frame F₂) (D.R.rS + 1)) • β (Gom (frame F) (frame F')) -
      star (GDl (frame F) (frame F') (D.R.rS + 1)) • Gom (frame F) (frame F₂) ∈ Xsp F₂

end BwdBetaCut

variable (u u' F0 what₂)

def BetaRat : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∃ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) ∧
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ ∧ OmB (lf D F0) (repF γ) (liftF F'₂) β₀

def ScalarOf : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β : (VS D).V ≃ₗ[D.host.E] (VS D).V, β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β (frame (repF γ) b) = frame (liftF F'₂) b) → OmB (lf D F0) (repF γ) (liftF F'₂) β →
      Scalar₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β

def BetaInt : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∃ v : (VS D).V ≃ₗ[D.host.E] (VS D).V, v ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
        (∀ b, v (frame (liftF F'₂) b) = frame (liftF F'₂) b) ∧
        (∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), v y - y ∈ Xsp (liftF F'₂)) ∧
        Formalism.HermitianLatticesTheory.gmap (v * β₀) γ.lam = Λ₂ ∧ IotaC₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) (v * β₀)

variable {u u' F0 what₂}

namespace BwdBetaCut

variable {T T' : D.host.E}

theorem fvec_cs' (F : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) : frame F i.castSucc = F.fl.e i := by
  first
  | exact PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc F.fl i
  | simp [frame]
  | rfl

theorem fvec_last' (F : LFlag (VS D) D.R.rS T) : frame F (Fin.last _) = F.fl.z := by
  first
  | exact PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_last F.fl
  | simp [frame]
  | rfl

theorem e_of_frame (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F F₂ : LFlag (VS D) D.R.rS T')
    (h : ∀ b, β (frame F b) = frame F₂ b) (i : Fin D.R.rS) : β (F.fl.e i) = F₂.fl.e i := by
  have hi := h i.castSucc
  rwa [fvec_cs', fvec_cs'] at hi

theorem Xflag_of_frame (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F F₂ : LFlag (VS D) D.R.rS T')
    (h : ∀ b, β (frame F b) = frame F₂ b) (j : ℕ) :
    (Xflag F j).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag F₂ j := by
  ext x
  rw [Submodule.mem_map_equiv]
  exact (Formalism.L2.SG.Pf.mem_xflag_of_frame (fun a => (h a).symm) j x).symm

theorem Xsp_of_frame (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F F₂ : LFlag (VS D) D.R.rS T')
    (h : ∀ b, β (frame F b) = frame F₂ b) :
    (Xsp F).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F₂ := by
  rw [← Formalism.L2.SG.FourParts.Xflag_r, ← Formalism.L2.SG.FourParts.Xflag_r]
  exact Xflag_of_frame β F F₂ h D.R.rS

theorem Gom_orth (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Gom (frame F) (frame F') ∈ orth (VS D) (Xsp F') := by
  unfold orth Xsp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  unfold Formalism.MainNotions.S.FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [← fvec_cs' F' i, PI.NRL.herm_eq, Formalism.L2.SG.Pf.ScalarFramePf.om_pair,
      if_neg (Fin.castSucc_lt_last i).ne, star_zero]
  | zero => simp
  | add y z _ _ hy hz => simp [map_add, hy, hz]
  | smul a y _ hy => simp [hy]

end BwdBetaCut

namespace BwdBetaCut

theorem comb_mem {V : Type*} [AddCommGroup V] [Module D.host.E V] {X : Submodule D.host.E V}
    (v : V ≃ₗ[D.host.E] V) (a c : D.host.E) (p q : V) (h : a • p - c • q ∈ X) (hvX : ∀ y ∈ X, v y ∈ X)
    (hq : v q - q ∈ X) : a • v p - c • q ∈ X := by
  have h1 := hvX _ h
  rw [map_sub, map_smul, map_smul] at h1
  have h2 := X.add_mem h1 (X.smul_mem c hq)
  convert h2 using 1
  rw [smul_sub]
  abel

private theorem Hp_le_orth_Xsp (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ)
    {T₁ T₂ : D.host.E} (F : LFlag (VS D) D.R.rS T₁) (F' : LFlag (VS D) D.R.rS T₂) :
    Hp Λ F F' ≤ orth (VS D) (Xsp F') := by
  have hle : XLam Λ F' ≤ UU Λ F F' := by
    unfold UU
    exact le_sup_right.trans le_sup_left
  have hX : Xsp F' ≤ spanE (VS D) (UU Λ F F') := by
    refine le_trans ?_ (Submodule.span_mono (SetLike.coe_subset_coe.mpr hle))
    intro x hx
    have hxs : x ∈ Submodule.span D.host.E (Λ : Set (VS D).V) := by
      rw [hΛ.span_eq_top]
      exact Submodule.mem_top
    obtain ⟨d, hd0, hd⟩ := Formalism.MainNotions.LatticeGluingRadicals.m_exists_smul_mem Λ hxs
    have hdx : (algebraMap (𝓞 D.host.E) D.host.E d) • x ∈ Xsp F' := (Xsp F').smul_mem _ hx
    rw [algebraMap_smul] at hdx
    have hdX : d • x ∈ XLam Λ F' := by
      unfold XLam
      exact Submodule.mem_inf.mpr ⟨hd, by unfold toO; first | exact hdx | simpa using hdx⟩
    have hd' : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 := by
      first
      | exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).mpr hd0
      | simpa using hd0
    have hx' : x = (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul D.host.E d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hdX)
  unfold Hp UUE
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
  intro x hx
  exact hy x (hX hx)

theorem h_le_orth_second_frame (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ) {T' : D.host.E}
    (F' : LFlag (VS D) D.R.rS T') (hL : IsLift Λ (lf D F0)) (hL' : IsLift Λ F') :
    Hp Λ (lf D F0) F' ≤ orth (VS D) (Xsp F') := by
  exact Hp_le_orth_Xsp Λ hΛ _ F'

end BwdBetaCut

theorem betaCore₂_of (h1 : BetaRat Zd u u' F0 what₂) (h2 : ScalarOf Zd u u' F0 what₂) (h3 : BetaInt Zd u u' F0 what₂) :
    BetaCore₂ Zd u u' F0 what₂ := by
  unfold BetaRat at h1
  unfold ScalarOf at h2
  unfold BetaInt at h3
  unfold BetaCore₂
  intro hP γ Z hC F'₂ φ φ' hS Λ₂ hG hn hT hPD hv0
  have hB : BwdBetaCut.BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ := by
    unfold BwdBetaCut.BHyp
    exact ⟨hP, hC, hS, hG, hn, hT, hPD, hv0⟩
  obtain ⟨β₀, hi₀, hf₀, hW₀, hO₀⟩ := h1 γ Z F'₂ φ φ' Λ₂ hB
  obtain ⟨v, hiv, hfv, hov, hgm, hio⟩ := h3 γ Z F'₂ φ φ' Λ₂ hB β₀ hi₀ hf₀ hW₀ hO₀
  have hfr : ∀ b, (v * β₀) (frame (repF γ) b) = frame (liftF F'₂) b := by
    intro b
    rw [LinearEquiv.mul_apply, hf₀, hfv]
  have hXv : ∀ y ∈ Xsp (liftF F'₂), v y ∈ Xsp (liftF F'₂) := by
    intro y hy
    rw [← BwdBetaCut.Xsp_of_frame v (liftF F'₂) (liftF F'₂) hfv]
    exact Submodule.mem_map_of_mem hy
  have hO : BwdBetaCut.OmB (lf D F0) (repF γ) (liftF F'₂) (v * β₀) := by
    unfold BwdBetaCut.OmB at hO₀ ⊢
    rw [LinearEquiv.mul_apply]
    exact BwdBetaCut.comb_mem v _ _ _ _ hO₀ hXv (hov _ (BwdBetaCut.Gom_orth _ _))
  have hi : v * β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hiv hi₀
  have hW : BwdBetaCut.W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) (v * β₀) := by
    unfold BwdBetaCut.W0₂ at hW₀ ⊢
    intro w hw
    obtain ⟨w₂, hw₂, hd1, hd2⟩ := hW₀ w hw
    refine ⟨w₂, hw₂, hd1, ?_⟩
    have hw₂o := BwdBetaCut.Hp_le_orth_Xsp Λ₂ hG.1 _ _ hw₂
    have hs := (Xsp (liftF F'₂)).add_mem (hXv _ hd2) (hov _ hw₂o)
    rw [LinearEquiv.mul_apply]
    convert hs using 1
    rw [map_sub]
    abel
  refine ⟨v * β₀, ?_⟩
  unfold BwdBetaCut.IsPair₂
  refine ⟨hi, hgm, fun j => BwdBetaCut.Xflag_of_frame _ _ _ hfr j, ?_, hio, hW,
    h2 γ Z F'₂ φ φ' Λ₂ hB _ hi hfr hO⟩
  rw [← BwdBetaCut.fvec_last' (repF γ), ← BwdBetaCut.fvec_last' (liftF F'₂)]
  exact hfr _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
