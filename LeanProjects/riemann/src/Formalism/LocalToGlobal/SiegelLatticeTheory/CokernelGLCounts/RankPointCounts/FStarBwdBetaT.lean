import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBeta
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace BwdBetaCut

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T T' : E}

theorem map_inf_equiv (A B : Submodule E S.V) :
    (A ⊓ B).map (β : S.V →ₗ[E] S.V) = A.map (β : S.V →ₗ[E] S.V) ⊓ B.map (β : S.V →ₗ[E] S.V) := by
  ext v
  simp only [Submodule.mem_inf, Submodule.mem_map_equiv]

theorem Xplus_mapL (F : LFlag S r T) : Xplus (mapL β hβ F) = (Xplus F).map (β : S.V →ₗ[E] S.V) := by
  simp only [Xplus, FlagG.Xplus]
  rw [Submodule.map_sup, ← Formalism.L2.SG.Pf.X_mapFlag β hβ, Submodule.map_span, Set.image_singleton]
  rfl

include hβ in
theorem Hp_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Hp (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = (Hp Λ F F').map (β : S.V →ₗ[E] S.V) := by
  rw [Hp, Hp, Formalism.L2.SG.Pf.UUE_mapL β hβ, Formalism.L2.SG.Pf.orth_map_sat β hβ]

include hβ in
theorem Ylift_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Ylift (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = (Ylift Λ F F').map (β : S.V →ₗ[E] S.V) := by
  rw [Ylift, Ylift, Formalism.L2.SG.Pf.UUE_mapL β hβ, Xplus_mapL β hβ, Formalism.L2.SG.Pf.orth_map_sat β hβ, map_inf_equiv]

include hβ in
theorem Ylift'_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Ylift' (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = (Ylift' Λ F F').map (β : S.V →ₗ[E] S.V) := by
  rw [Ylift', Ylift', Formalism.L2.SG.Pf.UUE_mapL β hβ, Xplus_mapL β hβ, Formalism.L2.SG.Pf.orth_map_sat β hβ,
    map_inf_equiv]

theorem sgRel_mapL (F : LFlag S r T) (F' : LFlag S r T') (y y' : S.V) (al al' : E) :
    SgRel (mapL β hβ F) (mapL β hβ F') (β y) (β y') al al' ↔ SgRel F F' y y' al al' := by
  simp only [SgRel, Formalism.L2.SG.Pf.Xsp_mapL β hβ, Formalism.L2.SG.Pf.zt_mapL]
  constructor
  · rintro ⟨x, hx, x', hx', h⟩
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨x0', hx0', rfl⟩ := Submodule.mem_map.1 hx'
    refine ⟨x0, hx0, x0', hx0', β.injective ?_⟩
    simp only [map_sub, map_add, map_smul, LinearEquiv.coe_coe] at h ⊢
    exact h
  · rintro ⟨x, hx, x', hx', h⟩
    refine ⟨β x, Submodule.mem_map_of_mem hx, β x', Submodule.mem_map_of_mem hx', ?_⟩
    rw [← map_sub, h]
    simp only [map_add, map_smul]

end Gen

end BwdBetaCut

open BwdCut BwdBetaCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdBetaCut

def IotaC₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (VS D) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ x' ∈ Lrep Λ F', ∀ l ∈ Lrep Λ F, ∀ l₂ ∈ Lrep Λ₂ F, l - l₂ ∈ Xsp F →
    (l - x' ∈ NgX Λ (gS D) F F' ↔ l₂ - β₂ x' ∈ NgX Λ₂ (gS D) F F₂)

def W0₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (VS D) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ w ∈ Hp Λ F F', ∃ w₂ ∈ Hp Λ₂ F F₂, w - w₂ ∈ Xsp F ∧ β₂ w - w₂ ∈ Xsp F₂

def Scalar₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (VS D) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ y1 ∈ Ylift Λ F F', ∀ y2 ∈ Ylift Λ₂ F F₂, ∀ y1' ∈ Ylift' Λ F F', ∀ y2'' ∈ Ylift' Λ₂ F F₂,
    y1 - y2 ∈ Xsp F → y2'' - β₂ y1' ∈ Xsp F₂ →
      ∀ al al' : D.host.E, SgRel F F' y1 y1' al al' ↔ SgRel F F₂ y2 y2'' al al'

def IsPair₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (VS D) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  β₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap β₂ Λ = Λ₂ ∧
    (∀ j, (Xflag F' j).map (β₂ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag F₂ j) ∧ β₂ F'.fl.z = F₂.fl.z ∧
    IotaC₂ Λ Λ₂ F F' F₂ β₂ ∧ W0₂ Λ Λ₂ F F' F₂ β₂ ∧ Scalar₂ Λ Λ₂ F F' F₂ β₂

end BwdBetaCut

variable (u u' F0 what₂)

def BetaCore₂ : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', (∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) →
        TermHyp (F0 := F0) Λ₂ F'₂ → PD D γ.lam (lf D F0) u' (repF γ) → Gval (lf D F0) (repF γ) ≠ 0 →
        ∃ β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V, IsPair₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₂

variable {u u' F0 what₂}

namespace BwdBetaCut

theorem unipotent_preserves_x {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) :
    (Xsp (lf D F0)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp (lf D F0) := by
  have h := Formalism.L2.SG.Pf.Xsp_mapL n (isom_of_N0F hn) (lf D F0)
  rw [mapL_lf hn] at h
  exact h.symm

theorem unipotent_preserves_orth {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) :
    (orth (VS D) (Xsp (lf D F0))).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) (Xsp (lf D F0)) := by
  rw [← Formalism.L2.SG.Pf.orth_map_sat n (isom_of_N0F hn), unipotent_preserves_x hn]

theorem unipotent_inv_sub_mem {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) {v : (VS D).V}
    (hv : v ∈ orth (VS D) (Xsp (lf D F0))) : v - n.symm v ∈ Xsp (lf D F0) := by
  have h1 : n.symm v ∈ orth (VS D) (Xsp (lf D F0)) := by
    rw [← unipotent_preserves_orth hn] at hv
    rw [Submodule.mem_map_equiv] at hv
    exact hv
  have h2 := hn.2.2.1 _ h1
  rwa [LinearEquiv.apply_symm_apply] at h2

theorem Hp_le_orthX (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ) {T' : D.host.E}
    (F' : LFlag (VS D) D.R.rS T') (hL : IsLift Λ (lf D F0)) (hL' : IsLift Λ F') :
    Hp Λ (lf D F0) F' ≤ orth (VS D) (Xsp (lf D F0)) := by
  intro w hw
  rw [Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)]
  have hw' := hw
  rw [Hp, Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)] at hw'
  intro e he
  refine hw' e ?_
  refine (Submodule.span_le.2 ?_) he
  rintro _ ⟨a, rfl⟩
  have := PI.PairCorankPos.W.frame_mem_UUE Λ hΛ (lf D F0) F' hL hL' (Sum.inl a.castSucc)
  simpa [FlagG.fvec] using this

end BwdBetaCut

namespace BwdBetaCut

theorem map_mul_eq (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Submodule D.host.E (VS D).V) :
    U.map ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
      (U.map (b : (VS D).V →ₗ[D.host.E] (VS D).V)).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  rw [← Submodule.map_comp]; rfl

theorem orth_Xplus_le {T : D.host.E} (F : LFlag (VS D) D.R.rS T) :
    orth (VS D) (Xplus F) ≤ orth (VS D) (Xsp F) := by
  intro v hv
  rw [Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)] at hv ⊢
  exact fun x hx => hv x (le_sup_left (a := Xsp F) hx)

end BwdBetaCut

theorem betaCore_of₂ (h : BetaCore₂ Zd u u' F0 what₂) : BetaCore Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg hT hPD hG
  obtain ⟨β₂, hiso, hgm, hfl, hz, hI, hW, hSc⟩ := h hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩ hT hPD hG
  have hni := isom_of_N0F hn
  have hF : mapL n hni (lf D F0) = lf D F0 := mapL_lf hn
  have hΛ : Formalism.HermitianLatticesTheory.gmap n Λ₂ = γ.lam := gmap_eq_of_image himg
  have hfix := (hC.2.1.1 γ.lam γ.mem).2.1
  have hL₂ : IsLift Λ₂ (lf D F0) := by
    have := Formalism.L2.SG.Pf.IsLift_mapL n hni Λ₂ (lf D F0)
    rw [hF, hΛ] at this
    exact this.1 hfix.2.2.1
  have hX'' : Xsp (mapL n hni (liftF F'₂)) = (Xsp (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) :=
    Formalism.L2.SG.Pf.Xsp_mapL n hni _
  refine ⟨n * β₂, ⟨⟨Subgroup.mul_mem _ hni hiso, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Formalism.L2.SG.Pf.gmap_mul_sat, hgm, hΛ]
  · intro j
    rw [Formalism.L2.SG.Pf.Xflag_mapL n hni, ← hfl j, BwdBetaCut.map_mul_eq]
  · show n (β₂ (repF γ).fl.z) = n (liftF F'₂).fl.z
    rw [hz]
  · intro x' hx' l hl
    have hN : NgX γ.lam (gS D) (lf D F0) (mapL n hni (liftF F'₂)) =
        Formalism.HermitianLatticesTheory.gmap n (NgX Λ₂ (gS D) (lf D F0) (liftF F'₂)) := by
      rw [← Formalism.L2.SG.Pf.NgX_mapL n hni, hF, hΛ]
    have hLr : Lrep γ.lam (lf D F0) = Formalism.HermitianLatticesTheory.gmap n (Lrep Λ₂ (lf D F0)) := by
      rw [← Formalism.L2.SG.Pf.Lrep_mapL n hni, hF, hΛ]
    have hl₂ : n.symm l ∈ Lrep Λ₂ (lf D F0) := by
      rw [hLr, Formalism.L2.SG.Saturated.mem_gmap_iff] at hl; exact hl
    have hlo : l ∈ orth (VS D) (Xsp (lf D F0)) := (Submodule.mem_inf.1 hl).2
    rw [hI x' hx' l hl (n.symm l) hl₂ (BwdBetaCut.unipotent_inv_sub_mem hn hlo), hN, Formalism.L2.SG.Saturated.mem_gmap_iff]
    simp only [map_sub]
    rw [show n.symm ((n * β₂) x') = β₂ x' from n.symm_apply_apply (β₂ x')]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW w hw
    refine Submodule.mem_map.2 ⟨(w, n w₂), ?_, rfl⟩
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_ThPairs]
    have hHp : Hp γ.lam (lf D F0) (mapL n hni (liftF F'₂)) =
        (Hp Λ₂ (lf D F0) (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← BwdBetaCut.Hp_mapL n hni, hF, hΛ]
    have hw₂o := BwdBetaCut.Hp_le_orthX Λ₂ hΛ₂.1 (liftF F'₂) hL₂ hT.1.1 hw₂
    refine ⟨hw, ?_, ?_, ?_⟩
    · rw [hHp]; exact Submodule.mem_map_of_mem hw₂
    · have h3 := hn.2.2.1 w₂ hw₂o
      have : w - n w₂ = (w - w₂) - (n w₂ - w₂) := by abel
      show w - n w₂ ∈ Xsp (lf D F0)
      rw [this]; exact sub_mem h1 h3
    · show n (β₂ w) - n w₂ ∈ Xsp (mapL n hni (liftF F'₂))
      rw [← map_sub, hX'']
      exact Submodule.mem_map_of_mem h2
  · intro y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hd1 hd2 al al'
    have hY : Ylift γ.lam (lf D F0) (mapL n hni (liftF F'₂)) =
        (Ylift Λ₂ (lf D F0) (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← BwdBetaCut.Ylift_mapL n hni, hF, hΛ]
    have hY' : Ylift' γ.lam (lf D F0) (mapL n hni (liftF F'₂)) =
        (Ylift' Λ₂ (lf D F0) (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← BwdBetaCut.Ylift'_mapL n hni, hF, hΛ]
    have hy2o : y2 ∈ orth (VS D) (Xsp (lf D F0)) :=
      BwdBetaCut.orth_Xplus_le (lf D F0) (Submodule.mem_inf.1 hy2).2
    rw [hY, Submodule.mem_map_equiv] at hy2
    rw [hY', Submodule.mem_map_equiv] at hy2''
    have e1 : y1 - n.symm y2 ∈ Xsp (lf D F0) := by
      have : y1 - n.symm y2 = (y1 - y2) + (y2 - n.symm y2) := by abel
      rw [this]; exact add_mem hd1 (BwdBetaCut.unipotent_inv_sub_mem hn hy2o)
    have e2 : n.symm y2'' - β₂ y1' ∈ Xsp (liftF F'₂) := by
      have hd2' : y2'' - (n * β₂) y1' ∈ (Xsp (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
        rw [← hX'']; exact hd2
      rw [Submodule.mem_map_equiv] at hd2'
      have : n.symm (y2'' - (n * β₂) y1') = n.symm y2'' - β₂ y1' := by
        rw [map_sub]; congr 1; exact n.symm_apply_apply (β₂ y1')
      rwa [this] at hd2'
    rw [hSc y1 hy1 _ hy2 y1' hy1' _ hy2'' e1 e2 al al']
    have hs := BwdBetaCut.sgRel_mapL n hni (lf D F0) (liftF F'₂) (n.symm y2) (n.symm y2'') al al'
    rw [hF, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hs
    exact hs.symm

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
