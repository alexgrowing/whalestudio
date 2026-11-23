import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmPart
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA

noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open OmP

namespace OmL

section Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem h_sum_left {ι : Type} [Fintype ι] (c : ι → E) (g : ι → V) (y : V) :
    H.h (∑ b, c b • g b) y = ∑ b, c b * H.h (g b) y := by
  let L : V →+ E := ⟨⟨fun x => H.h x y, H.h_zero_left y⟩, fun a b => H.h_add_left a b y⟩
  have := map_sum L (fun b => c b • g b) Finset.univ
  simp only [L, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  rw [this]
  exact Finset.sum_congr rfl fun b _ => H.h_smul_left _ _ _

theorem h_sub_left (x y z : V) : H.h (x - y) z = H.h x z - H.h y z := by
  have e : x - y = x + (-1 : E) • y := by simp [sub_eq_add_neg]
  rw [e, H.h_add_left, H.h_smul_left]
  ring

theorem dl_last {r : ℕ} (f g : Fin (r + 1) → V) : H.Dl f g (r + 1) = (H.Zhat f g).det := by
  unfold Loc.HermSp.Dl
  rw [dif_pos le_rfl]
  rfl

theorem om_pair {r : ℕ} (f g : Fin (r + 1) → V) (a : Fin (r + 1)) :
    H.h (H.om' f g) (f a) = (H.Zhat f g).det * (if a = Fin.last r then 1 else 0) := by
  unfold Loc.HermSp.om'
  rw [h_sum_left]
  have e : ∑ b, (H.Zhat f g).adjugate b (Fin.last r) * H.h (g b) (f a) =
      (H.Zhat f g * (H.Zhat f g).adjugate) a (Fin.last r) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [e, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

theorem om_perp {r : ℕ} (f g : Fin (r + 1) → V) : H.om' f g ∈ H.perp (H.X f) := by
  intro s hs
  have hl : ∀ s ∈ H.X f, H.h s (H.om' f g) = 0 := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [H.h_herm (H.om' f g), om_pair]
      simp [Fin.castSucc_ne_last]
    | zero => exact H.h_zero_left _
    | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]
  rw [H.h_herm s, hl s hs, map_zero]

theorem uniq_loc {r : ℕ} (f g : Fin (r + 1) → V) (hdet : IsUnit (H.Zhat f g).det) {d : V}
    (hd : d ∈ Submodule.span E (Set.range g)) (h0 : ∀ a, H.h d (f a) = 0) : d = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hd
  have hc : H.Zhat f g *ᵥ c = 0 := by
    funext a
    have := h0 a
    rw [h_sum_left] at this
    rw [Pi.zero_apply, ← this, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have h2 : (H.Zhat f g).det • c = 0 := by
    have := congrArg (fun v => (H.Zhat f g).adjugate *ᵥ v) hc
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero] at this
    rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at this
  have h3 : c = 0 := by
    obtain ⟨u, hu⟩ := hdet
    have := congrArg (fun v => (↑u⁻¹ : E) • v) h2
    simp only [← hu, smul_zero, smul_smul, Units.inv_mul, one_smul] at this
    exact this
  subst h3
  simp

theorem sendsTo_refl_mem {r : ℕ} (f g₁ g₂ : Fin (r + 1) → V) (c₁ c₂ : E)
    (hs : H.SendsTo (LinearEquiv.refl E (H.Wb f)).toLinearMap c₁ c₂ (H.om' f g₁) (H.om' f g₂)) :
    c₁ • H.om' f g₁ - c₂ • H.om' f g₂ ∈ H.X f := by
  have hs' := hs ⟨_, om_perp H f g₁⟩ ⟨_, om_perp H f g₂⟩ rfl rfl
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_apply] at hs'
  have h0 : H.mkW f (c₁ • ⟨_, om_perp H f g₁⟩ - c₂ • ⟨_, om_perp H f g₂⟩) = 0 := by
    rw [LinearMap.map_sub, LinearMap.map_smul, LinearMap.map_smul, hs', sub_self]
  have h1 := (Submodule.Quotient.mk_eq_zero _).1 h0
  rw [Submodule.mem_comap] at h1
  exact h1

theorem smul_combine {W : Type} [AddCommGroup W] [Module E W] (k d₁ d₂ : E) (a b A B : W)
    (ha : k • a = d₂ • A) (hb : k • b = d₁ • B) : k • (d₁ • a - d₂ • b) = (d₁ * d₂) • (A - B) := by
  rw [smul_sub, smul_comm k d₁, smul_comm k d₂, ha, hb, smul_smul, smul_smul, mul_comm d₂ d₁, ← smul_sub]

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

open Formalism.L2.SG.Pf.ScalarFramePf (sF sF' isUnit_sF isUnit_sF')

def fL {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : Fin (D.R.rS + 1) → Vp D p :=
  fun a => sF Zd p a • baseChange₂ D p (F0.fvec a)

def gL (G : Fin (D.R.rS + 1) → (VS D).V) : Fin (D.R.rS + 1) → Vp D p :=
  fun b => sF' Zd p b • baseChange₂ D p (G b)

theorem h_bcP_f {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Ω : (VS D).V) (a : Fin (D.R.rS + 1)) :
    (locH Zd p).h (baseChange₂ D p Ω) (fL Zd p F0 a) =
      (Zd.M p).L.cj (sF Zd p a) * (D.s.atP p).ιE ((VS D).hT (F0.fvec a) Ω) := by
  unfold fL
  rw [Formalism.L2.SG.Pf.ScalarFramePf.h_smul_right]
  congr 1
  exact baseChangeAt_form Zd.M p (Zd.hcj p) Ω (F0.fvec a)

theorem bcP_sp (G : Fin (D.R.rS + 1) → (VS D).V) {Ω : (VS D).V}
    (hΩ : Ω ∈ Submodule.span D.host.E (Set.range G)) :
    baseChange₂ D p Ω ∈ Submodule.span (D.s.atP p).Ep (Set.range (gL Zd p G)) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hΩ
  rw [map_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [baseChange_smul₂]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨u, hu⟩ := isUnit_sF' Zd p b
  have e : baseChange₂ D p (G b) = (↑u⁻¹ : (D.s.atP p).Ep) • gL Zd p G b := by
    simp only [gL, ← hu, smul_smul, Units.inv_mul, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem omL_eq {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V) {Ω : (VS D).V}
    (hsp : Ω ∈ Submodule.span D.host.E (Set.range G))
    (hΩ : ∀ a, (VS D).hT (F0.fvec a) Ω = if a = Fin.last D.R.rS then 1 else 0)
    (hdet : IsUnit ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p G)).det) :
    (Zd.M p).L.cj (sF Zd p (Fin.last D.R.rS)) • (locH Zd p).om' (fL Zd p F0) (gL Zd p G) =
      ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p G)).det • baseChange₂ D p Ω := by
  apply sub_eq_zero.1
  refine uniq_loc (locH Zd p) _ _ hdet (Submodule.sub_mem _ (Submodule.smul_mem _ _ ?_)
    (Submodule.smul_mem _ _ (bcP_sp Zd p G hsp))) fun a => ?_
  · exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · rw [h_sub_left, (locH Zd p).h_smul_left, (locH Zd p).h_smul_left, om_pair, h_bcP_f, hΩ]
    by_cases ha : a = Fin.last D.R.rS
    · subst ha; simp; ring
    · simp [ha]

theorem zhat_fg {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V) :
    (locH Zd p).Zhat (fL Zd p F0) (gL Zd p G) =
      Matrix.diagonal (fun a => (Zd.M p).L.cj (sF Zd p a)) *
        (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).map (D.s.atP p).ιE * Matrix.diagonal (sF' Zd p) := by
  ext a b
  simp only [Loc.HermSp.Zhat, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, fL, gL,
    Formalism.L2.SG.Pf.ScalarFramePf.h_bcP]
  rw [show brS (VS D) (G b) (F0.fvec a) = (VS D).hT (F0.fvec a) (G b) from rfl]
  ring

theorem isUnit_zhat_fg {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V)
    (h : (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det ≠ 0) :
    IsUnit ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p G)).det := by
  have e : ((Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).map (D.s.atP p).ιE).det =
      (D.s.atP p).ιE (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det := (RingHom.map_det _ _).symm
  rw [zhat_fg, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, e]
  refine ((IsUnit.prod_univ_iff.2 fun a => (isUnit_sF Zd p a).map _).mul
    ((isUnit_iff_ne_zero.2 h).map _)).mul (IsUnit.prod_univ_iff.2 fun b => isUnit_sF' Zd p b)

theorem descend {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (c : Fin D.R.rS → (D.s.atP p).Ep) {v : (VS D).V}
    (h : baseChange₂ D p v ∈ Submodule.span (D.s.atP p).Ep (Set.range fun i => c i • baseChange₂ D p (F0.fvec i.castSucc))) :
    v ∈ F0.X := by
  by_contra hv
  obtain ⟨ℓ, hℓv, hℓX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  let Lp : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep :=
    { toFun := fun y => ∑ i, y i * (D.s.atP p).ιE (ℓ ((VS D).frame i))
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a y => by simp [Finset.mul_sum, mul_assoc] }
  have hb : ∀ x, Lp (baseChange₂ D p x) = (D.s.atP p).ιE (ℓ x) := by
    intro x
    have e : ℓ x = ∑ i, (VS D).frame.repr x i * ℓ ((VS D).frame i) := by
      conv_lhs => rw [← (VS D).frame.sum_repr x]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    rw [e, map_sum]
    simp only [Lp, LinearMap.coe_mk, AddHom.coe_mk, baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact Finset.sum_congr rfl fun i _ => (map_mul _ _ _).symm
  have hℓe : ∀ i : Fin D.R.rS, ℓ (F0.fvec i.castSucc) = 0 := by
    intro i
    have : ℓ (F0.fvec i.castSucc) ∈ F0.X.map ℓ :=
      Submodule.mem_map_of_mem (by rw [fvec_cs]; exact Submodule.subset_span ⟨i, rfl⟩)
    rw [hℓX] at this
    exact (Submodule.mem_bot _).1 this
  have hle : Submodule.span (D.s.atP p).Ep (Set.range fun i : Fin D.R.rS => c i • baseChange₂ D p (F0.fvec i.castSucc)) ≤
      LinearMap.ker Lp := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_smul, hb, hℓe, map_zero, smul_zero]
  have hz := hle h
  rw [LinearMap.mem_ker, hb] at hz
  exact hℓv ((D.s.atP p).ιE.injective (by rw [hz, map_zero]))

end D7

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sp_frameAct {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {n : ℕ}
    (f : Fin n → S.V) (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) (hξ : ξ⁻¹ * ξ = 1) :
    Submodule.span E (Set.range f) ≤ Submodule.span E (Set.range (frameAct f ξ⁻¹)) := by
  rw [Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  have key : ∑ a, ((ξ a b : 𝓞 E) : E) • frameAct f ξ⁻¹ a = f b := by
    simp only [frameAct, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h1 : ∀ c, ∑ a, ((ξ a b : 𝓞 E) : E) * ((ξ⁻¹ c a : 𝓞 E) : E) = (((ξ⁻¹ * ξ) c b : 𝓞 E) : E) := by
      intro c
      rw [Matrix.mul_apply]
      push_cast
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    simp only [← Finset.sum_smul, h1, hξ, Matrix.one_apply]
    simp
  rw [← key]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem admissibility_witness_inv_mul {D : Formalism.BasicNotions.D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') : (admXi D Λ F F')⁻¹ * admXi D Λ F F' = 1 := by
  obtain ⟨h1, h2⟩ := admissibility_witness_unitriangular Λ F F'
  have hbt : (admXi D Λ F F').BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : (admXi D Λ F F').det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [h2]
  exact Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one)

end Main

end OmL

open OmL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem omLoc_at (p : PlF D) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Gγ G₂ : Fin (D.R.rS + 1) → (VS D).V)
    {Ωγ Ω₂ : (VS D).V} (hsγ : Ωγ ∈ Submodule.span D.host.E (Set.range Gγ))
    (hs₂ : Ω₂ ∈ Submodule.span D.host.E (Set.range G₂))
    (hγ : ∀ a, (VS D).hT (F0.fvec a) Ωγ = if a = Fin.last D.R.rS then 1 else 0)
    (h₂ : ∀ a, (VS D).hT (F0.fvec a) Ω₂ = if a = Fin.last D.R.rS then 1 else 0)
    (hunγ : IsUnit ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p Gγ)).det)
    (hun2 : IsUnit ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p G₂)).det)
    (hs : (locH Zd p).SendsTo (LinearEquiv.refl _ _ : (locH Zd p).Wb (fL Zd p F0) ≃ₗ[(D.s.atP p).Ep]
        (locH Zd p).Wb (fL Zd p F0)).toLinearMap
      ((locH Zd p).Dl (fL Zd p F0) (gL Zd p G₂) (D.R.rS + 1)) ((locH Zd p).Dl (fL Zd p F0) (gL Zd p Gγ) (D.R.rS + 1))
      ((locH Zd p).om' (fL Zd p F0) (gL Zd p Gγ)) ((locH Zd p).om' (fL Zd p F0) (gL Zd p G₂))) :
    Ω₂ - Ωγ ∈ F0.X := by
  have e1 := omL_eq Zd p F0 Gγ hsγ hγ hunγ
  have e2 := omL_eq Zd p F0 G₂ hs₂ h₂ hun2
  have hm := sendsTo_refl_mem (locH Zd p) (fL Zd p F0) (gL Zd p Gγ) (gL Zd p G₂) _ _ hs
  rw [dl_last, dl_last] at hm
  have hm2 := Submodule.smul_mem _ ((Zd.M p).L.cj (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p (Fin.last D.R.rS))) hm
  rw [smul_combine _ _ _ _ _ _ _ e1 e2, ← map_sub] at hm2
  obtain ⟨uu, huu⟩ := hun2.mul hunγ
  have hX := Submodule.smul_mem _ (↑uu⁻¹ : (D.s.atP p).Ep) hm2
  rw [← huu, smul_smul, Units.inv_mul, one_smul] at hX
  have hd := OmL.descend p F0 (fun i => Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p i.castSucc) hX
  rw [← neg_sub]
  exact Submodule.neg_mem _ hd

theorem omega_local_holds : OmLoc Zd u u' F0 what₂ := by
  intro _ γ Z _ F'₂ φ φ' hS _ hdZ Ω₂ Ωγ h₂ hγ
  obtain ⟨p⟩ := Formalism.L2.SG.Pf.LocModel.plF_nonempty D
  have hT2 := hS.2.1 p
  have hφ := hS.2.2 p
  have hs := hT2.2.2.2.1.2.2.2.1
  rw [hφ] at hs
  have hunγ := hT2.1.1.2.2.2.1
  rw [dl_last] at hunγ
  refine omLoc_at Zd p F0 (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹) F'₂.fl.fvec
    (sp_frameAct _ _ (admissibility_witness_inv_mul γ.lam (lf D F0) (repF γ)) hγ.1) h₂.1 hγ.2 h₂.2 hunγ ?_ hs
  apply isUnit_zhat_fg
  have e : (Matrix.of fun a b => (VS D).hT (F0.fvec a) (F'₂.fl.fvec b)) = Z := hS.1
  rw [e]
  exact hdZ

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
