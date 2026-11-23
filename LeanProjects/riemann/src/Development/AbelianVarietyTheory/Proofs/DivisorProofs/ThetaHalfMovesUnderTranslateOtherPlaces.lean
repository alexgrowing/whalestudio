import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppAtMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.ThetaBaseMove

open Formalism.IndefR.Fin.LevelGroupLemmas

section General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem heisO_smul' (u : WO S T) (c : ℂ) (g : WO S T → ℂ) : heisO ψ S T u (c • g) = c • heisO ψ S T u g := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_smul (c : ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (c • g) := by
  refine ⟨fun γ w => ?_, ?_, hg.cont.const_smul c, fun k L hL h0 w => (hg.smooth k L hL h0 w).const_smul c⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [hg.quasi]; ring
  · obtain ⟨U, hU, h⟩ := hg.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul', h u hu h0]⟩

theorem isPlaceModel_move (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ)) (g : GA D S) (h : GA D T) (c : ℂ)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g h x = x) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • om (g, h) f₀) (c • (om (g, h)).comp Tm) where
  trans Φ hΦ x hx := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, hTm.trans Φ hΦ x hx, LinearMap.comp_apply,
      hW.om_heis g h x (Tm Φ) (hth Φ hΦ), hfx x (Or.inl hx), heisO_smul']
  modul Φ hΦ y hy := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, hTm.modul Φ hΦ y hy, LinearMap.comp_apply,
      hW.om_heis g h y (Tm Φ) (hth Φ hΦ), hfx y (Or.inr hy), heisO_smul']
  vac := by rw [LinearMap.smul_apply, LinearMap.comp_apply, hTm.vac]

theorem isThetaAt_move (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hth : ∀ f₀, IsThetaFunO ψ S T f₀ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm →
      ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ))
    {b Φ f : WO S T → ℂ} (hb : IsThetaFunO ψ S T b) (g : GA D S) (h : GA D T) {c : ℂ} (hc : c ≠ 0)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g h x = x)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 b Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • om (g, h) b) Φ (c • om (g, h) f) := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  refine ⟨⟨_, isPlaceModel_move hW hTm (hth b hb Tm hTm) g h c hfx⟩, fun T' hT' => ?_⟩
  have hfx' : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g⁻¹ h⁻¹ x = x := fun x hx => by
    conv_lhs => rw [← hfx x hx]
    rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
  have k1 : ∀ v, om (g⁻¹, h⁻¹) (om (g, h) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have k2 : ∀ v, om (g, h) (om (g⁻¹, h⁻¹) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have hm := isPlaceModel_move hW hT' (hth _ (theta_smul c (hW.om_pres _ _ hb)) T' hT') g⁻¹ h⁻¹ c⁻¹ hfx'
  rw [map_smul, k1, smul_smul, inv_mul_cancel₀ hc, one_smul] at hm
  have e1 : f = _ := hall _ hm
  rw [e1, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, k2, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem actO_fix_of_orth {a e : AE D} {z : GA D S} (hz : SuppAt a S z) (h0 : e * (a + cA D a) = 0) {x : WO S T}
    (hx : IsHalf e x) : actO S T z⁻¹ 1 x = x := by
  rw [actO_eq, inv_inv, mt_one', Matrix.one_mul]
  have : HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S z - 1) = 0 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← hx k j, ← hz j l]
    linear_combination (x k j * (mt S z - 1) j l) * h0
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this

end General

theorem thAt_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Sa ⊆ R.Q t → St ⊆ R.Q t → Disjoint Sa St → ∀ (eg ea et : AE D) (fg b Φ f : WO (Vc D i) (Wc D i) → ℂ) (z : GA D (Vc D i)) (c : ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) b → SuppAt ea (Vc D i) z → c ≠ 0 → ThAt R i (cA D et) b Φ f → ThAt R i (cA D et) (c • R.ωP i t (z⁻¹, 1) b) Φ (c • R.ωP i t (z⁻¹, 1) f) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t _hV Sa St hSa hSt hd eg ea et fg b Φ f z c hg ha ht hfg hb hz hc hf
  obtain ⟨⟨hψ, hvac⟩, e, he, -⟩ := hC.thP.vP i t
  have hW := (GlobalTheory.OnCmp.kerDat_tuple (i := i) hC.lev hC.thP t).weil
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hsp : SplitSet (R.Q t) := SplitSet.mono ⟨e, he⟩ (by convert Finset.subset_union_right)
  have hth : ∀ {a : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum a P → ∀ f₀, IsThetaFunO R.ψ (Vc D i) (Wc D i) f₀ → ∀ Tm,
      IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D a)
        (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 f₀ Tm →
      ∀ Ψ, IsSBHalf (cA D a) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ →
        IsThetaFunO R.ψ (Vc D i) (Wc D i) (Tm Ψ) := by
    intro a P h f₀ hf₀ Tm hTm Ψ hΨ
    exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ hSV.1 hSW.1 (by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self h])
      (by rw [← map_mul, h.2, map_zero]) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart h)) hf₀ Tm hTm Ψ hΨ
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg))
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBa := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha))
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    Sa (fun y => omegaQ Sa (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  have hfgθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) fg := by
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hfg
    rw [hall Tm hTm]
    exact hth hg _ hvac.theta Tm hTm _ hSBg
  have hbθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) b := by
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hb
    rw [hall Tm hTm]
    exact hth ha _ hfgθ Tm hTm _ hSBa
  have o1 : et * ea = 0 := by
    rw [← idem_eq ht, ← idem_eq ha, idem, idem, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq =>
      hsp.mul_eq_zero (hSt hp) (hSa hq) fun e => Finset.disjoint_left.1 hd hq (e ▸ hp)
  have o2 : et * cA D ea = 0 := by
    rw [← idem_eq ht, ← idem_eq ha, idem, idem, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => hsp.mul_conj (hSt hp) (hSa hq)
  have o3 : et * (ea + cA D ea) = 0 := by rw [mul_add, o1, o2, add_zero]
  have o4 : cA D et * (ea + cA D ea) = 0 := by
    have := congrArg (cA D) o3
    rwa [map_mul, map_add, GlobalTheory.LatVac.cA_cA, map_zero, add_comm] at this
  refine isThetaAt_move hW (hth ht) hbθ z⁻¹ 1 hc (fun x hx => ?_) hf
  rcases hx with hx | hx
  · exact actO_fix_of_orth hz o4 hx
  · rw [GlobalTheory.LatVac.cA_cA] at hx
    exact actO_fix_of_orth hz o3 hx

end GlobalTheory.ThetaBaseMove
