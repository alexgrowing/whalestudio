import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActR
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActL
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLChi
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq

noncomputable section

open scoped Classical InnerProductSpace
open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.SatGramRep

namespace Formalism.L2.SG.Pf.SatGramActR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HSc

variable {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def hsInv (f : Formalism.L2.SG.PackageTie.HS Wq Wp) : Wq →L[ℂ] Wp :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ Wq i)).smulRight (f i)

theorem hsInv_apply (f : Formalism.L2.SG.PackageTie.HS Wq Wp) (ξ : Wq) :
    hsInv f ξ = ∑ i, ⟪stdOrthonormalBasis ℂ Wq i, ξ⟫_ℂ • f i := by
  simp [hsInv]

theorem hsEmb_hsInv (f : Formalism.L2.SG.PackageTie.HS Wq Wp) : Formalism.L2.SG.PackageTie.hsEmb (hsInv f) = f := by
  ext j
  simp only [Formalism.L2.SG.PackageTie.hsEmb, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, hsInv_apply]
  rw [Finset.sum_eq_single j]
  · rw [(stdOrthonormalBasis ℂ Wq).inner_eq_one, one_smul]
  · intro i _ hij
    rw [(stdOrthonormalBasis ℂ Wq).inner_eq_zero hij, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem hsInv_hsEmb (A : Wq →L[ℂ] Wp) : hsInv (Formalism.L2.SG.PackageTie.hsEmb A) = A := by
  ext ξ
  rw [hsInv_apply]
  simp only [Formalism.L2.SG.PackageTie.hsEmb, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply]
  conv_rhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' ξ]
  rw [map_sum]
  simp [map_smul]

theorem hsNormSq_comp_iso (A : Wq →L[ℂ] Wp) (P : Wq ≃ₗᵢ[ℂ] Wq) :
    hsNormSq (A.comp (P.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq)) = hsNormSq A :=
  Formalism.L2.SG.Pf.hsNormSq_of_iso A _ P id (fun _ => rfl) (fun x => by simp)

def hsR (P : Wq ≃ₗᵢ[ℂ] Wq) :
    Formalism.L2.SG.PackageTie.HS Wq Wp ≃ₗᵢ[ℂ] Formalism.L2.SG.PackageTie.HS Wq Wp where
  toFun f := Formalism.L2.SG.PackageTie.hsEmb ((hsInv f).comp (P.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq))
  invFun f := Formalism.L2.SG.PackageTie.hsEmb ((hsInv f).comp (P.toContinuousLinearEquiv : Wq →L[ℂ] Wq))
  map_add' f g := by
    have e : hsInv (f + g) = hsInv f + hsInv g := by
      ext ξ
      simp only [_root_.add_apply, hsInv_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PiLp.add_apply, smul_add]
    rw [e, ContinuousLinearMap.add_comp, map_add]
  map_smul' c f := by
    have e : hsInv (c • f) = c • hsInv f := by
      ext ξ
      simp only [_root_.smul_apply, hsInv_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PiLp.smul_apply, smul_comm]
    rw [e, ContinuousLinearMap.smul_comp, map_smul]
    rfl
  left_inv f := by
    simp only [hsInv_hsEmb]
    rw [ContinuousLinearMap.comp_assoc]
    have : ((P.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq)).comp (P.toContinuousLinearEquiv : Wq →L[ℂ] Wq) =
        ContinuousLinearMap.id ℂ Wq := by ext x; simp
    rw [this, ContinuousLinearMap.comp_id, hsEmb_hsInv]
  right_inv f := by
    simp only [hsInv_hsEmb]
    rw [ContinuousLinearMap.comp_assoc]
    have : ((P.toContinuousLinearEquiv : Wq →L[ℂ] Wq)).comp (P.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq) =
        ContinuousLinearMap.id ℂ Wq := by ext x; simp
    rw [this, ContinuousLinearMap.comp_id, hsEmb_hsInv]
  norm_map' f := by
    have h1 : ‖Formalism.L2.SG.PackageTie.hsEmb ((hsInv f).comp (P.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq))‖ ^ 2 =
        ‖f‖ ^ 2 := by
      rw [Formalism.L2.SG.PackageTie.norm_hsEmb_sq, hsNormSq_comp_iso, ← Formalism.L2.SG.PackageTie.norm_hsEmb_sq,
        hsEmb_hsInv]
    have := congrArg Real.sqrt h1
    simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem hsR_emb (P : Wq ≃ₗᵢ[ℂ] Wq) (A : Wq →L[ℂ] Wp) :
    hsR (Wp := Wp) P (Formalism.L2.SG.PackageTie.hsEmb A) =
      Formalism.L2.SG.PackageTie.hsEmb (A.comp (P.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq)) := by
  show Formalism.L2.SG.PackageTie.hsEmb ((hsInv (Formalism.L2.SG.PackageTie.hsEmb A)).comp _) = _
  rw [hsInv_hsEmb]

end HSc

section StepsPf

theorem autFConjN_holds : AutFConjN := fun _ _ _ _ _ hβ _ hn => Formalism.L2.SG.Pf.SatGramActL.nlam_conj hβ hn

variable {D : D7} (X : HidaSetting D)

theorem ooR_holds : OOR := by
  intro D X u u' γ Ω x
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  have hs : (γ : X.B.I.GA).1 ∈ Hinf X u' := (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).1
  set s : X.B.I.Ginf := (γ : X.B.I.GA).1 with hsdef
  let P := Formalism.L2.SG.Pf.SatGramActL.piUe u' s hs
  let L : (X.Vpi u' →L[ℂ] X.Vpi u) ≃L[ℂ] (X.Vpi u' →L[ℂ] X.Vpi u) :=
    P.toContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℂ (X.Vpi u))
  have hsS : s ∈ X.SinfU u' := hinf_le_sinf X u' s hs
  have hsS' : s⁻¹ ∈ X.SinfU u' := hinf_le_sinf X u' s⁻¹ ((Hinf X u').inv_mem hs)
  have hL : ∀ f, L f = f.comp (X.piU u' s⁻¹) := fun f => by
    ext ξ; rfl
  have hrk : ∀ (v : X.Vpi u) (w : X.Vpi u'), rk1 v (X.piU u' s w) = L (rk1 v w) := by
    intro v w
    rw [hL]
    ext ξ
    simp only [rankOneInnerOperator_apply, ContinuousLinearMap.comp_apply]
    congr 1
    have e1 : X.piU u' s (X.piU u' s⁻¹ ξ) = ξ := by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← (X.piU_rep u').2.1 _ hsS _ hsS',
        mul_inv_cancel, (X.piU_rep u').1, ContinuousLinearMap.one_apply]
    conv_lhs => rw [← e1]
    exact (X.piU_rep u').2.2.1 s hsS w (X.piU u' s⁻¹ ξ)
  unfold OO
  have hpt : ∀ y, rk1 (X.Wu u y) (X.Wu u' ((x * s⁻¹)⁻¹ * y)) = L (rk1 (X.Wu u y) (X.Wu u' (x⁻¹ * y))) := by
    intro y
    have e : (x * s⁻¹)⁻¹ * y = s * (x⁻¹ * y) := by group
    rw [e, Formalism.L2.SG.Pf.SatGramActL.wu_left X u' hs, hrk]
  simp_rw [hpt]
  rw [ContinuousLinearEquiv.integral_comp_comm, hL]

theorem kB_inv_fix_nxt {w : D.what₂.Word} (h : Hfin X w) (γ : Gam X w)
    (hk : ((h : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) * ((h : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) *
      ((h : X.B.I.Gf) * X.xu w))⁻¹ *ᵥ nxt X.e0 X.z0 a) (nxt X.e0 X.z0 a) := by
  have e : (((iotaF X w γ * h : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * ((h : X.B.I.Gf) * X.xu w) =
      (((h : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) * ((h : X.B.I.Gf) * X.xu w))⁻¹ := by
    push_cast
    group
  have hK : (((iotaF X w γ * h : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * ((h : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [e]; exact mem_Kset_inv X hk
  have h2 := (column_fixed_holds X w (iotaF X w γ * h) h hK).2
  rw [e] at h2
  exact h2

theorem chiNR_holds (hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll) : ChiNR := by
  intro D X w h γ κ hκ hk
  have h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
    have hh := mem_Kset_mul X hk (mem_Kset_inv X hk)
    rwa [mul_inv_cancel] at hh
  have hf : ∀ a, CongG X (X.B.I.fmat (1 : X.B.I.Gf)⁻¹ *ᵥ X.f0 a) (X.f0 a) := by
    have hK : (((1 : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * (((1 : Hfin X w) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
      rw [inv_mul_cancel]; exact h1
    have hh := (column_fixed_holds X w 1 1 hK).1
    simpa only [inv_mul_cancel, inv_one] using hh
  have hh := hB D X κ 1 _ hκ h1 (mem_Kset_inv X hk) hf (kB_inv_fix_nxt X h γ hk)
  rwa [one_mul] at hh

theorem kOf_mul_right (u u' : D.what₂.Word) (a b : X.B.I.Gf) (x y : X.B.I.GA) :
    kOf X u u' a b (x * y) = kOf X u u' a b x * (((b * X.xu u')⁻¹ * y.2 * (b * X.xu u'))) := by
  unfold kOf; rw [Prod.snd_mul]; group

end StepsPf

section RO

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}

theorem roset_mul_aut {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    ROset X F0 F0' Λ Λ' (γ * β⁻¹) = ROset X F0 F0' Λ Λ' γ := by
  have hβi : β⁻¹ ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0') := Formalism.L2.SG.Saturated.inv_mem_AutF' hβ
  ext y
  constructor
  · rintro ⟨x, n, hx, hy, hn, hn'⟩
    refine ⟨x, n, hx, hy, hn, ?_⟩
    have := Formalism.L2.SG.Pf.SatGramActL.nlam_conj hβi hn'
    have e : β⁻¹ * ((γ * β⁻¹)⁻¹ * n * (γ * β⁻¹)) * β⁻¹⁻¹ = γ⁻¹ * n * γ := by group
    rwa [e] at this
  · rintro ⟨x, n, hx, hy, hn, hn'⟩
    refine ⟨x, n, hx, hy, hn, ?_⟩
    have := Formalism.L2.SG.Pf.SatGramActL.nlam_conj hβ hn'
    have e : β * (γ⁻¹ * n * γ) * β⁻¹ = (γ * β⁻¹)⁻¹ * n * (γ * β⁻¹) := by group
    rwa [e] at this

end RO

section Main

open Formalism.L2.SG.Pf.SatGramActL in

theorem right_action_three_families (hB : ChiNBiAll) (hIR : IotaRepC) (hAR : AmpRepNC) : RightActC' := by
  intro D X Y u u' hOI _ _ S hS q b hb
  obtain ⟨γ, hk, rfl⟩ := hb
  have hk' : kB (Y.cs u') q.2.1 γ ∈ X.B.I.Kset := hk
  obtain ⟨β, hx, hβ⟩ := betaLift_holds D X u' (Y.what₂ u') (Y.cs u') q.2.1 q.2.2 γ hk'
  have hs : (γ : X.B.I.GA).1 ∈ Hinf X u' := (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).1
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u'
  have hl' : ∀ t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), positionT t = q → t.lam' = q.2.1 :=
    fun t ht => congrArg (fun r => (r.2 : Submodule (𝓞 D.host.E) (VS D).V)) ht
  refine ⟨tequiv (what₂ := Y.what₂ u) (rows' := Y.what₂ u') (γ : X.B.I.GA) β autFConjN_holds hx,
    hsR (piUe u' (γ : X.B.I.GA).1 hs), ?_, ?_, ?_⟩
  · intro t
    show (t ∈ S ∧ positionT t = q) ↔
      (tmap (γ : X.B.I.GA) β autFConjN_holds hx t ∈ S ∧ positionT (tmap (γ : X.B.I.GA) β autFConjN_holds hx t) = q)
    have hsl : positionT (tmap (γ : X.B.I.GA) β autFConjN_holds hx t) = positionT t := rfl
    rw [hsl, mem_fam_iff Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (toTerm_tmap _ β _ hx t) S hS]
  · intro t _ ht
    have hβt : β ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D (X.Fu u')) := (hl' t ht) ▸ hβ
    have hkt : kB (Y.cs u') t.lam' γ ∈ X.B.I.Kset := (hl' t ht) ▸ hk'
    show iotaOf Y.TR (Y.cs u) (Y.cs u') (tmap (γ : X.B.I.GA) β autFConjN_holds hx t) =
      iotaOf Y.TR (Y.cs u) (Y.cs u') t * (levi Y.TR (kB (Y.cs u') q.2.1 γ))⁻¹
    rw [iotaOf_of_mk (hIR D X Y u u') (tmap (γ : X.B.I.GA) β autFConjN_holds hx t)
      (rmul (γ : X.B.I.GA) β hx hβt t.rep) (tmap_cls _ β _ hx t hβt)]
    rw [iotaOf_of_mk (hIR D X Y u u') t t.rep (Quot.out_eq t.cls).symm]
    have e1 : (rmul (γ : X.B.I.GA) β hx hβt t.rep).1.1 = t.rep.1.1 * (γ : X.B.I.GA)⁻¹ := rfl
    have e2 : ((((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((γ : X.B.I.GA)⁻¹).2 *
        (((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')) = (kB (Y.cs u') t.lam' γ)⁻¹ := by
      have eg : (γ : X.B.I.GA).2 = (iotaF X u' γ : X.B.I.Gf) := rfl
      rw [Prod.snd_inv, eg]
      unfold kB
      group
    have hG1 : Good X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.rep.1.1) :=
      Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') t
    have hG2 : Good X (kB (Y.cs u') t.lam' γ) := satGramActLIota_kB_good (Y.cs u') t.lam' γ hkt
    show levi Y.TR (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ : X.B.I.GA)⁻¹)) = _
    rw [kOf_mul_right, e2, levi_mul Y.TR hG1 (good_inv X hG2), levi_inv Y.TR hG2]
    have hq2 : kB (Y.cs u') (q.2 : Submodule (𝓞 D.host.E) (VS D).V) γ = kB (Y.cs u') t.lam' γ := by rw [hl' t ht]
    rw [hq2]
  · intro t _ ht
    have hβt : β ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D (X.Fu u')) := (hl' t ht) ▸ hβ
    have hkt : kB (Y.cs u') t.lam' γ ∈ X.B.I.Kset := (hl' t ht) ▸ hk'
    show Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')
        (tmap (γ : X.B.I.GA) β autFConjN_holds hx t)) =
      hsR (piUe u' (γ : X.B.I.GA).1 hs) (Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t))
    have hft := fundOf_spec hF t
    have hΩ : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') t.lam t.lam' (rmul (γ : X.B.I.GA) β hx hβt t.rep).1.2)
        (FundOf t) := by
      have e := roset_mul_aut (X := X) (F0 := X.Fu u) (Λ := t.lam) hβt t.rep.1.2
      convert hft using 2
      exact e
    rw [ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI (tmap (γ : X.B.I.GA) β autFConjN_holds hx t)
      (rmul (γ : X.B.I.GA) β hx hβt t.rep) (tmap_cls _ β _ hx t hβt) (FundOf t) hΩ]
    rw [ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI t t.rep (Quot.out_eq t.cls).symm (FundOf t) hft]
    rw [hsR_emb]
    refine congrArg (fun A => Formalism.L2.SG.PackageTie.hsEmb A) ?_
    have e1 : (rmul (γ : X.B.I.GA) β hx hβt t.rep).1.1 = t.rep.1.1 * (γ : X.B.I.GA)⁻¹ := rfl
    have e2 : ((((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((γ : X.B.I.GA)⁻¹).2 *
        (((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')) = (kB (Y.cs u') t.lam' γ)⁻¹ := by
      have eg : (γ : X.B.I.GA).2 = (iotaF X u' γ : X.B.I.Gf) := rfl
      rw [Prod.snd_inv, eg]
      unfold kB
      group
    have hκ := ChiLeft.kBB_mem Y u u' t.mem t.mem' t.rep
    have eχ : chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ : X.B.I.GA)⁻¹)) =
        chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
          ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.rep.1.1) := by
      rw [kOf_mul_right, e2]
      exact chiNR_holds hB D X u' ((Y.cs u').h ((Y.cs u').base t.lam')) γ _ hκ hkt
    have eO : (t.rep.1.1 * (γ : X.B.I.GA)⁻¹).1 = t.rep.1.1.1 * ((γ : X.B.I.GA).1)⁻¹ := by
      rw [Prod.fst_mul, Prod.fst_inv]
    have hU : (((piUe u' (γ : X.B.I.GA).1 hs).symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u')) =
        X.piU u' ((γ : X.B.I.GA).1)⁻¹ := by
      ext v; rfl
    show ((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) •
        (chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
          ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ : X.B.I.GA)⁻¹)) •
          (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
           OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf t) (X.Wu u) (X.Wu u')
            (t.rep.1.1.1 * ((γ : X.B.I.GA).1)⁻¹))) = _
    rw [eχ, ooR_holds D X u u' γ (FundOf t) t.rep.1.1.1, hU]
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp]

end Main

end Formalism.L2.SG.Pf.SatGramActR
