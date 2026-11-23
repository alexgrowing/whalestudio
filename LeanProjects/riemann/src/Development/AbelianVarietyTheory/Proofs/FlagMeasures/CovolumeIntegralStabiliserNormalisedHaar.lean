import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartCG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LatBAsm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StMatSpec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatEqOfIndep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StMatIntIff
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.Cov0

open Formalism.L2.SG.RealObj Formalism.L2.S.Pv.Chart Formalism.MainNotions.S.ThB Formalism.L2.SG.LocWSOf in

theorem chart_of {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u')
    (w : Point D.host.E (D.R.rS + 1)) (γw s s' : X.B.I.Ginf) (hrep : IsPtRep X u u' w γw) (hs : s ∈ X.SinfU u)
    (hs' : s' ∈ X.SinfU u') (hpt : t.pt.1 = s * γw * s'⁻¹) :
    ∃ BX : FreeE w → (FreeE w → ℂ) → (FreeE w → ℂ) → ℂ,
        (∀ p, Measurable (fun z : (FreeE w → ℂ) × (FreeE w → ℂ) => BX p z.1 z.2)) ∧
        (∀ p (x x' y y' : FreeE w → ℂ), (∀ q, Formalism.L2.SG.NGCut.StabilizerCovolume.ht q < Formalism.L2.SG.NGCut.StabilizerCovolume.ht p →
          x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y') ∧
        (∀ p (x : FreeE w → ℂ), BX p x 0 = 0) ∧
        Measurable (stCoord X u' w γw) ∧
        MeasurableSet (StInf X u u' γw) ∧
        Set.InjOn (stCoord X u' w γw) (StInf X u u' γw) ∧
        (∀ x, ∃ z ∈ StInf X u u' γw, stCoord X u' w γw z = x) ∧
        (∀ z₁ ∈ StInf X u u' γw, ∀ z₂ ∈ StInf X u u' γw,
          z₁ * z₂ ∈ StInf X u u' γw ∧
          stCoord X u' w γw (z₁ * z₂) =
            Formalism.L2.SG.NGCut.SplitEmbedding.lawX BX (stCoord X u' w γw z₁) (stCoord X u' w γw z₂)) ∧
        (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, s⁻¹ * r * s ∈ StInf X u u' γw) := by
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hτ : ∀ v : InfinitePlace X.B.I.F, ∃ τ, vOf X τ = v := fun v => ⟨X.pl v, X.pl.symm_apply_apply v⟩
  have hpl : ∀ z ∈ StInf X u u' γw, ∀ v, z v ∈ Formalism.L2.SG.NGPin.StV X u u' γw v := by
    intro z hz v
    rw [Formalism.L2.SG.NGPin.stInf_eq_pi] at hz
    exact hz v (Set.mem_univ _)
  refine ⟨BX, fun p => BX_measurable p, fun p x x' y y' h => BX_lower p x x' y y' h, fun p x => BX_zero p x,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Formalism.L2.SG.NGPin.stCoord_eq]
    refine measurable_pi_lambda _ fun v => ?_
    obtain ⟨τ, rfl⟩ := hτ v
    exact (stCoordV_meas C u' w γw τ).comp (measurable_pi_apply _)
  · rw [Formalism.L2.SG.NGPin.stInf_eq_pi]
    exact MeasurableSet.univ_pi fun v => (isClosed_stV X u u' γw v).measurableSet
  · intro z₁ h₁ z₂ h₂ heq
    rw [Formalism.L2.SG.NGPin.stCoord_eq] at heq
    funext v
    obtain ⟨τ, rfl⟩ := hτ v
    exact stCoordV_inj C u u' w γw τ hrep (hpl z₁ h₁ _) (hpl z₂ h₂ _) (congrFun heq (vOf X τ))
  · intro x
    have hex : ∀ v, ∃ y ∈ Formalism.L2.SG.NGPin.StV X u u' γw v,
        Formalism.L2.SG.NGPin.stCoordV X u' w γw v y = x v := by
      intro v
      obtain ⟨τ, rfl⟩ := hτ v
      exact stCoordV_surj C u u' w γw τ hrep (x (vOf X τ))
    choose y hy hyx using hex
    refine ⟨y, ?_, ?_⟩
    · rw [Formalism.L2.SG.NGPin.stInf_eq_pi]; exact fun v _ => hy v
    · rw [Formalism.L2.SG.NGPin.stCoord_eq]; funext v; exact hyx v
  · intro z₁ h₁ z₂ h₂
    refine ⟨?_, ?_⟩
    · have hN := Formalism.L2.SG.Pf.psiInfChar_holds D X u
      have hN' := Formalism.L2.SG.Pf.psiInfChar_holds D X u'
      refine ⟨(hN.2.1 _ h₁.1 _ h₂.1).1, ?_⟩
      have e : γw⁻¹ * (z₁ * z₂) * γw = (γw⁻¹ * z₁ * γw) * (γw⁻¹ * z₂ * γw) := by group
      rw [e]
      exact (hN'.2.1 _ h₁.2 _ h₂.2).1
    · rw [Formalism.L2.SG.NGPin.stCoord_eq]
      funext v p
      exact stCoordV_mul X v (hpl z₁ h₁ v) (hpl z₂ h₂ v) p
  · intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    refine ⟨?_, ?_⟩
    · have := Formalism.L2.SG.Pf.FormTranspose.sinf_conj X u (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u hs) hr1
      simpa only [inv_inv] using this
    · have hγ : γw = s⁻¹ * t.pt.1 * s' := by rw [hpt]; group
      have := Formalism.L2.SG.Pf.FormTranspose.sinf_conj X u' (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u' hs') hr2
      rw [hγ]
      convert this using 1
      group

end GlobalTheory.HL.Cov0

end

noncomputable section
namespace GlobalTheory.HL.Cov0

theorem const_entry : ∀ (D : D7) (X : HidaSetting D) (h : ℕ), ddS D ≠ 0 ∧ (D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (InfinitePlace X.B.I.F) * ((FractionalIdeal.absNorm (ddS D ^ (-(h : ℤ))) : ℚ) : ℝ) * 2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * √|(discr D.host.E : ℝ)| * ((D.host.rdE : ℝ) ^ h) ^ (2 * Fintype.card (InfinitePlace X.B.I.F)) = ((X.B.g : ℝ) ^ D.R.f)⁻¹ := by
  intro D X h
  have hrd : 0 < D.host.rdE := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
  have hN := GlobalTheory.RealPlaces.absNorm_ddS D
  have hdd : ddS D ≠ 0 := by
    intro h0
    rw [h0, map_zero, Rat.cast_zero] at hN
    exact (pow_pos hrd _).ne' hN.symm
  refine ⟨hdd, ?_⟩
  rw [Formalism.L2.SG.LatBAsm.factor_eq X _ h, map_zpow₀, Rat.cast_zpow, hN]
  have hg : (0 : ℝ) < X.B.g := by
    rw [X.g_eq]
    exact_mod_cast Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  rw [zpow_neg, zpow_natCast, ← pow_mul]
  field_simp

end GlobalTheory.HL.Cov0
end

noncomputable section
namespace GlobalTheory.HL.Cov0

theorem grp_conj {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T} {F0' : LFlag (VS D) D.R.rS T'}
    {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}
    (c : GCoord Z F0 F0' FP G) (ρ t n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    c.grp (ρ * t) (t⁻¹ * n * t) = c.grp ρ n := LinearEquiv.ext fun x => by
  simp only [GCoord.grp, LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.symm_trans_apply]
  show c.e (ρ (t (t.symm (n (t (t.symm (ρ.symm (c.e.symm x)))))))) = _
  simp

theorem realPoints_integralIsometries_subset_stabilizer : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, c.grp ρ n ∈ G.K0 → (∃ x, RatLink X x n) ∧ ∀ x, RatLink X x n → x.1 ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv hrel n hn
  have hgrp := GlobalTheory.HL.GrpCoord.grp_coords D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv
  have hL := GlobalTheory.RatIsomPoint.ratLink_points D X
  have hN : c.grp ρ n ∈ G.N := fun p => by
    obtain ⟨g', hg', hext⟩ := hn p
    exact ⟨g', hg'.1.1.1, hext⟩
  have hN' : c.grp ρ n ∈ G.N' := fun p => by
    obtain ⟨g', hg', hext⟩ := hn p
    exact ⟨g', hg'.1.1.2, hext⟩
  have hnR : n ∈ NRat (lf D (X.Fu u)) := (hgrp.1 n).2 hN
  have hmR : t₀.lin⁻¹ * n * t₀.lin ∈ NRat (lf D (X.Fu u')) :=
    (hgrp.2.1 _).2 (by rw [grp_conj]; exact hN')
  obtain ⟨x0, hx0, -⟩ := hL.1 n hnR.1
  refine ⟨⟨x0, hx0⟩, fun x hx => ⟨(hL.2.2 u x n hx).1.1 hnR, ?_⟩⟩
  have htl : RatLink X t₀.pt t₀.lin := t₀.rep.2.1
  have h1 := (hL.2.1 _ _ _ _ ((hL.2.1 _ _ _ _ htl htl).2.1) hx).1
  have h2 := (hL.2.1 _ _ _ _ h1 htl).1
  exact (hL.2.2 u' _ _ h2).1.1 hmR

end GlobalTheory.HL.Cov0
end

noncomputable section
namespace GlobalTheory.HL.Cov0

open Formalism.L2.SG.NGCut.SplitEmbedding Formalism.L2.SG.NGCut.StabilizerCovolume Formalism.L2.SG.RealObj in

theorem covolume_integralStabiliser_normalisedHaar_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ μR, Formalism.L2.SG.VolPin.IsPinnedR t₀ w μR → ∃ K : Set X.B.I.Ginf, (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀, ∃! s, s ∈ realPts X {σ | c.grp ρ σ ∈ G.K0} ∧ s * y ∈ K) ∧ μR K = ENNReal.ofReal (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv hrel μR hPin
  obtain ⟨γw, s, s', μw, hIs, hs, hs', hpt, hHaar, hmap, rfl⟩ := hPin
  obtain ⟨BX, hBm, hBd, hB0, hstm, hStm, hinj, hsurj, hmul, hconj⟩ :=
    chart_of X Y u u' t₀ w γw s s' hIs hs hs' hpt
  have hTC := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have : IsEmpty {w : InfinitePlace D.host.E // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1)) w.2⟩
  obtain ⟨σι, hφ⟩ := Formalism.L2.SG.LatBAsm.exists_sigma X
  set St := StInf X u u' γw with hStdef
  set sc := stCoord X u' w γw with hscdef
  set φ := Formalism.L2.SG.Pf.VolPinAsm.phiV X with hφdef
  set Γ := realPts X {σ | c.grp ρ σ ∈ G.K0} with hΓdef
  have hT1 := realPoints_integralIsometries_subset_stabilizer D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv hrel
  have hΓR : ∀ y ∈ Γ, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := by
    rintro y ⟨x, n, hx, rfl, hn⟩
    exact (hT1 n hn).2 x hx
  have hgrp_inv : ∀ n, c.grp ρ n⁻¹ = (c.grp ρ n)⁻¹ := fun n => LinearEquiv.ext fun x => rfl
  have hΓinv : ∀ y ∈ Γ, y⁻¹ ∈ Γ := by
    rintro y ⟨x, n, hx, rfl, hn⟩
    refine ⟨x⁻¹, n⁻¹, ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x x n n hx hx).2.1, rfl, ?_⟩
    show c.grp ρ n⁻¹ ∈ G.K0
    rw [hgrp_inv]; exact G.K0.inv_mem hn
  have hgSt : ∀ y ∈ Γ, s⁻¹ * y * s ∈ St := fun y hy => hconj _ (hΓR y hy)

  obtain ⟨σ, hσn, A, hA, hcoord⟩ :=
    GlobalTheory.HL.CovDict.dict_coords D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv hrel γw s s' hIs hs hs' hpt
  have hT4 := GlobalTheory.HL.StIntLat.stMat_int_iff D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c
  have hrd : 0 < (D.host.rdE : ℝ) := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  have hσ0 : ∀ p, σ p ≠ 0 := fun p h => by
    have := hσn p
    rw [h, norm_zero] at this
    exact (pow_pos hrd _).ne' this.symm
  have hAu : ∀ v, Formalism.L2.SG.NGCut.StabilizerCovolume.IsUni ht (A v) := fun v x x' p hxx => hA v x x' p hxx
  choose B hAB hBA hBu using fun v => uni_inv ht (hAu v)
  have hdd : ddS D ≠ 0 := (const_entry D X 0).1
  let I : FreeE w → (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ :=
    fun p => Units.mk0 (ddS D ^ (-((ht p : ℕ) : ℤ))) (zpow_ne_zero _ hdd)
  let Λ : FreeE w → AddSubgroup D.host.E :=
    fun p => ((I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup
  let τ : FreeE w → (InfinitePlace X.B.I.F → FreeE w → ℂ) → (InfinitePlace X.B.I.F → ℂ) :=
    fun p x v => x v p - B v (x v) p
  let Aset : FreeE w → AddSubgroup (InfinitePlace X.B.I.F → ℂ) := fun p => (Λ p).map (embS φ (σ p))
  have hτ : ∀ p (x x' : InfinitePlace X.B.I.F → FreeE w → ℂ),
      (∀ q, ht q < ht p → ∀ v, x v q = x' v q) → τ p x = τ p x' := by
    intro p x x' hxx
    funext v
    have h1 := hBu v (x v) (x' v) p fun r hr => hxx r hr v
    show x v p - B v (x v) p = x' v p - B v (x' v) p
    linear_combination -h1
  have hdiff : ∀ p x, (fun v => x v p) - τ p x = fun v => B v (x v) p := by
    intro p x; funext v; show x v p - (x v p - B v (x v) p) = B v (x v) p; ring
  have hmemiff : ∀ p (z : InfinitePlace X.B.I.F → ℂ),
      (fun v => σ p * z v) ∈ Aset p ↔ z ∈ (Λ p).map (embS φ 1) := by
    intro p z
    simp only [Aset, AddSubgroup.mem_map]
    constructor
    · rintro ⟨a, ha, hae⟩
      refine ⟨a, ha, ?_⟩
      funext v
      have := congrFun hae v
      simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at this ⊢
      exact mul_left_cancel₀ (hσ0 p) this
    · rintro ⟨a, ha, hae⟩
      refine ⟨a, ha, ?_⟩
      funext v
      have := congrFun hae v
      simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at this ⊢
      rw [this]
  have hset : ∀ x, (∀ p, (fun v => x v p) - τ p x ∈ Aset p) ↔ ∃ y ∈ Γ, x = sc (s⁻¹ * y * s) := by
    intro x
    constructor
    · intro hx
      set y0 : InfinitePlace X.B.I.F → FreeE w → ℂ := fun v p => (σ p)⁻¹ * B v (x v) p with hy0
      have hy0m : ∀ p, (fun v => y0 v p) ∈ (Λ p).map (embS φ 1) := by
        intro p
        rw [← hmemiff]
        have := hx p
        rw [hdiff] at this
        convert this using 1
        funext v
        show σ p * ((σ p)⁻¹ * B v (x v) p) = B v (x v) p
        field_simp [hσ0 p]
      obtain ⟨g, hg, hgy⟩ := (hT4 y0).2 hy0m
      set e := ρ.trans c.e with he
      set n : (VS D).V ≃ₗ[D.host.E] (VS D).V := (e.trans g).trans e.symm with hn
      have hgn : c.grp ρ n = g := by
        apply LinearEquiv.ext; intro z
        show e (e.symm (g (e (e.symm z)))) = g z
        simp
      obtain ⟨x0, hx0⟩ := (hT1 n (by rw [hgn]; exact hg)).1
      refine ⟨x0.1, ⟨x0, n, hx0, rfl, by show c.grp ρ n ∈ G.K0; rw [hgn]; exact hg⟩, ?_⟩
      funext v
      rw [show sc (s⁻¹ * x0.1 * s) v = _ from hcoord x0 n hx0 (by rw [hgn]; exact hg) v, hgn]
      have : (fun p => σ p * φ v (GlobalTheory.HL.TraceConjugationCover.stMat G g p.1.1 p.1.2)) = B v (x v) := by
        funext p
        have := congrFun (congrFun hgy v) p
        simp only [hy0] at this
        rw [← this]
        field_simp [hσ0 p]
      rw [this, hAB v]
    · rintro ⟨y, ⟨x0, n, hx0, rfl, hn⟩, rfl⟩
      intro p
      rw [hdiff]
      have hxv : ∀ v, sc (s⁻¹ * x0.1 * s) v = A v (fun p => σ p * φ v (GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) p.1.1 p.1.2)) :=
        fun v => hcoord x0 n hx0 hn v
      have e1 : (fun v => B v (sc (s⁻¹ * x0.1 * s) v) p) =
          fun v => σ p * φ v (GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) p.1.1 p.1.2) := by
        funext v; rw [hxv v, hBA v]
      rw [e1, hmemiff]
      exact (hT4 _).1 ⟨c.grp ρ n, hn, rfl⟩ p

  have hBd' : ∀ p (x x' y y' : FreeE w → ℂ), (∀ q, ht q < ht p → x q = x' q ∧ y q = y' q) →
      BX p x y = BX p x' y' := hBd
  have hinv : ∀ γ, (∀ p, (fun v => γ v p) - τ p γ ∈ Aset p) → ∃ γ', (∀ p, (fun v => γ' v p) - τ p γ' ∈ Aset p) ∧
      ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x := by
    intro γ hγ
    obtain ⟨y, hy, rfl⟩ := (hset γ).1 hγ
    refine ⟨sc (s⁻¹ * y⁻¹ * s), (hset _).2 ⟨y⁻¹, hΓinv y hy, rfl⟩, fun x => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hsurj x
    have hg1 := hgSt y hy
    have hg2 := hgSt y⁻¹ (hΓinv y hy)
    have h1 := hmul _ hg1 z hz
    have h1' := hmul _ hg2 z hz
    constructor
    · have h2 := hmul _ hg2 _ h1.1
      rw [← h1.2, ← h2.2]
      congr 1; group
    · have h2 := hmul _ hg1 _ h1'.1
      rw [← h1'.2, ← h2.2]
      congr 1; group

  have hfd : ∀ p, ∃ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F ∧
      ∀ v, ∃! b : Aset p, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F := by
    intro p
    obtain ⟨F, hF, hFd⟩ := exists_fd D.host.E (InfinitePlace X.B.I.F) φ σι hφ (I p) (Λ p)
      (fun a ha => ha) (by simp [Λ]) (σ p) (hσ0 p)
    refine ⟨F, hF, fun v => ?_⟩
    obtain ⟨a, ha, hau⟩ := hFd v
    refine ⟨⟨embS φ (σ p) a, AddSubgroup.mem_map_of_mem _ a.2⟩, ha, ?_⟩
    rintro ⟨y, hy⟩ hyF
    obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 hy
    have := hau ⟨a', ha'⟩ hyF
    apply Subtype.ext
    show embS φ (σ p) a' = embS φ (σ p) a
    rw [show a' = (a : D.host.E) from congrArg Subtype.val this]
  choose F hF hFd using hfd
  set K' : Set (InfinitePlace X.B.I.F → FreeE w → ℂ) := {y | ∀ p, (fun v => y v p) ∈ F p} with hK'def
  have hK'm : MeasurableSet K' := by
    rw [hK'def, Set.ofPred_forall]
    exact MeasurableSet.iInter fun p =>
      (measurable_pi_lambda _ fun v => (measurable_pi_apply p).comp (measurable_pi_apply v)) (hF p)
  have hKd := box_fundX ht BX hBd' τ hτ Aset F hFd
  have hcov := pi_measure_eq_prod_absNorm_mul_sqrt_discr D.host.E (InfinitePlace X.B.I.F) φ σι hφ (FreeE w) ht BX hBm hBd' hB0
    (D.host.ka / (X.B.g : ℝ) / Real.pi) (by
      have e : D.host.ka = Real.pi / (D.host.rdE / 2) := rfl
      rw [e]
      exact div_nonneg (div_nonneg (div_nonneg Real.pi_pos.le (div_nonneg hrd.le zero_le_two)) (Nat.cast_nonneg _))
        Real.pi_pos.le) I Λ (fun p a ha => ha) (fun _ => 1) (by intro p; simp [Λ])
    (fun _ => one_ne_zero) σ hσ0 τ hτ hinv K' hK'm hKd

  have hQm : Measurable (fun y : X.B.I.Ginf => s⁻¹ * y * s) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  set KA := (fun y : X.B.I.Ginf => s⁻¹ * y * s) ⁻¹' (St ∩ sc ⁻¹' K') with hKAdef
  have hKAm : MeasurableSet KA := hQm (hStm.inter (hstm hK'm))
  refine ⟨KA, ⟨hKAm, fun y hy => ?_⟩, ?_⟩
  · set z := s⁻¹ * y * s with hzdef
    have hz : z ∈ St := hconj _ hy
    obtain ⟨γ, ⟨hγΓ, hγK⟩, hγu⟩ := hKd (sc z)
    obtain ⟨y0, hy0, rfl⟩ := (hset γ).1 hγΓ
    refine ⟨y0, ⟨hy0, ?_⟩, ?_⟩
    · show s⁻¹ * (y0 * y) * s ∈ St ∩ sc ⁻¹' K'
      have e : s⁻¹ * (y0 * y) * s = (s⁻¹ * y0 * s) * z := by rw [hzdef]; group
      rw [e]
      have h1 := hmul _ (hgSt y0 hy0) z hz
      exact ⟨h1.1, by show sc _ ∈ K'; rw [h1.2]; exact hγK⟩
    · rintro y1 ⟨hy1, hy1K⟩
      have hK2 : s⁻¹ * (y1 * y) * s ∈ St ∩ sc ⁻¹' K' := hy1K
      have e : s⁻¹ * (y1 * y) * s = (s⁻¹ * y1 * s) * z := by rw [hzdef]; group
      rw [e] at hK2
      have h1 := hmul _ (hgSt y1 hy1) z hz
      have hin : lawX BX (sc (s⁻¹ * y1 * s)) (sc z) ∈ K' := by rw [← h1.2]; exact hK2.2
      have heq := hγu (sc (s⁻¹ * y1 * s)) ⟨(hset _).2 ⟨y1, hy1, rfl⟩, hin⟩
      have hgg : s⁻¹ * y1 * s = s⁻¹ * y0 * s := hinj (hgSt y1 hy1) (hgSt y0 hy0) heq
      have := congrArg (fun g => s * g * s⁻¹) hgg
      simpa [mul_assoc] using this
  · have hs1m : Measurable (fun y : X.B.I.Ginf => s * y * s⁻¹) :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable
    rw [Measure.map_apply hs1m hKAm]
    have hset' : (fun y : X.B.I.Ginf => s * y * s⁻¹) ⁻¹' KA = St ∩ sc ⁻¹' K' := by
      ext y
      simp only [Set.mem_preimage, hKAdef]
      have e : s⁻¹ * (s * y * s⁻¹) * s = y := by group
      rw [e]
    rw [hset', Set.inter_comm, measure_inter_conull hHaar.2.2.1, ← Measure.map_apply hstm hK'm, hmap]
    unfold Formalism.L2.SG.RealObj.muStab
    rw [hcov]
    have hterm : ∀ p : FreeE w, ENNReal.ofReal ((D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (InfinitePlace X.B.I.F) *
        (((fun _ => 1 : FreeE w → ℕ) p : ℕ) : ℝ) *
        ((FractionalIdeal.absNorm ((I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : ℚ) : ℝ) *
        2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * √|(discr D.host.E : ℝ)| *
        ‖σ p‖ ^ (2 * Fintype.card (InfinitePlace X.B.I.F))) = ENNReal.ofReal (((X.B.g : ℝ) ^ D.R.f)⁻¹) := by
      intro p
      congr 1
      have h5 := (const_entry D X (ht p)).2
      rw [hσn p]
      simp only [I, Units.val_mk0, Nat.cast_one, mul_one]
      exact h5
    rw [Finset.prod_congr rfl fun p _ => hterm p, Finset.prod_const, Finset.card_univ,
      ← ENNReal.ofReal_pow (by positivity), inv_pow, ← pow_mul]

end GlobalTheory.HL.Cov0
end
