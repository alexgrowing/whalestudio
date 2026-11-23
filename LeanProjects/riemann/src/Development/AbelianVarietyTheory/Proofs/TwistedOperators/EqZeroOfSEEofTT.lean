import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankComapOfLeRange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModelStatement
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.SeeIsoRow

variable {D : D7} {S : D.what₂.Tau → SPar}

theorem sEEofTT_apply {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E) :
    sEEofTT M μ 𝓕 E St Gd ι t c T = conjHH St Gd (hE.choose_spec.2.choose T) := by
  unfold sEEofTT
  simp only [dif_pos hE]
  rfl

theorem norm_sq_sEEofTT {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E) :
    ‖sEEofTT M μ 𝓕 E St Gd ι t c T‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re := by
  have h := congrArg norm (sEEofTT_apply hE T)
  rw [LinearIsometry.norm_map] at h
  rw [h]
  exact (hE.choose_spec.2.choose_spec T).2

theorem eq_zero_of_sEEofTT {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E)
    (h : ‖sEEofTT M μ 𝓕 E St Gd ι t c T‖ = 0) : T = 0 := by
  have h1 := congrArg norm (sEEofTT_apply hE T)
  rw [LinearIsometry.norm_map] at h1
  have h2 : ‖hE.choose_spec.2.choose T‖ = 0 := h1.symm.trans h
  exact (LinearEquiv.map_eq_zero_iff _).1 (norm_eq_zero.1 h2)

theorem seeIso_row : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (hK : X.LevelSubgroupCharacter) (Zs : DefSub A3.fam3.amb3) (Dc : DefCols (A3.side3 F.P1 F.ψ1 Zs)) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX X)) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cS κS : ℝ) (uS : ℂ), R.toRealDat.IsModels → (R.toCx3 F).zs = Zs → F.Dc Zs = Dc → HEq (F.Sp Zs) (spOf (X := X) (twAt D.what₂.embLL A3.A.v0) Dc hK Gd wdD pw bR) → HEq sEE sEEc → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS → ‖uS‖ = 1 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) ((uS * (κS : ℂ)) • (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS) ⟨R.HE.e (Tw.out x), hx⟩)) → (0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), ‖(κ' : ℂ) • (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS) ⟨R.HE.e (Tw.out x), hx⟩‖ = ‖x‖) → ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H), R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) → RealDat.nP F.lv2 true * ‖sEEc x‖ ^ 2 = ‖x‖ ^ 2)) → (R.toCx3 F).SEEIso sEE := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X Gd hK Zs Dc wdD pw bR sEE sEEc ι tS cS κS uS hM hzs hDc hSp hh hE _ hDef hK'
  subst hzs
  subst hDc
  have hSp' := eq_of_heq hSp
  have hHE := hM.HE
  have hle := (GlobalTheory.T.goodRows_level_sub_principalLevel_hilbertModel R.toRealDat hM).1 (R.toRealDat.levR F.lv2 true)
  have key : ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H)
      (hx : R.HE.e (Tw.out x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)),
      ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ ^ 2 = cS * ‖x‖ ^ 2 := by
    intro x hx
    rw [norm_sq_sEEofTT hE]
    congr 1
    show (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e (Tw.out x)) (R.HE.e (Tw.out x))).re = ‖Tw.out x‖ ^ 2
    rw [← hHE.2.2]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (Tw.out x)
  have hex : ∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H)
      (hx : R.HE.e (Tw.out x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)),
      ‖(κ' : ℂ) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = ‖x‖ := by
    by_cases hc : 0 < cS
    · have hsp : 0 < Real.sqrt cS := Real.sqrt_pos.2 hc
      refine ⟨(Real.sqrt cS)⁻¹, inv_pos.2 hsp, fun x hx => ?_⟩
      have h1 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = Real.sqrt cS * ‖x‖ := by
        rw [← pow_left_inj₀ (norm_nonneg _) (mul_nonneg hsp.le (norm_nonneg _)) two_ne_zero, key x hx, mul_pow,
          Real.sq_sqrt hc.le]
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hsp).le, h1, ← mul_assoc,
        inv_mul_cancel₀ hsp.ne', one_mul]
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have h2 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ ^ 2 ≤ 0 := by
        rw [key x hx]
        exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) (sq_nonneg _)
      have h0 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = 0 :=
        pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _))
      have hT := eq_zero_of_sEEofTT hE _ h0
      have he0 : R.HE.e (Tw.out x) = 0 := congrArg Subtype.val hT
      have hx0 : Tw.out x = 0 := (map_eq_zero_iff _ hHE.1).1 he0
      rw [norm_smul, h0, mul_zero]
      show 0 = ‖Tw.out x‖
      rw [hx0, norm_zero]
  have hn := hK'.2 hex
  refine GlobalTheory.Mem.SJ.RowIso.clauses (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD pw bR (F.Sp (R.toCx3 F).zs)
    hSp' ((R.toCx3 F).EEl true) ((R.toCx3 F).nP true) sEE sEEc hh (fun e he => hn e he) (fun e he => ?_) ?_
  · refine (congrArg (fun y : Tw (twAt D.what₂.embLL A3.A.v0) (HHX X) =>
      ((Tw.out y : HHX X) : L2X X) ∈ goodSub X Gd) (hDef e he)).mpr ?_
    show (((uS * (κS : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out e), he⟩ : HHX X) : L2X X) ∈ goodSub X Gd
    rw [Submodule.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    unfold sEEofTT
    rw [dif_pos hE]
    exact (mem_EEC X Gd _).1 (hE.choose_spec.2.choose _).2
  · refine (GlobalTheory.Mem.SJ.RowIso.finrank_of_evalTieT hE).trans ?_
    refine Eq.symm ((GlobalTheory.Mem.SJ.RowIso.finrank_twSub (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0)
      ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e)).trans ?_)
    refine GlobalTheory.Mem.SJ.RowIso.finrank_comap_of_le_range _ hHE.1 _ ?_
    rw [hHE.2.1]
    exact hle

end GlobalTheory.Twist.SeeIsoRow
