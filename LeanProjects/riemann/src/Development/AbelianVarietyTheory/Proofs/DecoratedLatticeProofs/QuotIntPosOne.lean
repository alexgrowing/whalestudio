import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotIntCellsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents app_coe)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale volR)

noncomputable section
namespace GlobalTheory.PosOneCell

section Lemmas
variable {X : Type} [TopologicalSpace X] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem app_smul (l : SB X →ₗ[ℂ] V) (z : ℂ) (f : X → ℂ) : app l (z • f) = z • app l f := by
  by_cases hz : z = 0
  · subst hz
    have : app l (0 : X → ℂ) = 0 := by
      rw [show (0 : X → ℂ) = ((0 : SB X) : X → ℂ) from rfl, app_coe, map_zero]
    rw [zero_smul, zero_smul, this]
  · by_cases hf : f ∈ SB X
    · have hzf : z • f ∈ SB X := (SB X).smul_mem z hf
      simp only [app, hf, hzf, dif_pos]
      rw [← map_smul]
      rfl
    · have hzf : z • f ∉ SB X := fun h => hf (((SB X).smul_mem_iff hz).1 h)
      simp [app, hf, hzf]

theorem app_zero (l : SB X →ₗ[ℂ] V) : app l (0 : X → ℂ) = 0 := by
  rw [show (0 : X → ℂ) = ((0 : SB X) : X → ℂ) from rfl, app_coe, map_zero]

end Lemmas

theorem quotInt_posOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (_ : 1 ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (m : Measure (GL n k)) [m.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (L : Level (GL (n ⊕ Fin c) k)) (_ : IsCO L.J) (_ : μG L.J = 1) (b : GL (n ⊕ Fin c) k) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ 1 σ B) (F : A) (_ : ∀ j : L.J, σ (j : GL (n ⊕ Fin c) k) F = (L.lam j : ℂ) • F) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (_ : ∀ j : L.J, om μ 1 (j : GL (n ⊕ Fin c) k) Φ.1 = (((L.lam j)⁻¹ : ℂˣ) : ℂ) • Φ.1) (h' : GL (n' ⊕ Fin (c + 1)) k) (T : Finset (GL (n ⊕ Fin c) k)) (_ : Covers 1 L.J T fun h => flat ψ ν μ Φ.1 h' h), IsQuotInt ν (rescale ν b m) μG 1 (tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1)) (∑ h ∈ T, (((m (prX (Cgrp L.J h))).toReal⁻¹ : ℝ) : ℂ) * app B (xi ψ ν μ Φ.1 L.J b h' h) (σ h F)) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c hc ψ hψ hψc ν hν μ hμ m _ μG _ L hJ hJ1 b A _ _ σ hσ B hB F hF Φ hΦ h' T hT
  haveI : ν.IsAddHaarMeasure := hν.1
  have hr := volN_stabLat (n := n) (c := c) ν b
  haveI : (rescale ν b m).IsHaarMeasure := by
    unfold rescale
    exact Measure.IsHaarMeasure.smul m (ENNReal.inv_ne_zero.2 (ENNReal.toReal_pos_iff.1 hr).2.ne)
      (ENNReal.inv_ne_top.2 (ENNReal.toReal_pos_iff.1 hr).1.ne')
  have hflat : ∀ h, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h = app B (flat ψ ν μ Φ.1 h' h) (σ h F) := by
    intro h
    simp only [tInt, flat]
    rw [← om_mul]
    simp
  have hSB : ∀ h, flat ψ ν μ Φ.1 h' h ∈ SB (Matrix n n' k) := fun h =>
    (GlobalTheory.RootEx.opE_SB_and_linear k n n' c 1 ψ hψ ν).1 _ (om_mem_SB μ h' h Φ.2)
  have hinv : ∀ h, ∀ j ∈ L.J, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) (h * j) = tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h := by
    intro h j hj
    have hΦj : om μ 1 j Φ.1 = (((L.lam ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) • Φ.1 := hΦ ⟨j, hj⟩
    have hFj : σ j F = (L.lam ⟨j, hj⟩ : ℂ) • F := hF ⟨j, hj⟩
    have e : flat ψ ν μ Φ.1 h' (h * j) = (((L.lam ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) • flat ψ ν μ Φ.1 h' h := by
      unfold flat
      rw [show om μ h' (h * j) Φ.1 = om μ h' h (om μ 1 j Φ.1) by rw [← om_mul]; simp, hΦj,
        GlobalTheory.UnfoldedEntries.om_smul, GlobalTheory.UnfoldedEntries.opE_smul]
    rw [hflat, hflat, e, PosOneCell.app_smul, map_mul, Module.End.mul_apply, hFj, map_smul, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul]
  have hmod : ∀ (x : GL n k), ∀ u ∈ N k n c 1, ∀ h, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) (embX c x * u * h) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h := by
    intro x u hu h
    have e : flat ψ ν μ Φ.1 h' (embX c x * u * h) =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) •
          om μ 1 x ((ψ (-simpleSum u) : ℂ) • flat ψ ν μ Φ.1 h' h) := by
      unfold flat
      rw [show om μ h' (embX c x * u * h) Φ.1 = om μ 1 (embX c x) (om μ 1 u (om μ h' h Φ.1)) by
          rw [← om_mul, ← om_mul]; simp,
        (GlobalTheory.RootEx.opE_om_embX k n n' c 1 le_rfl hc ψ ν μ _).1,
        GlobalTheory.RootEx.opE_om_target_unipotent k n n' c 1 le_rfl hc ψ ν μ _ u hu]
    let Ψ : SB (Matrix n n' k) := ⟨flat ψ ν μ Φ.1 h' h, hSB h⟩
    let Ψ₁ : SB (Matrix n n' k) := ⟨om μ 1 x (flat ψ ν μ Φ.1 h' h), om_mem_SB μ 1 x (hSB h)⟩
    have a0 : app B (flat ψ ν μ Φ.1 h' h) = B Ψ := app_coe B Ψ
    have a1 : app B (om μ 1 x (flat ψ ν μ Φ.1 h' h)) = B Ψ₁ := app_coe B Ψ₁
    rw [hflat, hflat, e, GlobalTheory.UnfoldedEntries.om_smul, smul_smul, PosOneCell.app_smul, map_mul, map_mul,
      Module.End.mul_apply, Module.End.mul_apply, a0, a1, LinearMap.smul_apply, hB.2 x Ψ Ψ₁ _ rfl,
      hB.1 Ψ u hu, smul_eq_mul]
    have key : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
    have hp := GlobalTheory.RootEx.OpELevi.nabs_pos (Matrix.GeneralLinearGroup.det x)
    have rp : ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hp]
      congr 2
      ring
    linear_combination (B Ψ (σ h F)) * (((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ)) * key
      + (B Ψ (σ h F)) * rp
  have hcov : Covers 1 L.J T (tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1)) := by
    refine ⟨hT.1, fun h hh => hT.2 h ?_⟩
    intro h0
    apply hh
    simp only at h0
    rw [hflat, h0, PosOneCell.app_zero, LinearMap.zero_apply]
  obtain ⟨-, hiff⟩ := GlobalTheory.T.isQuotInt_cells_alt k n c 1 le_rfl hc ν (rescale ν b m) μG L.J hJ _ hinv hmod T hcov
  refine (hiff _).2 (Finset.sum_congr rfl fun h _ => ?_)
  obtain ⟨-, -, -, -, hm⟩ := (GlobalTheory.UnfoldedEntries.entries_wellDefined k ψ ν hψc hν).2.2.1 n c hc L.J hJ h
  obtain ⟨-, -, -, hresc, -⟩ := hm m inferInstance
  have hvc : volCell ν (rescale ν b m) 1 L.J h = volR ν (rescale ν b m) (Cgrp L.J h) := by
    unfold volCell volR
    refine lintegral_congr fun g => ?_
    congr 1
    ext u
    simp only [Set.mem_setOf_eq, mem_Cgrp]
    refine ⟨fun H => ⟨?_, H⟩, fun H => H.2⟩
    exact (R k n c 1).mul_mem (Subgroup.mem_sup_left (MonoidHom.mem_range.2 ⟨g, rfl⟩)) (Subgroup.mem_sup_right u.2)
  have hxi : xi ψ ν μ Φ.1 L.J b h' h = (((volNat ν b (Cgrp L.J h))⁻¹ : ℝ) : ℂ) • flat ψ ν μ Φ.1 h' h := rfl
  rw [hxi, PosOneCell.app_smul, LinearMap.smul_apply, smul_eq_mul, hflat, hvc, hresc b, hJ1, ENNReal.toReal_one]
  push_cast
  ring

end GlobalTheory.PosOneCell
