import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapStep
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPfA
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

set_option maxHeartbeats 1000000 in

theorem invLiftCondition : InvLiftStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hπ T h' hh' hT hJ c
  haveI := ((HW l).W K 1 LL hG).ddTowO T
  have hNL : NinLam ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' :=
    ninlam_pf D HW F Cm CA CB CK hA l hl K LL hG π' E hπ T h' hT hJ
  rcases le_or_gt (MK l K h') 1 with hM | hM
  · refine ⟨fun w hw => ⟨((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ^ sigA l (sK l K) h' • w, ?_, ?_⟩,
      fun wb _ hwb => gradNPf_PiNS_anti _ T π' hM hwb⟩
    · obtain ⟨hwL, hwγ⟩ := (mem_InvS _ T π' _ h' 1 c w).1 hw
      refine (mem_InvS _ T π' _ h' _ c _).2 ⟨Submodule.smul_mem _ _ hwL, ?_⟩
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ (gradNPf_PiNS_anti _ T π' hM hwγ)
    · rw [sub_self]
      exact Submodule.zero_mem _
  have hs : 1 ≤ sK l K := by
    by_contra h0
    have h0' : sK l K = 0 := by omega
    have : MK l K h' = 0 := by simp [MK, h0']
    omega
  obtain ⟨f, t, x, u, hu, hxu, hf, ht, hEE, hπΔ, hγN, hK, hprod⟩ :=
    gradNPf_hyps D HW F Cm hA.1 l hl K LL hG π' E hπ T hT hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨a, ha⟩ := hprod (MK l K h' - 1)
  have hM1 : MK l K h' - 1 + 1 = MK l K h' := by omega
  rw [hM1] at ha
  have hσ : sigA l (sK l K) h' = MK l K h' - 1 + padicValNat l (MK l K h' - 1).factorial := rfl

  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h0
    have hv := (D.loc l).v_l LL
    rw [h0, AddValuation.map_zero] at hv
    exact absurd hv (by simp)
  have hℓ : ∀ c : ↥(OL LL), (l : ↥(OL LL)) * c = 0 → c = 0 := by
    intro c hc
    have h1 := congrArg (algebraMap ↥(OL LL) ↥LL.1) hc
    rw [map_mul, map_natCast, map_zero] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left hl0
    exact (injective_iff_map_eq_zero (algebraMap ↥(OL LL) ↥LL.1)).1 Subtype.val_injective c h2

  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := hA.1 l K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, -, hm₀⟩, -⟩ := h9W T hT hs1 hp
  obtain ⟨⟨r, b, hbΔ, huniq, -⟩, -⟩ := hm₀
  obtain ⟨w, hw⟩ := hπ.2.2.1
  have hnz : ∀ y : ℕ, 1 ≤ y → y < MK l K h' → ∀ r₀ ∈ ((HW l).W K 1 LL hG).N T,
      ∀ d ∈ ((HW l).W K 1 LL hG).N T, ((x ^ sK l K) ^ y - 1) • r₀ = π' • d →
      ∃ e ∈ ((HW l).W K 1 LL hG).N T, r₀ = π' • e := by
    intro y hy1 hyM r₀ hr₀ d hd hrd
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun y => (x ^ sK l K) ^ y - 1)
      (Finset.mem_Ico.2 ⟨hy1, hyM⟩)
    rw [hq] at ha
    refine invLiftPf_nzd _ T π' w (sK l K) w.isUnit hw (l : ↥(OL LL)) hℓ r b
      (fun j => (hbΔ j).1) huniq (MK l K h' - 1 + padicValNat l (MK l K h' - 1).factorial) r₀
      ((a * q) • d) hr₀ ?_ ?_
    · rw [← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))]
      exact Submodule.smul_mem _ _ hd
    · rw [ha, mul_comm ((x ^ sK l K) ^ y - 1) q, ← mul_assoc, mul_smul, hrd,
        ← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (a * q) (π' • d),
        ← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (a * q) d, smul_smul, smul_smul,
        mul_comm]
  have hpσ : (((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ^ sigA l (sK l K) h') =
      a * ∏ y ∈ Finset.Ico 1 (MK l K h'), ((x ^ sK l K) ^ y - 1) := by
    rw [hpl, hσ]
    exact ha
  have hGr : GradN ((HW l).W K 1 LL hG) T π' (sigA l (sK l K) h') (MK l K h') :=
    gradNPf_local _ T π' f t (x ^ sK l K) hf ht hEE hπΔ hγN hK _ _ (by omega) a hpσ
  refine ⟨invLiftPf_lift _ T π' _ h' _ _ c hGr hNL, fun wb hwb hwb1 => ?_⟩
  exact invLiftPf_inj _ T π' f t (x ^ sK l K) hf ht hEE hπΔ hγN hK _ hnz wb hwb1
    ((mem_InvS _ T π' _ h' _ c wb).1 hwb).2

end Formalism.MainNotions.N.Ln34

end
