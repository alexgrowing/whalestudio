import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastStepVectorLiftPairFlagLevelCharactersStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

namespace GlobalTheory.Chain.SourceLaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isLift_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsLevelLift V β L 1 1 := by
  unfold IsLevelLift
  refine ⟨Subgroup.one_mem _, ?_, ?_⟩
  · rw [map_one]
    exact Subgroup.one_mem _
  · rw [map_one]
    exact rTup_one

theorem levChi_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    levChi V β L 1 = 1 := by
  have h := (levChar D.sp.cm V.gram β L).map_one
  rw [levChar_apply] at h
  have h' : levFn β L 1 = 1 := h
  unfold levChi
  rw [map_one, h', Units.val_one]

theorem isLift_of_mem (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {κ : GA D V} (h : κ ∈ levG V β (flag1L L)) : IsLevelLift V β L 1 κ := by
  have hm := h
  unfold levG levA at hm
  rw [Subgroup.mem_inf, Subgroup.mem_comap, mem_lev] at hm
  obtain ⟨h1, h2, h3⟩ := hm
  exact ⟨h1, h2, Subgroup.mem_bot.mp h3⟩

private lemma levChi_flag1L_eq_levChi_flagL (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (κ : GA D V) :
    levChi V β (flag1L L) κ = levChi V β (flagL L) κ := by
  have e1 : ext1 (flag1L L).P.H (flag1L L).P.chi (rTup β (flag1L L) (finE V κ)) = 1 := by
    unfold ext1
    split_ifs <;> rfl
  have e2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := by
    unfold ext1
    split_ifs <;> rfl
  unfold levChi levFn
  rw [e1, e2]
  rfl

theorem law_of_pair {V W : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (β' : GL (Fin W.rank) (Lev.EAf D)) (L' : LevDat D.host.E ℂ W.rank) {X : Type} [AddCommGroup X] [Module ℂ X]
    {κ : GA D V} {u v : X}
    (h : (levChi V β (flagL L) κ)⁻¹ • u = (levChi W β' (flagL L') 1)⁻¹ • v) :
    u = levChi V β (flag1L L) κ • v := by
  have hne : levChi V β (flagL L) κ ≠ 0 := by
    unfold levChi
    exact Units.ne_zero _
  rw [levChi_one W β' (flagL L'), inv_one, one_smul] at h
  rw [levChi_flag1L_eq_levChi_flagL, ← h, smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem lawsOK : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → LawsOK R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hIs hθ hωY hωX hvY hvX
  have hInf : R.models_inf := hθ
  refine ⟨?_, ?_⟩
  · intro t k hk κ hκ
    have hl : IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) 1 κ := isLift_of_mem _ _ _ hκ
    have hl' := isLift_one (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv)
    have key := GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain R hIs hInf hωY hvY t k hk 1 κ 1 hl hl'
    have e : flag1L (R.datYt t k R.triv) = R.datYt t k R.triv := rfl
    have hlaw := law_of_pair (R.βY k) (R.datYt t k R.triv) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) key
    rw [e] at hlaw
    exact ⟨hl.1, hlaw⟩
  · intro t κ hκ
    have hl : IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) 1 κ :=
      isLift_of_mem _ _ _ hκ
    have hl' := isLift_one D.sp.X' R.βX (R.datXt t)
    have key := GlobalTheory.T.lastVector_lift_pair_flagLevel_characters R hIs hInf hωX hvX t 1 κ 1 hl hl'
    have e : flag1L (R.datYt t (D.R.m - 1) R.triv) = R.datYt t (D.R.m - 1) R.triv := rfl
    have hlaw := law_of_pair (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) R.βX (R.datXt t) key
    rw [e] at hlaw
    exact ⟨hl.1, hlaw⟩

end GlobalTheory.Chain.SourceLaw

end
