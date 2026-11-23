import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaQEmpty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumInvLeftMulTargetLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifiStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepVecLawBoth

set_option maxHeartbeats 1000000 in
open Classical in

theorem stepLevLawT (D : D7) (c : Com D) (hc : c.Is) (k : ℕ) (hk : k < D.R.m) (s s' : PiLocalization₂ D) (hs : s.Is c k)
    (hs' : s'.Is c (k + 1)) (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ))
    (hW : IsWeilDatumO c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) ω) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (f₀ f : WO s.V s'.V → ℂ)
    (hv : IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f) :
    ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ω (1, κ) f = (Lev.levChi s'.V s'.β s'.L κ)⁻¹ • f := by
  intro κ hκ
  obtain ⟨hr, ξ1, hL⟩ := hs.lev
  obtain ⟨hr', ξ2, hL'⟩ := hs'.lev
  rw [hL] at hv
  rw [hL'] at hκ ⊢
  have ea : s.V.rank = D.R.r + k * D.R.t := hs.rank
  have eb : s'.V.rank = D.R.r + (k + 1) * D.R.t := hs'.rank
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have he' : IsIdemSum e c.Pg := by rw [← Finset.union_empty c.Pg]; exact he
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified D c hc k hk
  have hlev : Lev.finE s'.V κ ∈ lev D.sp.cm s'.V.gram s'.β
      (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B) := hκ.2
  have sg : Lev.finE s.V 1 ∈ St s.β := by rw [map_one]; exact Subgroup.one_mem _
  have sh : Lev.finE s'.V κ ∈ St s'.β := parLev_St hlev.1
  have h1 := GlobalTheory.StepVecLaw.om_vac hW hs.sigOK hs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M)
    (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M) hs.selfDual hs'.selfDual hs.frame hs'.frame hf he'
    (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT (Subgroup.one_mem _) hκ.1 sg sh
  set H : ∀ PP : Pl D.host.E, GL (Fin s'.V.rank) (kP PP) := fun PP => redFn s'.β PP (Lev.finE s'.V κ) with hH
  have hPeq : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).P = c.P := by simp [Lev.datY]
  have hcg : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).cg = c.chi := by simp [Lev.datY]
  have hP : (fun PP : ↥c.Pg => upperLeftBlock hr' (H PP.1)) ∈ c.P.H := by
    have := hlev.2
    rw [hPeq] at this
    exact this
  have hBT : ∀ PP ∈ c.Pg, H PP ∈ blockTri (blkOf D.R.r D.R.t) := fun PP hPP => parLev_g hlev.1 hPP
  have h1' : ω (1, κ) f₀ = ((∏ PP ∈ c.Pg, (c.chi (k + 1) PP (GeneralLinearGroup.det (H PP)))⁻¹ : ℂˣ) : ℂ) • f₀ := by
    rw [h1]
    congr 2
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [map_one, redFn_one, MonoidHom.inv_apply, inv_one, one_mul, hH]
  have hoT := GlobalTheory.T.levelPlacesDatum_inv_left_mul_target_level D s.V.rank s'.V.rank D.R.r D.R.t k hr hr' ea eb c.Pg c.P c.chi ξ1 H hBT hP
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D c.ψ s.V s'.V _ _ ω hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D c.ψ hW.std s.V s'.V s.Λ s'.Λ hs.selfDual hs'.selfDual e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ 1 κ
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D s.V s'.V s.Λ s'.Λ s.β s'.β hs.selfDual hs'.selfDual hs.frame hs'.frame 1 κ sg sh) _
    ((((c.P.chi ⟨_, hP⟩ * ∏ PP ∈ c.Pg, ∏ i ∈ Finset.range (k + 1),
        c.chi (i + 1) PP (dBlk (blkOf D.R.r D.R.t) (i + 1) (H PP)))⁻¹ *
      ∏ PP ∈ c.Pg, c.chi (k + 1) PP (GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ)) (Units.ne_zero _) h1' (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D s.V s'.V s.β s'.β 1 κ sg sh x
      have i0 : IsHalf e (actO s.V s'.V 1⁻¹ κ⁻¹ x) ↔ IsHalf e x :=
        ⟨fun H' => GlobalTheory.AdelicLatMove.actO_actO_inv s.V s'.V 1 κ x ▸ GlobalTheory.SplitHecke.isHalf_actO 1 κ H',
          fun H' => GlobalTheory.SplitHecke.isHalf_actO _ _ H'⟩
      by_cases hx : IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), StepLevLaw.omegaQ_empty, StepLevLaw.omegaQ_empty,
          mul_one, mul_one]
        simp only [map_one, redFn_one, Units.val_one, Matrix.mul_one]
        exact hoT (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
      · beta_reduce
        rw [if_neg hx, if_neg fun H' => hx ⟨i0.1 H'.1, i1.1 H'.2⟩, mul_zero])
  rw [h2]
  congr 1
  have hchi : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).P.chi ⟨_, hlev.2⟩ =
      c.P.chi ⟨_, hP⟩ := rfl
  unfold Lev.levChi levFn
  rw [extendOne_of_mem _ hlev.2, hchi]
  simp only [Lev.datY, ↓reduceIte, Finset.prod_empty, mul_one]
  rw [Finset.prod_inv_distrib, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
  congr 1
  rw [mul_comm _ (∏ PP ∈ c.Pg, c.chi (k + 1) PP (GeneralLinearGroup.det (H PP))), inv_mul_cancel_left]

theorem vecLaw : ∀ D : D7, ForStep D fun _ _ s s' p => VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L)
    (Lev.levG s'.V s'.β s'.L) (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  intro D _ c hc k hk s s' hs hs' p hp
  obtain ⟨ξ, f₀, hv⟩ := hp.vec
  refine ⟨fun κ hκ => (StepLevLaw.stepLevLaw D c hc ⟨k, hk⟩ s s' hs hs' p.ω hp.weil ξ f₀ p.f hv κ hκ).2, ?_⟩
  exact stepLevLawT D c hc k hk s s' hs hs' p.ω hp.weil ξ f₀ p.f hv

end GlobalTheory.ChainOnto.StepVecLawBoth

end
