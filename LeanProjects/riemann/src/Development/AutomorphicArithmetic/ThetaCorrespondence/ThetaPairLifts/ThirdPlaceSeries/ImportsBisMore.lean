import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.MuTameQS
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu ∧ ((∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu) := by
  intro hL D P S hS i w hw hSQ
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hc := hS.mu i w hw j hjj
  have hc' : IsComp (P.tp.tup (D.nd.mu i) j) w ((P.tp.tup (D.nd.mu i) j).loc w) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ w, fun _ => rfl⟩
  have hmu : (S i w hw).mu = (P.tp.tup (D.nd.mu i) j).loc w := GlobalTheory.HeckeComp.eq_of_isComp hc' hc
  rw [hmu]
  refine ⟨isTame_loc (tameAt_mul ((P.cf.isMu0 j).tame w) (P.tp.xi_tame _ w)), fun hg => ?_⟩
  refine not_isUnram_loc fun hU => ?_
  have hm0 : (P.cf.mu0 j).UnrAt w := (P.cf.isMu0 j).unr w fun k hk => hg k hk
  have hX : (P.tp.xi (D.nd.mu i)).UnrAt w := unrAt_of_mul_left hm0 hU
  rw [D.nd.mu_w i, P.tp.xi_tw, CharFrame.delAt, D.nd.w_l i] at hX
  have hpsi := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i, ← P.Q_eq i] at hpsi
  have hnl : w ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i w hSQ
  rcases hSQ with hwS | hwQ
  ·
    have hwQ : w ∉ D.nd.Q i := Finset.disjoint_left.1 (D.nd.SQ_disj i) hwS
    have hp : (P.tp.psi (D.nd.w i)).UnrAt w := (hpsi.ram w).2 hwQ
    have hd := (D.nd.S_def i w).1 hwS
    rcases hd.1 with h0 | h1 | hq
    · exact hg 0 h0
    · exact hg 1 h1
    · split_ifs at hX hq with hl
      · have hdu := unrAt_of_mul_left hp ((mul_comm _ _ : P.cf.del' * _ = _) ▸ hX)
        have := (P.cf.isDel'.ine w hq 1).1 fun x hx => by rw [pow_one]; exact hdu x hx
        norm_num at this
      · have hdu := unrAt_of_mul_left hp ((mul_comm _ _ : P.cf.del * _ = _) ▸ hX)
        have := (P.cf.isDel.ine w hq 1).1 fun x hx => by rw [pow_one]; exact hdu x hx
        norm_num at this
  ·
    have hwS : w ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hwQ
    have hd : (CharFrame.delAt P.cf (D.nd.l i)).UnrAt w := by
      unfold CharFrame.delAt
      split_ifs with hl
      · refine P.cf.isDel'.unr w fun ho => hwS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr ?_), hnl⟩)
        rw [if_pos hl]; exact ho
      · refine P.cf.isDel.unr w fun ho => hwS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr ?_), hnl⟩)
        rw [if_neg hl]; exact ho
    have hX' : (CharFrame.delAt P.cf (D.nd.l i) * P.tp.psi (D.nd.w i)).UnrAt w := by
      unfold CharFrame.delAt; exact hX
    exact (hpsi.ram w).1 (unrAt_of_mul_left hd hX') hwQ
end GlobalTheory.MuTameQS
end
