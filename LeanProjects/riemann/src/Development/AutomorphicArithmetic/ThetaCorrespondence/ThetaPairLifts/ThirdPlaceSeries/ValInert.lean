import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceSplitCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ValInert
theorem val_inert_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∀ c : ℂ, D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {c} → c = (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) := by
  intro _ hL D P X _ _ _ _ i hμ j hj w hG hI c hc
  have hcw := conjSelf D w hI
  have hLv : X.R.toLevCh.Is X.A.μ0 := X.recR.base.lev
  obtain ⟨hg, -, -⟩ := (GlobalTheory.GoodPrimes.good_primes X.R X.F hLv).2.1 _ w hG
  have hm0 : (X.R.C.mu0 j).UnrAt w := (X.R.C.isMu0 j).unr w fun k hk => hg (by
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk'
    · exact Ideal.mul_mem_left _ _ hk')
  have hxu : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra h
    rcases (hLv.Q_ram _ w).1 h with h | ⟨PP, h, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr h)).2 hc
  have hxi : X.R.xiH (X.tupT (D.nd.mu i)) = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ, xi_eq X.cfEq X.Tp P.tp X.tpEq]
  have hmu : (P.chr.e1 (D.naut.muC i)).1 = X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) := by
    rw [P.chr.muC i j hj, hxi, X.cfEq]
    rfl
  have hu : D.naut.unr (D.naut.locG (D.naut.muC i) w) := (P.chr.unr_iff _ w).2 (by rw [hmu]; exact hm0.mul hxu)
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp ((D.naut.frobEig_card _ hu).trans (D.naut.locG_dim _ w))
  have haa : a = a⁻¹ := by
    have e := (D.naut.csd_unr (D.naut.muC i) w w (D.naut.muC_csd i) hcw hu).2
    rw [ha, Multiset.map_singleton] at e
    exact Multiset.singleton_inj.1 e
  have hns := notSplit D w hcw
  have heu := (D.naut.etaTinv_def w).1
  have hee : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(-1 : ℂ)⁻¹} := by
    rw [(D.naut.etaTinv_def w).2, D.naut.etaT_inert w hns, Multiset.map_singleton]
  have hc1 : c = a * (-1 : ℂ)⁻¹ := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu heu (D.naut.locG_dim _ w) hee, ha, Multiset.map_singleton] at hc
    exact (Multiset.singleton_inj.1 hc).symm
  have hcc : c = c⁻¹ := by
    have h1 : (-1 : ℂ)⁻¹ = -1 := by norm_num
    rw [hc1, mul_inv, inv_inv, ← haa, h1]
  have hte : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 =
      X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) * X.R.C.eta⁻¹ := by
    rw [P.chr.tw, hmu, P.chr.etaTinv, X.cfEq]
  have hut : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1.UnrAt w :=
    (P.chr.unr_iff _ w).1 (by rw [D.naut.locG_tw]; exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu heu)
  have hc2 := P.chr.frob _ w hut
  rw [hc] at hc2
  have hc3 : c = (((X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ : ℂˣ) : ℂ)⁻¹ := by
    rw [Multiset.singleton_inj.1 hc2, hte]
    simp
  have hv : GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w =
      (X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ := by
    rw [← GlobalTheory.LFun.val_eq_of_chrEq (hLv.mu0 j) w, ← GlobalTheory.LFun.val_eq_of_chrEq (hLv.xi _) w,
      ← GlobalTheory.LFun.val_eq_of_chrEq hLv.eta w]
    first
      | rfl
      | (simp only [GlobalTheory.DownLift.valV, GlobalTheory.DownLift.chiV, Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Links.LevCh.mu, Formalism.IndefR.Lift.tup, GlobalTheory.LFun.val, GlobalTheory.LFun.locChar]; ext; simp)
      | (unfold GlobalTheory.DownLift.valV GlobalTheory.DownLift.chiV Formalism.IndefR.Lift.chrTh Formalism.IndefR.Links.LevCh.mu Formalism.IndefR.Lift.tup GlobalTheory.LFun.val GlobalTheory.LFun.locChar; simp)
  rw [hv, hcc, hc3, inv_inv]
end GlobalTheory.ValInert
end
