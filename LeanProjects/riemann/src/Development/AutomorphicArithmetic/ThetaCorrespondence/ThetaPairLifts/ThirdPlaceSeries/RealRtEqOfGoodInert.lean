import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceFirst
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.InertFormFix.real_rt_eq_of_good_inert_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl Pp v → ∀ g : D.what₂.Mt (D.nd.mu i) (D.nd.j i), ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ → NG.rt D.host.E D.R.nV κ ((P.M.loc i).real g) = (P.M.loc i).real g := by
  intro hA hL D P X hX h41 h7 htie i hμ j hj h hh Pp hG hI v hv g κ hκ hT
  have hstd := hX.stdV j
  have hprime := GlobalTheory.InertFrameLoc.isPrimeIdem_tensAt hI rfl
  have hsupp := GlobalTheory.InertFormFix.suppF_of_trivOutside D hX.hF (Formalism.IndefR.Links.Vc D j) D.R.nV (hX.PV j) hstd Pp _ _ hprime v hv κ hT
  obtain ⟨c, hc⟩ := X.given.core.lev.βV j
  rw [one_pow] at hc
  have ls := (GlobalTheory.LevSplit.lev_split (Formalism.IndefR.Links.Vc D j) (X.R.βV j) (X.R.ΛV j) 1
    (Formalism.IndefR.RecTie.datVP X.R j (X.tupT (D.nd.mu i)) (X.R.levR X.F false)) hc).2 Pp _ _ hprime
    (by
      intro h1
      have : ((1 : ℕ) : 𝓞 D.host.E) = 1 := Nat.cast_one
      rw [this] at h1
      exact Pp.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1))
    (fun PP hPP => hG PP hPP)
  have hK : (hX.PV j).ψ κ ∈ Formalism.L2.Theta.KsphC (Formalism.IndefR.Links.Vc D j) ∅ := (hstd.2 κ).1 hκ
  have hlev := (ls.1 _ hsupp).2 hK
  have hchi := ls.2.1 _ hlev hsupp
  have hfix : ∀ (x : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) y,
      X.fn hμ j x (y * (hX.PV j).ψ κ) = X.fn hμ j x y := by
    intro x y
    have hm := ((X.IL.jMt (D.nd.mu i) hμ j) x).2
    obtain ⟨-, hm2⟩ := hm
    have e1 := hm2 ((hX.PV j).ψ κ) hlev y
    unfold GlobalTheory.NJoin.RealAt.fn
    rw [e1]
    rw [hchi]
    exact one_smul ℂ _
  have key : ∀ (j' : ℕ) (e : j.1 + 1 = j') (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m) (x : D.what₂.Mt (D.nd.mu i) j'),
      NG.rt D.host.E D.R.nV κ ((P.M (D.nd.mu i) j' h1 h2).real x) = (P.M (D.nd.mu i) j' h1 h2).real x := by
    intro j' e h1 h2 x
    subst e
    funext y
    show (P.M _ _ h1 h2).real x (y * κ) = _
    rw [hX.real (D.nd.mu i) hμ j x (y * κ), hX.real (D.nd.mu i) hμ j x y, ← mul_assoc, map_mul, hfix]
  exact key _ hj _ _ g
end
end
