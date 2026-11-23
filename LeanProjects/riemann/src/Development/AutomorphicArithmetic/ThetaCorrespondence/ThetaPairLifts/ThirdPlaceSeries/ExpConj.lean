import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealDatumRationalNormalization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpOneLevelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp
theorem expConj_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∀ (n : ℕ) (a : Fin n → NX.KB p.Sx ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
        (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
        p.nexp.eF ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) (Nat.le_add_left _ _) j.2 f =
          ∑ k, a k ⊗ₜ[p.Sx.Ks] g k →
      ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
        ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
          ∑ k, τ (ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k)) • evW p.nexp p.v₀ j (g k).val =
            c • ∑ k, ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k) • evW p.nexp p.v₀ j (g k).val := by
  intro h1 h2 h3 h4
  have hO := _root_.GlobalTheory.T.real_datum_normalized_rational_base_alt h1 h2 h3 h4
  have hZ := _root_.GlobalTheory.BigOn.Exp.bigOn_expZero
  unfold _root_.GlobalTheory.BigOn.Exp.ExpZeroAlt at hZ
  refine (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hO hZ).imp fun Fm x hx i p _ _ w _ j H => ?_
  intro ρ hρ ν hpin hL hN hR0 s h P hd hP f hf n a g hfe τ hfix
  obtain ⟨a1, a2⟩ := H
  obtain ⟨c, hc, n', b, g', hb, hbc⟩ := a1 ρ hρ ν hpin hL hN hR0 s h P hd hP τ hfix
  have hν : ν ≠ 0 := hN.1
  have hsum : ∑ k, ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k) • evW p.nexp p.v₀ j (g k).val =
      ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P := by
    rw [← hf]
    change _ = ν • ν⁻¹ • evK p.nexp p.v₀ hρ _ j _ (p.nexp.eF _ _ _ (Nat.le_add_left _ _) j.2 f)
    rw [smul_inv_smul₀ hν, hfe, map_sum]
    rfl
  have h0 := a2 τ hfix (n + n')
    (Fin.append (fun k => ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k)) (fun k => -b k))
    (Fin.append g g') (by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, neg_smul, Finset.sum_neg_distrib]
      rw [hsum, hb, add_neg_cancel])
  rw [Fin.sum_univ_add] at h0
  simp only [Fin.append_left, Fin.append_right, map_neg, neg_smul, Finset.sum_neg_distrib] at h0
  refine ⟨c, hc, ?_⟩
  rw [hsum, ← hbc]
  exact add_neg_eq_zero.1 h0
end GlobalTheory.BigOn.Exp
end
