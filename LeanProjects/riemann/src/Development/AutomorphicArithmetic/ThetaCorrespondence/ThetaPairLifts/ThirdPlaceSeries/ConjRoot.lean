import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRatioRealizationSameDual
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpConjStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem conjRoot_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ c : ℂ, (∃ n : ℕ, n ≠ 0 ∧ c ^ n = 1) ∧
        rdAt p w j hρ' ν f = c • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P := by
  intro p1 p2 p3 p4
  have hA := _root_.GlobalTheory.T.expAlg_of_cusp_decay_and_reciprocity p1 p2 p3 p4
  have hB := _root_.GlobalTheory.T.real_datum_rational_normalization_alt p1 p2 p3 p4
  unfold _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt at hA
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hA hB).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f hf => ?_⟩
  obtain ⟨a1, a2⟩ := hx0 x hx hle i p hp
  obtain ⟨n, a, g, hfe, halg⟩ := a1 hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP f hf
  obtain ⟨τ, hτ⟩ := exists_aut_alg (ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
    (ρ'.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
  have hfix : ∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y := by
    intro y
    have h1 := hρ.e_LL0 ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) y
    have h2 := hρ'.e_LL0 ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) y
    have hy : IsAlgebraic ℚ (Formalism.L2.Host.embLL0 (Fm.D x i) y) :=
      ((Algebra.IsAlgebraic.isAlgebraic y).algHom (Formalism.L2.Host.embLL0 (Fm.D x i)).toRatAlgHom)
    rw [← h1] at hy ⊢
    rw [hτ _ hy, h2, h1]
  obtain ⟨c, hc, hsum⟩ := a2 hm w hw j ρ hρ ν hpin hlev hN hR0 s h P hd hP f hf n a g hfe τ hfix
  refine ⟨c, hc, ?_⟩
  rw [← hf]
  have key : ∀ (ρ₀ : Setup (Fm.D x i).ntw) (hρ₀ : ρ₀.Good), rdAt p w j hρ₀ ν f =
      ν⁻¹ • ∑ k, ρ₀.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k) • evW p.nexp p.v₀ j (g k).val := by
    intro ρ₀ hρ₀
    change ν⁻¹ • evK p.nexp p.v₀ hρ₀ _ j _ (p.nexp.eF _ _ _ (Nat.le_add_left _ _) j.2 f) = _
    rw [hfe, map_sum]
    rfl
  rw [key ρ' hρ', key ρ hρ, smul_comm, ← hsum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hτ _ (halg k)]
end GlobalTheory.BigOn.Exp
end
end
