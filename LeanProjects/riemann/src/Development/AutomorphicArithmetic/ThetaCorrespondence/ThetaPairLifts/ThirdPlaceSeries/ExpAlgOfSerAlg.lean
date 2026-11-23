import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfPowEqOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgAlt

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
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
def SerAlgAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
      ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
        ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, z k • evW p.nexp p.v₀ j (g k).val
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem expAlg_of_serAlg_alt (hS : _root_.GlobalTheory.BigOn.Exp.SerAlgAlt) : _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt _root_.GlobalTheory.BigOn.Exp.SerAlgAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine hS.imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP f hf => ?_⟩
  obtain ⟨n, z, g, hz, hsum⟩ := hx0 x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hp.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  refine exists_algExp p.nexp p.v₀ hρ _ j _ hU hW (Z.vec j) hK _ z g hz ?_
  rw [← hsum, ← hf]
  exact (smul_inv_smul₀ hN.1 _).symm
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
def SerRefAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∃ ν₀ : ℂ, IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν₀ ∧ RatBase (rdAt p w j hρ ν₀) ∧
    ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
      P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
        ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
          ν₀ • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, z k • evW p.nexp p.v₀ j (g k).val
theorem serAlg_of_serRef_scaleRoot (hR : _root_.GlobalTheory.BigOn.Exp.SerRefAlt) (hS : _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis) : _root_.GlobalTheory.BigOn.Exp.SerAlgAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.SerAlgAlt _root_.GlobalTheory.BigOn.Exp.SerRefAlt _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hR hS).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP => ?_⟩
  obtain ⟨a1, a2⟩ := hx0 x hx hle i p hp
  obtain ⟨ν₀, hN₀, hR₀, hexp⟩ := a1 hm w hw j ρ hρ ν hpin hN hR0
  obtain ⟨n, z, g, hz, hsum⟩ := hexp s h P hd hP
  by_cases hθ : ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, ?_⟩
    rw [hθ, smul_zero, Finset.univ_eq_empty, Finset.sum_empty]
  · obtain ⟨m, hm0, hpow⟩ := a2 hm w hw j ρ ρ hρ hρ ν₀ ν hpin hpin ⟨rfl, rfl, rfl, rfl, rfl⟩ hN₀ hN hR₀ hR0 s h P hd hP hθ
    have h0 : ν₀ ≠ 0 := hN₀.1
    have hζ : (ν / ν₀) ^ m = 1 := by rw [div_pow, hpow, div_self (pow_ne_zero _ h0)]
    refine ⟨n, fun k => ν / ν₀ * z k, g, fun k => ?_, ?_⟩
    · have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
      exact (hmem _).1 (mul_mem ((hmem _).2 (isAlgebraic_of_pow_eq_one hm0 hζ)) ((hmem _).2 (hz k)))
    · conv_lhs => rw [← div_mul_cancel₀ ν h0]
      rw [mul_smul, hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]
end GlobalTheory.BigOn.Exp
end
end
