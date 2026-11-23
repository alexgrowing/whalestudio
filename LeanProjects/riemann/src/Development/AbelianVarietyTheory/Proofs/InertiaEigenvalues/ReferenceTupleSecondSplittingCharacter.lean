import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem chiData_chrTh_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ChiData (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) (D.host.g 0 * D.host.g 1) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ hLev _ _ _ _ _ i _
  have hxi : R.toLevCh.xi A.μ0 = 1 := MonoidHom.ext fun x => by
    have h := hLev.xi A.μ0
    rw [hLev.xi_base] at h
    exact GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one h x
  have e : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).2 = R.toLevCh.mu0 ((i : ℕ) + 1) * R.eta⁻¹ := by
    simp only [Lift.chrTh, LevCh.mu, Lift.tup, hxi, mul_one]
  rw [e]
  refine ⟨?_, fun Q hQ => ?_, fun Q hQ k => ?_⟩
  · have ha := hLev.mu0 i
    have hc := hLev.eta
    refine ⟨⟨ha.1.1.mul hc.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha.1.2, hc.1.2, inv_one, one_mul]
    · show ((R.toLevCh.mu0 ((i : ℕ) + 1) x * (R.eta x)⁻¹ : Circle) : ℂ) =
        (((R.C.mu0 i).locK P k * (R.C.eta.locK P k)⁻¹ : ℂˣ) : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv, ha.2 P e he k x hx, hc.2 P e he k x hx, Units.val_mul,
        Units.val_inv_eq_inv_val]
  · intro x hx
    have hg : ∀ k, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) Q := fun k hk => hQ (by
      rw [Nat.cast_mul]
      fin_cases k
      · exact Ideal.mul_mem_right _ _ hk
      · exact Ideal.mul_mem_left _ _ hk)
    rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, (R.C.isMu0 i).unr Q hg x hx, R.C.isEta.unr Q x hx,
      inv_one, one_mul]
  · have hcard : (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (Q.under (𝓞 D.host.F))).card ≠ 1 := by
      refine ne_of_gt (Finset.one_lt_card.2 ⟨Q, ?_, GlobalTheory.IdemSupport.cP Q, ?_, hQ.symm⟩)
      · rw [Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset]; rfl
      · rw [Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset]; exact GlobalTheory.IdemSupport.under_cP Q
    rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv, (R.C.isMu0 i).triv.1, R.C.isEta.res.1,
      Formalism.L2.Host.etaFin, if_neg hcard, inv_one, one_mul]

end GlobalTheory.LevelSeries

end
