import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadPlace

set_option maxHeartbeats 2000000 in

theorem vec_read_at : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → ∃ (ea : AE D) (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) (c : ℂ), IsIdemSum ea (R.Pg ∪ R.Q t) ∧ IsSplitIdem D e ∧ e * ea = e ∧ f = e + cA D e ∧ IsStdChar D R.ψ (-1) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) ∧ IsLatVac (heisO R.ψ (Vc D i) (Wc D i)) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (R.vacP i) ∧ IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) 1 (R.vacP i) Tm ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) ∧ R.vP i t = Tm (datP R i t ea) ∧ R.ωP i t (1, k) (R.vP i t) = c • Tm (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t P hP e f hPI k hk
  obtain ⟨⟨hψ, hvac⟩, ea, hIS, hth⟩ := hL.thP.vP i t
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hvP : R.vP i t = Tm (datP R i t ea) := hall Tm hTm
  have lV := GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hL.lev.βV i)
  have lW := GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hL.lev.βW i)
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) := GlobalTheory.AdTh.RecPair.selfDual_of_coe lV
  have hSW : IsSelfDualC (Wc D i) (R.ΛW i) := GlobalTheory.AdTh.RecPair.selfDual_of_coe lW
  have hIS' := hIS
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := hIS'
  have hPm : P ∈ R.Pg ∪ R.Q t := Finset.mem_union.2 hP
  obtain ⟨rfl, rfl⟩ := GlobalTheory.Hk3.SplitMatch.idem_unique (hes P hPm) hPI
  have h1 : ∀ PP ∈ R.Pg ∪ R.Q t, IsSplitIdem D (es PP) := fun PP hPP => (hes PP hPP).1
  have h2 : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ QQ ∈ R.Pg ∪ R.Q t, QQ ≠ PP → es PP * es QQ = 0 := by
    intro PP hPP QQ hQQ hne
    refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP) (h1 QQ hQQ)).resolve_left fun h => hne ?_
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [(hes PP hPP).2 x hx, (hes QQ hQQ).2 x hx, h]
  have hee : es P * ea = es P := by
    rw [hsum]; exact GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hPm
  have ho := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS).conj
  have hinf : infPart D (cA D ea) = 0 := ho.infPart_eq
  have hSB : IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) :=
    GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinf (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
      (R.Pg ∪ R.Q t) (fun y => omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => by
        rw [GlobalTheory.PlaceVec.omegaK_congr R.Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          GlobalTheory.PlaceVec.omegaQ_congr (R.Q t) _ (R.xiR t) _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)]
  have hSB2 := GlobalTheory.SplitLinear.isSBHalf_actO hSV.1 hSW.1 1 k⁻¹ hSB
  have hcc : cA D ea * cA D (cA D ea) = 0 := by rw [GlobalTheory.SplitOnto.cA_cA, mul_comm, hc]
  have ha : cA D ea * cA D ea = cA D ea := ho.idem
  have r1 : cA D ea * cA D (es P) = cA D (es P) := by rw [← map_mul, mul_comm, hee]
  have r2 : ea * cA D (es P) = 0 := by
    have e1 : cA D (es P) = cA D (es P) * cA D ea := by rw [← map_mul, hee]
    rw [e1, ← mul_assoc, mul_comm ea, mul_assoc, hc, mul_zero]
  have r3 : cA D ea * es P = 0 := by
    have := congrArg (cA D) r2
    rwa [map_mul, GlobalTheory.SplitOnto.cA_cA, map_zero] at this
  have r4 : ea * es P = es P := by rw [mul_comm, hee]
  have key : (cA D ea + cA D (cA D ea)) * (es P + cA D (es P)) = es P + cA D (es P) := by
    rw [GlobalTheory.SplitOnto.cA_cA]
    linear_combination r1 + r2 + r3 + r4
  have hsupp : SuppAt (cA D ea) (Wc D i) k := fun a b => by
    rw [← hk a b, ← mul_assoc, key]
  have hLaw := GlobalTheory.SplitLinear.law_orth (hF i t).datum hSV hSW ho hcc hvac.theta hvac.lat one_ne_zero hTm
    (GlobalTheory.SplitLinear.suppAt_one _ _) hsupp (GlobalTheory.VecInv.isDetAt_detAt _ ha _ 1) (GlobalTheory.VecInv.isDetAt_detAt _ ha _ k)
  have hω := hLaw _ hSB
  rw [← hvP] at hω
  simp only [inv_one] at hω
  exact ⟨ea, Tm, _, hIS, (hes P hPm).1, hee, rfl, hψ, hSV, hSW, hvac.theta, hvac.lat, hTm, hSB, hSB2, hvP, hω⟩

end GlobalTheory.BadPlace

end
