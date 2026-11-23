import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OmegaQEqGaussMulFlatTransform
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftVectorEqUnitMulDilatedFlatDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqUnitMulCentralTranslateLiftVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFourierCoefficientsConjugateTuples
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusActionIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddSumEqProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilOperatorIdempotentSumVacuumNormalisedSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarDilationElementSupportDetPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelTypePlaceThetaVectorLatticeFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHeisenbergTranslatesBaseVectorEqCardSmulStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FlatForm

theorem lift_eq_gauss_model_flat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t₀ : T0), VStd D i → ∀ eQ : AE D, IsIdemSum eQ (R.Q t₀) → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t₀, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ R.Q t₀, (ψP PP).IsPrimitive) ∧ ∀ t : T0, R.Q t = R.Q t₀ → ∀ (eg : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ Gc : ℂ, Gc = (∏ PP ∈ R.Q t₀, ((Nat.card (kP PP) : ℂ) ^ ((Vc D i).rank * (Wc D i).rank) * (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) (Wc D i).rank)⁻¹))⁻¹ → IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (fun x => Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0)) ∧ ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → R.vP i t = Tm (fun x => Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t₀ hV eQ heQ ϖ hϖ0 hϖ
  obtain ⟨ψP, Rs, hall⟩ := LiftFlatModel.exists_reps_pairing D G Pl0 T0 A Ks R F hC hQG i t₀ hV eQ heQ ϖ hϖ0 hϖ
  refine ⟨ψP, hall.1, fun t hQt eg fg heg hfg Gc hGc => ?_⟩
  rw [← hQt] at hall heQ hϖ hGc
  obtain ⟨hprim, hRs, hk, hbij, hiii, hiv, hv⟩ := hall
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hfin := omegaQ_eq_gauss_mul_flat_transform D (R.Q t) (R.xiR t) ψP (Wc D i).rank (Vc D i).rank (by omega)
    (fun PP hPP => ⟨hprim PP hPP, GlobalTheory.ChainTw.RModel.xiR_ne R hC.lev t PP hPP⟩)
  rw [← hGc] at hfin
  have hE : (ϖ : D.host.E) ≠ 0 := fun h => hϖ0 (by exact_mod_cast h)
  have hu : IsUnit (incA D (ϖ : D.host.E)) := (Ne.isUnit hE).map (incA D)
  have F1 : ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ↔ IsHalf eQ x := by
    intro x
    constructor
    · intro h a b
      have h1 := h a b
      simp only [Matrix.map_apply] at h1
      rw [mul_left_comm] at h1
      exact hu.mul_left_cancel h1
    · intro h a b
      simp only [Matrix.map_apply]
      rw [mul_left_comm, h a b]
  have F2 : ∀ x : WO (Vc D i) (Wc D i), ((-x).map fun w => incA D (ϖ : D.host.E) * w) =
      -(x.map fun w => incA D (ϖ : D.host.E) * w) := by
    intro x
    ext a b
    simp [mul_neg]
  have hPsiNeg : ∀ u ∈ Rs, (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0) =
      omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => if h : PP ∈ R.Q t then
        -((fun PP : ↥(R.Q t) => redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (u.map fun w => incA D (ϖ : D.host.E) * w))) ⟨PP, h⟩) else 0) := by
    intro u hu'
    have hh : IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) := by
      rw [F2]
      exact LiftFlatModel.isHalf_neg ((F1 u).2 (hRs u hu').1)
    have hi : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) := by
      rw [F2, LiftFlatModel.frMapO_neg]
      exact LiftFlatModel.isIntM_neg (hRs u hu').2
    rw [if_pos ⟨hh, hi⟩]
    apply LiftFlatModel.omegaFlat_congr
    intro PP hPP
    rw [dif_pos hPP, F2, LiftFlatModel.frMapO_neg, LiftFlatModel.redM_neg _ (hRs u hu').2]

  have hA : ∀ x : WO (Vc D i) (Wc D i),
      (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0) =
      ∑ u ∈ Rs, (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0) *
        halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) := by
    intro x
    by_cases hx : IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))
    · obtain ⟨u, ⟨huR, hured⟩, huniq⟩ := hbij (fun PP => -(redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
        (x.map fun w => incA D (ϖ : D.host.E) * w))))
      have hxh : IsHalf eQ x := (F1 x).1 hx.1
      rw [Finset.sum_eq_single u]
      · have hmem : x + u ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) :=
          (hiii x hxh u huR).2 ⟨hx.2, fun PP hPP => by rw [hured ⟨PP, hPP⟩, neg_neg]⟩
        have hhalf : IsHalf eQ (x + u) := (LiftFlatModel.isHalf_add_iff (hRs u huR).1).2 hxh
        rw [show halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) = 1 from
          if_pos ⟨hmem, hhalf⟩, mul_one, hPsiNeg u huR, if_pos hx]
        apply LiftFlatModel.omegaFlat_congr
        intro PP hPP
        rw [dif_pos hPP]
        show _ = -(redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (u.map fun w => incA D (ϖ : D.host.E) * w)))
        rw [hured ⟨PP, hPP⟩, neg_neg]
      · intro u' hu' hne
        rw [show halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u') = 0 from if_neg ?_,
          mul_zero]
        rintro ⟨hmem, -⟩
        obtain ⟨-, hred⟩ := (hiii x hxh u' hu').1 hmem
        exact hne (huniq u' ⟨hu', fun PP => by
          show _ = -(redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)))
          rw [hred PP.1 PP.2, neg_neg]⟩)
      · intro h
        exact absurd huR h
    · rw [if_neg hx]
      symm
      refine Finset.sum_eq_zero fun u hu' => ?_
      rw [show halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) = 0 from if_neg ?_,
        mul_zero]
      rintro ⟨hmem, hhalf⟩
      have hxh : IsHalf eQ x := (LiftFlatModel.isHalf_add_iff (hRs u hu').1).1 hhalf
      exact hx ⟨(F1 x).2 hxh, ((hiii x hxh u hu').1 hmem).1⟩
  have hB : ∀ x : WO (Vc D i) (Wc D i),
      (if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
        else 0) =
      halfInd (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) x *
        ∑ u ∈ Rs, (Gc * (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
          IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
          omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
            ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0)) * R.ψ (symplO (Vc D i) (Wc D i) x u) := by
    intro x
    by_cases hx : x ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) ∧ IsHalf (cA D eQ) x
    · have hint := (hiv x hx.2).1 hx.1
      rw [if_pos ⟨hx.2, hint⟩, show halfInd (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) x = 1 from
        if_pos hx, one_mul, hfin, Finset.mul_sum]
      symm
      refine Finset.sum_bij (fun u _ => fun PP : ↥(R.Q t) => redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (u.map fun w => incA D (ϖ : D.host.E) * w))) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro a ha b hb hab
        exact (hbij _).unique ⟨ha, fun PP => rfl⟩ ⟨hb, fun PP => (congrFun hab PP).symm⟩
      · intro y _
        obtain ⟨u, ⟨hu', hred⟩, -⟩ := hbij y
        exact ⟨u, hu', funext hred⟩
      · intro u hu'
        rw [hPsiNeg u hu', hv x hx.2 hint u hu', ← Finset.univ_eq_attach]
        ring
    · rw [show halfInd (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) x = 0 from if_neg hx,
        zero_mul, if_neg]
      rintro ⟨hh, hint⟩
      exact hx ⟨(hiv x hh).2 hint, hh⟩
  have hθ := GlobalTheory.T.thetaLiftVector_isThetaFunction_twoStepModel D G Pl0 T0 A Ks R F hC hQG i t eg eQ fg heg heQ hfg
  have hvP := LiftFlatModel.thetaAt_sum hθ (fun u hu' => by rw [LiftFlatModel.cA_cA]; exact (hRs u hu').1) hB
  have hΨ : ∀ x : WO (Vc D i) (Wc D i), Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0) =
      ∑ u ∈ Rs, (Gc * (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0)) *
        halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) := by
    intro x
    rw [hA x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  refine ⟨LiftFlatModel.isSBHalf_of_sum (fun u hu' => (hRs u hu').1) hΨ hk, fun Tm hTm => ?_⟩
  rw [LiftFlatModel.placeModel_sum hTm (fun u hu' => (hRs u hu').1) hΨ]
  exact hvP

theorem om_model_eq_dilate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t₀ : T0), VStd D i → ∀ (eQ : AE D) (es : Pl D.host.E → AE D), IsIdemSum eQ (R.Q t₀) → (∀ PP ∈ R.Q t₀, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → eQ = ∑ PP ∈ R.Q t₀, es PP → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t₀, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ (z : GA D (Vc D i)) (x : (AE D)ˣ), IsCentAt i (R.Q t₀) z ∧ (x : AE D) = 1 + ∑ PP ∈ R.Q t₀, cA D (es PP) * (incA D (star (ϖ : D.host.E)) ^ (Vc D i).rank - 1) ∧ ∀ t : T0, R.Q t = R.Q t₀ → ∀ (eg : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ → R.ωP i t (z, 1) (Tm Ψ) = ((((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ * ((Real.sqrt ((((∏ PP ∈ R.Q t₀, Nat.card (kP PP)) ^ ((Vc D i).rank * (Wc D i).rank) : ℕ) : ℝ)) : ℝ) : ℂ)) • Tm (fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t₀ hV eQ es heQ hes hsum ϖ hϖ0 hϖ
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨⟨z, hz⟩, hall⟩ := (GlobalTheory.ZRep.central_reps D G Pl0 T0 A Ks R F hC hQG i t₀).2.2 eQ es (fun _ => ϖ) heQ hes hϖ hsum
  obtain ⟨⟨hcent, hsupp, ⟨x, hx, hxv⟩, -⟩, Λe, Λc, Xe, Xc, Re, Rr, -, -, hE, hCc⟩ := hall z hz _ rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hR1, hR2, -, hcard, -⟩ := hE
  obtain ⟨-, -, -, hR3, -⟩ := hCc
  refine ⟨z, x, hcent, hxv, fun t hQt eg fg heg hfg Tm hTm Ψ hΨ => ?_⟩
  have hz' : mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) +
      (1 - eQ - cA D eQ)) := by
    rw [hz]
    congr 1
    funext _
    have hs : incA D (star (ϖ : D.host.E)) = cA D (incA D (ϖ : D.host.E)) := rfl
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← map_sum, ← hsum, hs]
    ring
  have hK := GlobalTheory.OnCmp.kerDat_tuple (i := i) hC.lev hC.thP t
  have heQ' : IsIdemSum eQ (R.Q t) := by rw [hQt]; exact heQ
  obtain ⟨hSV, hSW, hθ, hfix⟩ := GlobalTheory.T.tameKernel_typePlaceThetaVector_latticeFixed D G Pl0 T0 A Ks R F hC hQG i hV _ _ _ _ _ _ hK ⟨t, subset_rfl⟩ eg eQ fg heg heQ' hfg
  have hW := hC.thP.ωP i t
  have hN : (∏ PP ∈ R.Q t₀, Nat.card (kP PP)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun PP _ => Nat.card_pos.ne'
  have hNQ : ∀ PP ∈ R.Q t₀, ((∏ PP ∈ R.Q t₀, Nat.card (kP PP) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨c, hc⟩ : Nat.card (kP PP) ∣ ∏ PP ∈ R.Q t₀, Nat.card (kP PP) := Finset.dvd_prod_of_mem _ hPP
    rw [hc, Nat.cast_mul]
    refine Ideal.mul_mem_right _ _ ?_
    have := Ideal.absNorm_mem PP.asIdeal
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  obtain ⟨-, -, hpull, hsb, hlat⟩ :=
    GlobalTheory.DilScalar.scalar_dil_facts D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.Q t₀) eQ heQ _ hN hNQ ϖ hϖE hϖ z hz'
  have hom := GlobalTheory.SumHecke.om_eq_sum_idemSum D R.ψ (Vc D i) (Wc D i) _ _ _ hW (R.ΛV i) (R.ΛW i) hSV hSW (R.Q t₀) eQ heQ z x hsupp hx
    Rr hR1 hR2 hR3 fg hθ hfix
  have hsum := GlobalTheory.T.sum_heisenbergTranslates_baseVector_eq_card_smul D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW (R.Q t₀) eQ heQ z hlat Rr hR1 hR2 hR3 fg Tm hTm
  rw [← hcard]
  have hvac : R.ωP i t (z, 1) fg = ((((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ)) •
      Tm (Formalism.IndefR.Fin.LevelGroupLemmas.actPull (z, (1 : GA D (Wc D i))) (halfInd eQ (Formalism.IndefR.Fin.latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i)))) := by
    rw [hom, hsum, smul_smul]
    congr 1
    have hs : ((Rr.card : ℕ) : ℂ) = ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    rw [hs]
    simp only [splitFacO, map_one, mul_one, Circle.coe_mul, Circle.coe_inv]
    by_cases h0 : ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) = 0
    · rw [h0]; simp
    · field_simp
  have h := GlobalTheory.T.weilRep_apply_eq_smul_of_halfIndicator_base D R.ψ (Vc D i) (Wc D i) _ _ _ hW (R.ΛV i) (R.ΛW i) hSV hSW (R.Q t₀) eQ heQ fg hθ hfix Tm hTm (z, 1) _ hsb
    hvac Ψ hΨ
  rw [h, hpull Ψ hΨ.1]

theorem scalar_identity {ι : Type} (Q : Finset ι) (q : ι → ℕ) (g : ι → ℂ) (b ξ : ℂ) (n a : ℕ) (hq : ∀ P ∈ Q, q P ≠ 0) :
    ((b * ξ⁻¹ * ((Real.sqrt ((((∏ P ∈ Q, q P) ^ (n * (2 * a + 1)) : ℕ) : ℝ)) : ℝ) : ℂ)) *
      (∏ P ∈ Q, ((q P : ℂ) ^ (n * (2 * a + 1)) * (g P)⁻¹))⁻¹)⁻¹ =
    (b * ∏ P ∈ Q, (((Real.sqrt (q P : ℝ) : ℝ) : ℂ)⁻¹) ^ n)⁻¹ * (((∏ P ∈ Q, q P) ^ (n * a) : ℕ) : ℂ) *
      (∏ P ∈ Q, g P) ^ (-1 : ℤ) * ξ := by
  set S : ℂ := ∏ P ∈ Q, ((Real.sqrt (q P : ℝ) : ℝ) : ℂ) with hS
  have hSr : S = ((∏ P ∈ Q, Real.sqrt (q P : ℝ) : ℝ) : ℂ) := by rw [hS, Complex.ofReal_prod]
  have hsq : (∏ P ∈ Q, Real.sqrt (q P : ℝ)) ^ 2 = ((∏ P ∈ Q, q P : ℕ) : ℝ) := by
    rw [← Finset.prod_pow, Nat.cast_prod]
    exact Finset.prod_congr rfl fun P _ => Real.sq_sqrt (Nat.cast_nonneg _)
  have hM : ((∏ P ∈ Q, q P : ℕ) : ℂ) = S ^ 2 := by
    rw [hSr, ← Complex.ofReal_pow, hsq, Complex.ofReal_natCast]
  have hS0 : S ≠ 0 := fun h => by
    rw [h, zero_pow two_ne_zero, Nat.cast_eq_zero] at hM
    exact Finset.prod_ne_zero_iff.2 hq hM
  have h1 : ((Real.sqrt ((((∏ P ∈ Q, q P) ^ (n * (2 * a + 1)) : ℕ) : ℝ)) : ℝ) : ℂ) = S ^ (n * (2 * a + 1)) := by
    rw [Nat.cast_pow, ← hsq, ← pow_mul, mul_comm 2, pow_mul,
      Real.sqrt_sq (pow_nonneg (Finset.prod_nonneg fun P _ => Real.sqrt_nonneg _) _), hSr, Complex.ofReal_pow]
  have h2 : (∏ P ∈ Q, ((q P : ℂ) ^ (n * (2 * a + 1)) * (g P)⁻¹)) = (S ^ 2) ^ (n * (2 * a + 1)) * (∏ P ∈ Q, g P)⁻¹ := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, ← hM, Nat.cast_prod]
  have h3 : (∏ P ∈ Q, (((Real.sqrt (q P : ℝ) : ℝ) : ℂ)⁻¹) ^ n) = (S ^ n)⁻¹ := by
    rw [Finset.prod_pow, Finset.prod_inv_distrib, inv_pow]
  have h4 : (S ^ 2) ^ (n * (2 * a + 1)) = S ^ (n * (2 * a + 1)) * (S ^ n * (S ^ 2) ^ (n * a)) := by ring
  rw [h1, h2, h3, Nat.cast_pow, hM, _root_.zpow_neg_one, h4]
  have h5 : S ^ (n * (2 * a + 1)) ≠ 0 := pow_ne_zero _ hS0
  generalize S ^ (n * (2 * a + 1)) = U at h5
  simp only [mul_inv, inv_inv]
  calc _ = (U⁻¹ * U) * (b⁻¹ * S ^ n * (S ^ 2) ^ (n * a) * (∏ P ∈ Q, g P)⁻¹ * ξ) := by ring
    _ = _ := by rw [inv_mul_cancel₀ h5, one_mul]

theorem flat_eq_gauss_smul_om : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∃ (z : GA D (Vc D i)) (B : ℂ) (ε : ℤ) (r : ℕ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsCentAt i (R.Q t) z ∧ (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ B = B) ∧ (∀ PP ∈ R.Q t, (ψP PP).IsPrimitive) ∧ ∀ t' : T0, R.Q t' = R.Q t → ∀ f', IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, f' = (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε * ((R.xi t' s : Circle) : ℂ)) • R.ωP i t' (z, 1) (R.vP i t') := by
  intro D G _ _ Pl0 T0 A T _ R F hC hQG i t hV
  obtain ⟨eQ, heQ⟩ := (GlobalTheory.ZRep.central_reps D G Pl0 T0 A T.Q.c.F R F hC hQG i t).1
  obtain ⟨es, hes, hsum⟩ := heQ.1
  obtain ⟨ϖ, hϖ0, hϖ⟩ := GlobalTheory.FlatLift.exists_unif D.host.E (R.Q t)
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, x, hz, hx, hact⟩ := om_model_eq_dilate D G Pl0 T0 A T.Q.c.F R F hC hQG i t hV eQ es heQ hes hsum ϖ hϖ0 hϖ
  obtain ⟨ψP, hprim, hlift⟩ := lift_eq_gauss_model_flat D G Pl0 T0 A T.Q.c.F R F hC hQG i t hV eQ heQ ϖ hϖ0 hϖ
  obtain ⟨b, hb, hχ, -⟩ := GlobalTheory.FlatConst.flat_const D G Pl0 T0 A T R F hC i t es (fun _ => ϖ) (Vc D i).rank x hes
    (by rw [← hsum]; exact heQ.2) hϖ hx
  have hcardN : ∀ PP : Pl D.host.E, Ideal.absNorm PP.asIdeal = Nat.card (kP PP) := fun PP => by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  simp only [hcardN] at hb
  obtain ⟨a, ha⟩ : ∃ a, (Wc D i).rank = 2 * a + 1 := by
    have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨c, hc⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    exact ⟨a + c - 1, by rw [rW]; simp only [Ranks.r]; omega⟩
  refine ⟨z, (b * ∏ PP ∈ R.Q t, (((Real.sqrt (Nat.card (kP PP) : ℝ) : ℝ) : ℂ)⁻¹) ^ (Vc D i).rank)⁻¹ *
    (((∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank * a) : ℕ) : ℂ), -1, (Wc D i).rank, ψP, hz, fun τ hτ => ?_, hprim,
    fun t' hQt f hf => ⟨x, ?_⟩⟩
  · rw [map_mul, map_inv₀, hb τ hτ, map_natCast]
  obtain ⟨eg, eQ', fg, heg, heQ', hfg, hf⟩ := hf
  obtain rfl : eQ = eQ' := GlobalTheory.ConjDatum.idemSum_unique (Vc D i) (hQt ▸ heQ') heQ
  obtain ⟨hSB, hvP⟩ := hlift t' hQt eg fg heg hfg _ rfl
  obtain ⟨Tm, hTm⟩ := hf.1
  have hfT := hf.2 Tm hTm
  have hvT := hvP Tm hTm
  have hactT := hact t' hQt eg fg heg hfg Tm hTm _ hSB
  have hid := scalar_identity (R.Q t) (fun PP => Nat.card (kP PP))
    (fun PP => GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) (Wc D i).rank) b ((R.xi t' x : Circle) : ℂ) (Vc D i).rank a
    (fun PP _ => Nat.card_pos.ne')
  rw [← ha, ← GlobalTheory.FlatConst.chr_inv_val, ← hχ t'] at hid
  rw [← hid]
  generalize hκ : (((Lift.chrTh (R.toLevCh.mu t') R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ * ((Real.sqrt ((((∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank * (Wc D i).rank) : ℕ) : ℝ)) : ℝ) : ℂ) = κ at hactT ⊢
  generalize hGc : (∏ PP ∈ R.Q t, ((Nat.card (kP PP) : ℂ) ^ ((Vc D i).rank * (Wc D i).rank) * (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) (Wc D i).rank)⁻¹))⁻¹ = Gc at hactT hvT ⊢
  have hκ0 : κ ≠ 0 := by
    rw [← hκ]
    refine mul_ne_zero (inv_ne_zero (Circle.coe_ne_zero _)) ?_
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero (Nat.cast_nonneg _), Nat.cast_ne_zero]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun PP _ => Nat.card_pos.ne')
  have hG0 : Gc ≠ 0 := by
    rw [← hGc]
    refine inv_ne_zero (Finset.prod_ne_zero_iff.2 fun PP hPP => mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne'))
      (inv_ne_zero (gaussP_ne_zero _ _ _ _ (hprim PP hPP) ?_)))
    exact GlobalTheory.ChainTw.RModel.xiR_ne R hC.lev t' PP (hQt ▸ hPP)
  have hne : κ * Gc ≠ 0 := mul_ne_zero hκ0 hG0
  have hcomp : ∀ x : WO (Vc D i) (Wc D i),
      ((x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w).map fun w => incA D (ϖ : D.host.E) * w) = x := by
    intro x
    ext a b
    simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  rw [hvT, hactT]
  simp only [hcomp]
  have hsm : (fun x : WO (Vc D i) (Wc D i) => Gc * (if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaFlat (R.Q t') (Wc D i).rank (R.xiR t') (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0)) =
      Gc • (fun x : WO (Vc D i) (Wc D i) => if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaFlat (R.Q t') (Wc D i).rank (R.xiR t') (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) := rfl
  rw [hsm, map_smul, ← hfT, smul_smul, smul_smul, mul_assoc (κ * Gc)⁻¹, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.FlatForm
