import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrimeStatement
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.OneLetter

open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

theorem localLogarithm_eq_single_variable_oneLetter (D : D7) (p : ℕ) [Fact p.Prime] (h1 : nP D p = 1) {β : Type} (v : OrbitPlaces.Pl D × β) :
    OrbitPlaces.logPl D p v = at1 v (lgF ℂ_[p] p) := by
  rw [Formalism.L2.Th1.D.SingleLetterLog.at_variable_artin_hasse_eq_one_log]
  ext m
  have hb : ∀ e : ℕ, OrbitPlaces.backPl D p v.1 e = v.1 := fun e => by
    simp [OrbitPlaces.backPl, h1, posPl_zero]
  show (∑ e ∈ Finset.range (JetTdeg m + 1), _) = ∑ e ∈ Finset.range (m.degree + 1), _
  have hd : JetTdeg m = m.degree := rfl
  rw [hd]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hb]

theorem owOK_one {K : Type} [NormedField K] (σ : K →+* K) :
    OwOK 2 σ (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) :=
  ⟨fun _ => ⟨by simp, by simp⟩, fun _ => ⟨Formalism.L2.Th1.D.SingleLetterLog.iter_one σ 2, Formalism.L2.Th1.D.SingleLetterLog.iter_one σ 2⟩⟩

theorem trDual_one {K : Type} [NormedField K] (σ : K →+* K) :
    TrDual 2 σ (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) := by
  refine ⟨by simp, fun r r' => ?_⟩
  have hr : r = r' := Fin.ext (by have := r.isLt; have := r'.isLt; omega)
  rw [Formalism.L2.Th1.D.SingleLetterLog.univ_two, Finset.sum_pair (by decide)]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [h1, hr]

theorem beMean_fin_unit {K : Type} [Field K] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K) (ζ : K) :
    Formalism.L2.Th1.D.beMean (d := 2) l σ be0 (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) ζ =
      Formalism.L2.Th1.D.beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K)) (fun _ => 1) ζ := by
  have h : Formalism.L2.Th1.D.beTil (d := 2) l σ be0 (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) =
      Formalism.L2.Th1.D.beTil (d := 2) l σ be0 (fun _ : Unit => (1 : K)) (fun _ => 1) := by
    unfold Formalism.L2.Th1.D.beTil
    rw [Finset.sum_const, Finset.sum_const]
    simp
  unfold Formalism.L2.Th1.D.beMean
  rw [h]

end GlobalTheory.KerStd.OneLetter

namespace GlobalTheory.KerStd

open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open OneLetter

theorem expShape_of_integralClass : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → nP D p = 1 → ∀ (N N' : ℕ) (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), ‖ep‖ = 1 → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) → OrbitPlaces.ThetaExpansionRealPlaces D p Th := by
  intro D p _ g2 g3 s2 ε σ F hC h1 N N' ep Th hep hH
  obtain ⟨h5, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hl : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨f1, f2, hph⟩ := Formalism.L2.Th1.D.FAux.ffs p Formalism.L2.Th1.D.first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.FAux.exists_root2 p
  set B : MvPowerSeries (ZMod 2) (MaximalUnramifiedExtension p) :=
    Formalism.L2.Th1.D.beMean (d := 2) p σ (cob F (phFF p g2 g3 s2 ε)) (fun _ : Unit => (1 : MaximalUnramifiedExtension p)) (fun _ => 1) ζ with hBdef
  set Bc : MvPowerSeries (ZMod 2) ℂ_[p] := MvPowerSeries.map (MaximalUnramifiedExtension p).subtype B with hBc
  have hstd : BeStd p 2 Bc := ⟨σ, F, cob F (phFF p g2 g3 s2 ε), fun _ => 1, fun _ => 1, ζ,
    ⟨hσ, hF, f1, f2, owOK_one σ, trDual_one σ, hζ⟩, by rw [beOf, beMean_fin_unit]⟩
  have hB14 := GlobalTheory.T.standard_series_b_conditions_large_prime p 2 Bc h5 le_rfl even_two hstd

  have hO := Formalism.L2.Th1.D.oneLetterHalf (MaximalUnramifiedExtension p) p σ hσ F hF _ f1 f2 ζ hζ _ hph
  have h2 := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq (MaximalUnramifiedExtension p) ℂ_[p] Unit (MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.FAux.norm_coe p)).1 _ _ hO
  have hsL0 : MvPowerSeries.HasSubst (fun _ : ZMod 2 => (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have hsL : MvPowerSeries.HasSubst (fun _ : ZMod 2 => (lgF ℂ_[p] p : MvPowerSeries Unit ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have e2 : MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (MvPowerSeries.C ((2 : MaximalUnramifiedExtension p)⁻¹) *
      MvPowerSeries.subst (fun _ : ZMod 2 => (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p))) B) =
      MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => (lgF ℂ_[p] p : MvPowerSeries Unit ℂ_[p])) Bc := by
    rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_subst hsL0, map_inv₀, map_ofNat]
    have e3 : MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p)) = lgF ℂ_[p] p :=
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF (MaximalUnramifiedExtension p).subtype p
    simp only [e3, hBc]
  rw [e2] at h2
  obtain ⟨-, hsymm, -, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] (OrbitPlaces.Pl D × Fin N × Fin N')
  have hsub := (Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] Unit).2.2.2.2 (OrbitPlaces.Pl D × Fin N × Fin N')
  have h3 : ∀ x : OrbitPlaces.Pl D × Fin N × Fin N', Simeq (at1 x (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)))
      (MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => at1 x (lgF ℂ_[p] p)) Bc) := by
    intro x
    have hsx : MvPowerSeries.HasSubst
        (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    have h4 := hsub _ _ (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (fun _ => by simp) (fun _ => Formalism.InvariantFactorPaths.G7.TwoS.integral_X x) h2
    rw [MvPowerSeries.subst_mul hsx, MvPowerSeries.subst_C,
      MvPowerSeries.subst_comp_subst_apply hsL hsx] at h4
    exact h4
  have h5s := Formalism.L2.Th1.D.B4.simeq_sum Finset.univ _ _ fun x _ => h3 x
  obtain ⟨h50, h5I⟩ := hsymm _ _ h5s
  set f : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ∑ x : OrbitPlaces.Pl D × Fin N × Fin N', at1 x (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)) with hf
  set g : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ∑ x : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => at1 x (lgF ℂ_[p] p)) Bc with hg
  have hm0 : PowerSeries.constantCoeff (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.D.FAux.cc_phFF hl, map_zero]
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    rw [hf, map_sum]
    exact Finset.sum_eq_zero fun x _ => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero x hm0
  have hg0 : MvPowerSeries.constantCoeff g = 0 := by
    have h := h50
    rw [map_sub, hf0, sub_zero] at h
    exact h
  have hng0 : MvPowerSeries.constantCoeff (-g) = 0 := by rw [map_neg, hg0, neg_zero]
  have hnf0 : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf0, neg_zero]

  have hsA : MvPowerSeries.HasSubst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have hsE : MvPowerSeries.HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by simp
  have hlogfun : (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => MvPowerSeries.C ep * OrbitPlaces.logPl D p v) =
      fun v => MvPowerSeries.C ep * at1 v (lgF ℂ_[p] p) := funext fun v => by rw [localLogarithm_eq_single_variable_oneLetter D p h1]
  have hlog2 : (OrbitPlaces.logPl D p (β := Fin N × Fin N')) = fun v => at1 v (lgF ℂ_[p] p) :=
    funext fun v => localLogarithm_eq_single_variable_oneLetter D p h1 v
  have hS : MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => MvPowerSeries.C ep * OrbitPlaces.logPl D p v) Th =
      MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
    rw [hlogfun, MvPowerSeries.subst_comp_subst_apply hsE hsA]
    congr 1
    funext v
    rw [MvPowerSeries.subst_mul hsA, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsA]

  have hE : ∀ z : OrbitPlaces.Pl D, ∀ a : Fin N, ∀ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc =
      MvPowerSeries.subst (fun _ : ZMod 2 =>
        (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Bc := by
    intro z a b
    simp only [map_one, one_mul, ite_self]
  have hsX : ∀ x : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.HasSubst
      (fun _ : ZMod 2 => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    fun x => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by simp
  set E' : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ((-1 : ℂ_[p]) / 2) • ∑ x : OrbitPlaces.Pl D × Fin N × Fin N',
      MvPowerSeries.subst (fun _ : ZMod 2 =>
        (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Bc with hE'
  have hsubE : MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p)) E' = -g := by
    rw [hE', ← MvPowerSeries.coe_substAlgHom hsA, map_smul, MvPowerSeries.coe_substAlgHom hsA,
      Formalism.L2.Th1.D.Pair.subst_sum hsA, hg, MvPowerSeries.smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.subst_comp_subst_apply (hsX x) hsA]
    simp only [MvPowerSeries.subst_X hsA]
    rw [← neg_mul, ← map_neg]
    congr 2
    ring
  have hE0 : MvPowerSeries.constantCoeff E' = 0 := by
    rw [← HostLog.constantCoeff_subst (fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (Formalism.L2.Th1.D.Pair.cc_lgF hl)) E',
      hsubE, hng0]
  have hsum : (∑ z : OrbitPlaces.Pl D, ((-1 : ℂ_[p]) / 2) • ∑ a : Fin N, ∑ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc) = E' := by
    simp only [hE, hE', Fintype.sum_prod_type, Finset.smul_sum]
  have e5 : mvExp (g - f) * mvExp (-g) = mvExp (-f) := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add h50 hng0]
    congr 1
    ring
  have e6 : mvExp (-f) * mvExp f = 1 := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add hnf0 hf0, neg_add_cancel, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero']
  refine ⟨ep, hep, fun _ => Bc, fun _ => hB14, fun _ => 1, fun _ => norm_one, fun _ => -1, fun _ => Or.inr rfl,
    mvExp (g - f) * (mvExp f * MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th)),
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' h5I hH, ?_⟩
  show _ = _ * MvPowerSeries.subst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) (product_zeroth_first_parts.expS ℂ_[p]
    (∑ z : OrbitPlaces.Pl D, ((-1 : ℂ_[p]) / 2) • ∑ a : Fin N, ∑ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc))
  rw [hS, hsum, hlog2]
  show _ = _ * MvPowerSeries.subst _ (mvExp E')
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hsA hE0, hsubE]
  calc _ = (mvExp (-f) * mvExp f) * MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
        rw [e6, one_mul]
    _ = _ := by rw [← e5]; ring

end GlobalTheory.KerStd
