import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.WhittakerFunctional
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem G5.ptsIntegral_curve_const (W : Ideal (MRing ι)) (hW1 : IsArithVar W 1)
    (hfin : Finite (GroundTheory.Heights₂.Heights.projPts W)) (c : ℝ) :
    ptsIntegral W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) = c * degC W := by
  have : Nonempty K := hW1.1
  have hpot : pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.elim0 := Subsingleton.elim _ _
  have hpts := GroundTheory.Heights₂.Heights.PtsIntegralPoints.homogProof K ι W (fun _ => c) hW1.2.1.2.1 hfin
    (fun _ _ _ _ => rfl)
  rw [hpot, hpts]
  letI := Fintype.ofFinite (GroundTheory.Heights₂.Heights.projPts W)
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    GroundTheory.Heights₂.Heights.degC_eq_card_projPts, Nat.card_eq_fintype_card]
  ring

theorem G5.proof' (hK : ArithKleiman.Statement) (hF : CurvePointsFinite.Statement) : G5.Statement := by
  intro K _ ι _ P P0 D A e II hII hP hP0 hsemi hnef hconj hW
  set A' := A.tensor (constLine (ι := ι) e) with hA'def
  have hA : IsSmoothHerm A := hsemi.1
  have hA' : IsSmoothHerm A' := hA.mul (G5.isSmoothHerm_constLine e)
  have hU : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hsemi' : IsSemipositiveRel P0 P A' := by
    refine ⟨hA', fun z hz w hw => ?_⟩
    have hev : ∀ᶠ z' in 𝓝 z, Real.log (A'.h z') = Real.log (A.h z') + -e :=
      (show ∀ᶠ z' in 𝓝 z, ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 from hU.mem_nhds hz.1).mono fun z' hz' =>
        G5.log_tensor_constLine A e z' hz'
    have : leviForm (fun z => Real.log (A'.h z)) z w = leviForm (fun z => Real.log (A.h z)) z w := by
      unfold leviForm
      rw [G5.fderiv_fderiv_eq_of_add_const (-e) hev]
    rw [this]
    exact hsemi.2 z hz w hw
  have ha : A'.a = A.a := by
    show A.a + 0 = A.a
    rw [add_zero]
  have hnef' : NefOnFibres P A'.a := ha ▸ hnef
  have hconj' : IsConjInvariantH A' := fun z => by
    show A.h _ * Real.exp (-e) = A.h z * Real.exp (-e)
    rw [hconj z]
  have hW' : ∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A'] := by
    intro W hW1 hPW
    have hsn : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι,
        (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin 1 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ![B] := by
      intro B
      funext j
      fin_cases j
      rfl
    have hmc := metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => e) (fun _ _ _ => rfl) hW1
      (fun j => j.elim0) hA contDiffOn_const
    rw [hsn, hsn] at hmc
    have hA'W : II K ι W 1 ![A'] = II K ι W 1 ![A] - e * degC W := by
      rw [← G5.ptsIntegral_curve_const W hW1 (hF K ι W hW1) e]
      exact hmc
    rw [hA'W]
    linarith [hW W hW1 hPW]
  have hkl := hK K ι P P0 D A' II hII hP hP0 hsemi' hnef' hconj' hW'
  have htop := G5.top_tensor_constLine (II K ι) (hII K ι) P D A e hP hA
  rw [← hA'def] at htop
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
