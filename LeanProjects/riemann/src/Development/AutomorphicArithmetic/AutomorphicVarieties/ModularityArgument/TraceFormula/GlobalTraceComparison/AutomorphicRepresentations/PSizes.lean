import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.Rs
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem centre_eq (τ : ℝ) : splitCentre E n τ = (An.tor E (fun _ : Fin n => τ) : GA E n) := by
  have h := GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) n (Real.exp_pos τ)
  rw [Real.log_exp] at h
  rw [← h, DiscreteGroups.T1.G.Dcy.tor_eq]

private theorem logSize_centre (τ : ℝ) :
    logSize (splitCentre E n τ) ≤ 2 * Module.finrank ℚ E * |τ| := by
  rw [centre_eq]
  refine ((torNorm_holds E).2 n _).2.trans ?_
  have h : ‖(fun _ : Fin n => τ)‖ ≤ |τ| :=
    (pi_norm_le_iff_of_nonneg (abs_nonneg τ)).2 fun _ => by simp
  gcongr

private theorem logSize_inv' (g : GA E n) : logSize (g⁻¹) = logSize g := by
  unfold logSize
  rw [inv_inv, add_comm]

private theorem deg_top (g : GA E n) : deg g ⊤ = deg (1 : GA E n) ⊤ + logAbs g.val.det := by
  have e : (((1 : Matrix (Fin n) (Fin n) E)ᵀ : Matrix (Fin n) (Fin n) E) : Fin n → Fin n → E) =
      ⇑(Pi.basisFun E (Fin n)) := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hli : LinearIndependent E ((1 : Matrix (Fin n) (Fin n) E)ᵀ) := by
    rw [e]; exact (Pi.basisFun E (Fin n)).linearIndependent
  have hsp : Submodule.span E (Set.range ((1 : Matrix (Fin n) (Fin n) E)ᵀ)) = ⊤ := by
    rw [e]; exact (Pi.basisFun E (Fin n)).span_eq
  have h1 := D1.degBasis E n n g 1 hli
  have h2 := D1.degBasis E n n 1 1 hli
  have h3 := D1.degAdelic E n n 1 g g 1 hli (by simp)
  rw [mul_one] at h3
  rw [hsp] at h1 h2
  rw [← h1, ← h2, h3]

private theorem abs_logAbs_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA E n,
    |logAbs g.val.det| ≤ C * (1 + logSize g) := by
  obtain ⟨C, hC, h⟩ := degRight E n
  refine ⟨C, hC, fun g => abs_le.2 ⟨?_, ?_⟩⟩
  · have h1 := h g g⁻¹ ⊤
    rw [mul_inv_cancel, logSize_inv', deg_top g] at h1
    linarith
  · have h1 := h 1 g ⊤
    rw [one_mul, deg_top g] at h1
    linarith

private theorem sizes' : Sizes := by
  intro E _ _ _ n hn
  obtain ⟨C, hC, hdet⟩ := abs_logAbs_le (E := E) (n := n)
  obtain ⟨-, -, -, c₀, hc₀⟩ := D1.sizeBasic E n
  have hc : 0 ≤ 2 + |c₀| + C := by positivity
  refine ⟨2 + |c₀| + C, hc, fun x => ⟨?_, ?_, DiscreteGroups.T1.G.Dcy.redSize_nonneg _⟩⟩
  · set l := ldet x with hl
    set d : ℝ := (Module.finrank ℚ E : ℝ) with hd
    have hd0 : 0 < d := by
      rw [hd]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := E)
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set τ : ℝ := l / (n * d) with hτ
    set y : GA E n := splitCentre E n (-l / (n * d)) * x.1 with hy
    have hr : r0 x = redSize y := rfl
    have hx : x.1 = splitCentre E n τ * y := by
      rw [hy, ← mul_assoc, ← CuspidalL2GL.splitCentre_add]
      have : τ + -l / (n * d) = 0 := by rw [hτ]; ring
      rw [this, CuspidalL2GL.splitCentre_zero, one_mul]
    have hτle : 2 * d * |τ| ≤ 2 * |l| := by
      have hpos : 0 < (n : ℝ) * d := by positivity
      rw [hτ, abs_div, abs_of_pos hpos]
      have e : 2 * d * (|l| / (n * d)) = 2 * |l| / n := by field_simp
      rw [e]
      exact div_le_self (by positivity) hn0
    have hK : 2 * |l| + c₀ ≤ (2 + |c₀| + C) * (1 + |l|) := by
      have h1 := le_abs_self c₀
      have h2 := abs_nonneg l
      have h3 := abs_nonneg c₀
      nlinarith [mul_nonneg h3 h2, mul_nonneg hC h2]
    have key : redSize x.1 - (2 + |c₀| + C) * (1 + |l|) ≤ redSize y := by
      refine le_ciInf fun γ => ?_
      have h1 := DiscreteGroups.T1.G.Dcy.redSize_le x.1 γ
      have h2 : ratGL E n γ * x.1 = splitCentre E n τ * (ratGL E n γ * y) := by
        rw [hx, ← mul_assoc, ← CuspidalL2GL.splitCentre_comm, mul_assoc]
      rw [h2] at h1
      have h3 := hc₀ (splitCentre E n τ) (ratGL E n γ * y)
      have h4 : logSize (splitCentre E n τ) ≤ 2 * d * |τ| := logSize_centre τ
      linarith
    rw [hr]
    linarith
  · have h1 : |ldet x| ≤ C * (1 + logSize x.1) := hdet x.1
    have h2 := DiscreteGroups.T1.G.Dcy.logSize_nonneg x.1
    have h3 := abs_nonneg c₀
    nlinarith [mul_nonneg h3 h2]

theorem sizes_of_basic : Basic → Sizes := fun _ => sizes'

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
