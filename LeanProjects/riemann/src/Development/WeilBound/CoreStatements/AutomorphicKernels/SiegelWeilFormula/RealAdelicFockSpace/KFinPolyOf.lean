import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.PolyGaussOfLines
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Imports
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.LineData
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.MemFockOf

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem actB_mul {d : SD σ} (a b : d.G) (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    actB (cA σ) (a * b) u = actB (cA σ) a (actB (cA σ) b u) := by
  simp only [actB, Units.val_mul, Subgroup.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem actB_one {d : SD σ} (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    actB (cA σ) (1 : d.G) u = u := by
  simp [actB]

theorem kFinPoly_of (hT : TAll) (hU : TUnit) (hH : THeis) (hA : AuxiliaryPrimeFunction) (hF : FockMem) (hLO : LocOpEx)
    (hLI : LocInst) : KFinPoly := by
  intro F E _ _ _ _ _ σ d R Φ hK
  have hΦ : Φ ∈ d.sch := hK.1
  obtain ⟨k, ω, χ, C, c, ν, νf, vv, hk, hω1, hω, hχ, hC, hν, hνf, heig, hrot, hB⟩ :=
    line_data hT hU hH hA hF hLO hLI R
  obtain ⟨q, hq0, hq⟩ := exists_poly hK hk
  have hω0 : ω ≠ 0 := by
    intro h; rw [h, norm_zero] at hω1; exact zero_ne_one hω1
  have hωi : ∀ j : ℕ, 0 < j → ω⁻¹ ^ j ≠ 1 := fun j hj h => hω j hj (by rw [inv_pow] at h; exact inv_eq_one.1 h)
  have hμ : (star χ)⁻¹ ≠ 0 := inv_ne_zero (star_ne_zero.2 hχ)
  obtain ⟨N, hN⟩ := poly_of_rot q hq0 (star χ)⁻¹ ω⁻¹ hμ (inv_ne_zero hω0) hωi
  have hinv : ∀ ξ z, actB (cA σ) k⁻¹ (vv ξ z) = vv ξ (ω⁻¹ * z) := fun ξ z => by
    have := congrArg (actB (cA σ) k⁻¹) (hrot ξ (ω⁻¹ * z))
    rwa [← actB_mul, inv_mul_cancel, actB_one, ← mul_assoc, mul_inv_cancel₀ hω0, one_mul, eq_comm] at this
  have hact : ∀ (i : ℕ) ξ z, actB (cA σ) (k⁻¹ ^ i) (vv ξ z) = vv ξ (ω⁻¹ ^ i * z) := by
    intro i
    induction i with
    | zero => intro ξ z; simp [actB_one]
    | succ i ih => intro ξ z; rw [pow_succ, actB_mul, hinv, ih, pow_succ, mul_assoc]
  have hTΦ : d.T Φ ∈ d.schM := (hT.1 F E σ d).1 Φ hΦ
  refine mem_fock_of R hνf hTΦ fun g hg' => ?_
  obtain ⟨Ω, hΩ, hTΩ⟩ := exists_lift hT hF R hg'
  obtain ⟨h, hh⟩ := hg_sch R hνf hTΦ hg'
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨P, -, hP⟩ := poly_gauss_of_lines (2 * Real.pi) hpi N h fun ξ => by
    set I : ℂ → ℂ := fun z => ∫ u, h u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) with hI
    set Eξ : ℂ → ℂ := fun z => Complex.exp (-(z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi))) * I z with hE
    have hdiff : Differentiable ℂ Eξ :=
      (Differentiable.cexp (by fun_prop)).mul (entire_laplace (2 * Real.pi) hpi h ξ)
    have hrel : ∀ z, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (star χ)⁻¹ ^ i * Eξ (ω⁻¹ ^ i * z) = 0 := by
      intro z
      have e0 := B_rel hT hU hν hχ hΩ (heig g hg' Ω hΩ hTΩ) hΦ q hq (vv ξ z)
      simp only [hact, hB g hg' Ω hΩ hTΩ Φ hΦ, ← hh] at e0
      have hn : ∀ i : ℕ, ‖ω⁻¹ ^ i * z‖ = ‖z‖ := fun i => by
        rw [norm_mul, norm_pow, norm_inv, hω1, inv_one, one_pow, one_mul]
      simp only [hn] at e0
      have hc0 : (C * (Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) : ℂ)) ≠ 0 :=
        mul_ne_zero hC (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')
      refine (mul_eq_zero.1 (?_ : (C * (Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) : ℂ)) *
        ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (star χ)⁻¹ ^ i * Eξ (ω⁻¹ ^ i * z) = 0)).resolve_left hc0
      rw [Finset.mul_sum, ← e0]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hE, hI]
      ring
    obtain ⟨p, hpN, hp⟩ := hN Eξ hdiff hrel
    refine ⟨p, hpN, fun z => ?_⟩
    have e1 := hp z
    simp only [hE] at e1
    have e2 : I z = Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi)) * p.eval z := by
      rw [← e1, ← mul_assoc, ← Complex.exp_add]
      simp
    have e3 : ((8 : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 16 * (Real.pi : ℂ) := by push_cast; ring
    rw [e3]
    simpa [hI] using e2
  exact ⟨P, fun u => by rw [← hh]; exact hP u⟩

end PositivityTheory.SiegelWeilFormula.KFP

end
