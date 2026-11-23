import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub

noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area)

namespace GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem delta_ne_zero (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : δ ≠ 0 :=
  (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.1

theorem area_pos (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : 0 < area (lamOf D cc δ) := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [GlobalTheory.MomDict.area_lamOf D cc δ h.1.1]
  have h1 : (0 : ℝ) < Ideal.absNorm cc := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h.1.1)
  have h2 := Complex.normSq_pos.2 (delta_ne_zero h)
  have h3 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
  positivity

theorem xiR_pos (D : D7) : 0 < Formalism.L2.Pj.xiR D := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [hxi]
  have h1 : (0 : ℝ) < Ideal.absNorm D.host.ccK := by linarith
  have h3 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
  positivity

theorem normSq_scale (hc : cc ≠ ⊥) (h : IsScale D cc r) (δ : ℂ) (τ : D.what₂.Tau) :
    Complex.normSq (δ * embT D τ r) = 2 * Formalism.L2.Pj.xiR D * area (lamOf D cc δ) := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  have hcj : embT D τ (D.host.conj r) = starRingEnd ℂ (embT D τ r) := by
    have := D.host.isCMField_hostE
    have h : NumberField.IsCMField.complexConj D.host.E r = D.host.conj r := by
      apply D.host.φ₀.injective
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [← h, NumberField.IsCMField.complexEmbedding_complexConj]
  have h1 := congrArg (embT D τ) h
  rw [map_mul, map_mul, hcj, Complex.mul_conj, map_natCast, map_natCast] at h1
  have h2 : Complex.normSq (embT D τ r) * (Ideal.absNorm D.host.ccK : ℝ) = (Ideal.absNorm cc : ℝ) := by exact_mod_cast h1
  rw [GlobalTheory.MomDict.area_lamOf D cc δ hc, hxi, map_mul, ← h2]
  have h3 : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
  have h4 : Real.sqrt D.host.d ≠ 0 := by linarith
  field_simp

theorem IsScale.ne_zero (hc : cc ≠ ⊥) (h : IsScale D cc r) : r ≠ 0 := by
  rintro rfl
  have h1 : ((Ideal.absNorm cc : ℕ) : D.host.E) = 0 := by rw [← h]; simp
  exact hc (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))

theorem norm_period_sq (hc : cc ≠ ⊥) (h : IsScale D cc r) (δ : ℂ) (τ : D.what₂.Tau) :
    ‖period D δ r τ‖ ^ 2 = area (lamOf D cc δ) / Real.pi := by
  have hx := xiR_pos D
  have hp := Real.pi_pos
  rw [period, norm_div, div_pow, ← Complex.normSq_eq_norm_sq, normSq_scale hc h, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  field_simp

theorem Hf_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ} (Z X : VC D a d) :
    Hf D (tor0 D cc δ) (fun τ i j => δ * embT D τ r * Z τ i j) (fun τ i j => δ * embT D τ r * X τ i j) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (X τ i j) := by
  have hA : ((area (lamOf D cc δ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (area_pos hc).ne'
  have hL : (tor0 D cc δ).abelian₂ = lamOf D cc δ := rfl
  rw [Hf, hL, div_eq_iff hA]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : δ * embT D τ r * starRingEnd ℂ (δ * embT D τ r) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ((area (lamOf D cc δ) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, normSq_scale hc.1.1 h]; push_cast; ring
  rw [map_mul (starRingEnd ℂ) (δ * embT D τ r)]
  linear_combination (Z τ i j * starRingEnd ℂ (X τ i j)) * h1

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem reads_iff (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) (G : VC D S.rank T.rank → ℂ) (f : WO S T → ℂ) :
    Reads ψ θ rfl rfl cc δ r G f ↔ IsThetaFunO ψ S T f ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
      f w = GlobalTheory.FockPos.gaussO θ 1 1 w *
        (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) (GlobalTheory.FockPos.zCo θ 1 1 w) := by
  have hz : ∀ w : WO S T, GlobalTheory.FockPos.zCo θ 1 1 w = fun τ => compAt θ τ w := fun w => by
    funext τ
    have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
      Matrix.map_one _ (map_zero _) (map_one _)
    simp only [GlobalTheory.FockPos.zCo, e, inv_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  refine and_congr_right fun _ => forall₂_congr fun w _ => ?_
  have e1 : coordY θ rfl rfl δ r w = fun τ i j => δ * embT D τ r * compAt θ τ w i j := rfl
  have e2 := Hf_scale hc h (fun τ i j => compAt θ τ w i j) (fun τ i j => compAt θ τ w i j)
  rw [e1, e2, GlobalTheory.FockPos.gaussO, hz]
  simp only [Complex.mul_conj']
  congr! 3
  push_cast
  ring

variable {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {G : VC D a d → ℂ} {f f' : WO S T → ℂ}

theorem Reads.smul (h : Reads ψ θ hS hT cc δ r G f) (c : ℂ) : Reads ψ θ hS hT cc δ r (c • G) (c • f) :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).smul_mem c h.1, fun w hw => by
    rw [Pi.smul_apply, Pi.smul_apply, h.2 w hw, smul_eq_mul, smul_eq_mul]; ring⟩

theorem Reads.add {G' : VC D a d → ℂ} (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G' f') :
    Reads ψ θ hS hT cc δ r (G + G') (f + f') :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).add_mem h.1 h'.1, fun w hw => by
    rw [Pi.add_apply, Pi.add_apply, h.2 w hw, h'.2 w hw]; ring⟩

theorem Reads.unique (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G f') : f = f' :=
  sub_eq_zero.1 (GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real ((GlobalTheory.FinWeilO.thetaSub ψ S T).sub_mem h.1 h'.1)
    fun w hw => by rw [Pi.sub_apply, h.2 w hw, h'.2 w hw, sub_self])

end GlobalTheory.NormExact
