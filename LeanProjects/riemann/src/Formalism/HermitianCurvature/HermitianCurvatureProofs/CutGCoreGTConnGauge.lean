import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem mulQ_zbP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P (MA.DQ P).zbP f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = star q.1.2 * (f : MA.Qp P.r P.TT → ℂ) q := mul_conjCoordinate_apply P f q

theorem mulQ_zP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P (MA.DQ P).zP f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = q.1.2 * (f : MA.Qp P.r P.TT → ℂ) q := algebraMap_comp_ofPadicInt_apply P f q

theorem mulQ_ggiP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P ((MA.DQ P).ggiP P.TT) f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * (f : MA.Qp P.r P.TT → ℂ) q := ggiP_apply P f q

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nabF_phase (P : M.Par) (hTT : 0 ≤ P.TT) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A B u : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hC : ConnF P Bs d e A B) (hu : PhaseEq P A B u) :
    NabF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  have hu' : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 :=
    fun ρ => ⟨(hu ρ).1, fun ζ hζ => ((hu ρ).2 ζ hζ).1⟩
  intro Φ
  constructor
  · funext ρ
    rw [actA_nabA, trR_phase P Bs e u hu', trR_phase P Bs e u hu', (hC Φ ρ).1]
    apply Subtype.ext
    funext q
    have hv := conj_smooth (hu ρ).1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    obtain ⟨_, hA, _⟩ := (hu ρ).2 q.1.2 hζ
    have hdc := (dZ_conj_unit P (hu ρ).1 (fun ζ hζ => ((hu ρ).2 ζ hζ).1) hζ).1
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Pi.add_apply, Pi.mul_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [mulQ_zbP, mulQ_ggiP, dzQ_apply P hTT, dzQ_apply P hTT, wirtQ_mul, wirtinger_derivative_fibre_function P hv, fnZ_val P hv,
      fnZ_val P (hAB ρ).1, hdc]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P hv]
    unfold modA at hA
    linear_combination (star (u ρ q.1.2) * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) * hA
  · funext ρ
    rw [actA_nabsA, trR_phase P Bs e u hu', trR_phase P Bs e u hu', (hC Φ ρ).2]
    apply Subtype.ext
    funext q
    have hv := conj_smooth (hu ρ).1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    obtain ⟨_, _, hB⟩ := (hu ρ).2 q.1.2 hζ
    have hdc := (dZ_conj_unit P (hu ρ).1 (fun ζ hζ => ((hu ρ).2 ζ hζ).1) hζ).2
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Subalgebra.coe_neg, Pi.add_apply,
      Pi.mul_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rw [mulQ_zP, mulQ_ggiP, dzbQ_apply P hTT, dzbQ_apply P hTT, wirtQ_mul, wirt_fnZ_zb P hv, fnZ_val P hv,
      fnZ_val P (hAB ρ).2, hdc]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P hv]
    unfold modB at hB
    linear_combination (star (u ρ q.1.2) * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) * hB

end main

theorem gauge_transform_holds : GTCGauge := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk A B' u hAB hC hu
  have hTT : 0 ≤ P.TT := torus_parameter Wp Wq P Bs X d hH
  have hu' : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 :=
    fun ρ => ⟨(hu ρ).1, fun ζ hζ => ((hu ρ).2 ζ hζ).1⟩
  exact ⟨isFrameB_phase P Bs e u he hu', kapF_phase P Bs d e u hu' hk,
    nabF_phase P hTT Bs d e A B' u hAB hC hu⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
