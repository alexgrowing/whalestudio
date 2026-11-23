import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientConjugateThetaForm

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedWeights

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift in

theorem exists_io_conj_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → HypConj R i σ μ' η' → ∀ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ io, IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ B f) (deltaConj i σ) io := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ _ μ' η' _ hH c c₁ hc ω f₀ f B hω hv
  have hM := hR.models
  have hθ : IsInfFam R.θ := hM.inf
  have hψ : IsStdChar D R.ψ (-1) := hv.vec.1.1
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f :=
    hv.vec.2.elim fun _ h => isThetaFunO_of_isThetaAt hψ hθ h.2 hv.vec.1.2.theta
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => onb_eq_one (hM.BV i τ)
  have hBu : ∀ τ, IsUnit (R.BV i τ) := fun τ => (IsUnit.of_mul_eq_one_right _ (hBS τ))
  have hw := fun ρ => weights_label D i (lab σ ρ) (pW D i ρ) (qW D i ρ)
    (congrArg Prod.fst ((hH.sig ρ).trans (hH.sig _).symm)) (congrArg Prod.snd ((hH.sig ρ).trans (hH.sig _).symm))
    ((R.MW i σ).lam ρ) ((R.MW i σ).ε ρ) (by have := (R.MW i σ).enum ρ; rw [hH.par ρ] at this; exact this)
  choose x₁ x₂ x₃ hx₁ hx₂ hx₃ hK hU hpq hε hap ham using hw
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hj := exists_poly_model (Vc D i) R.θ c (lamV D i) σ (Equiv.ofBijective _ hH.lab_bij) hH.lab_at c₁ hθ
    hc.coef hc.act hc.indep hc.span (R.BV i) hBu
  obtain ⟨j, hj1, hj2⟩ := hj
  exact exists_isIoW D (Vc D i) (Wc D i) R.ψ R.θ _ (R.MW i σ) c (lamV D i) (Equiv.ofBijective _ hH.lab_bij) (R.BV i) B
    j hj1 hj2 _ _ _ _ x₁ x₂ x₃ (hrk.le.trans (r_le_V i)) hpq hε hap ham hK hU _ _ ω hω hψ hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS hv.onb _ _ hH.mu_inf
    (fun τ => GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hH.mu_inf τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hH.eta_inf τ)))
    hx₁ hx₂ hx₃ f hth (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv.vec hth)

end GlobalTheory.MovedWeights

end
