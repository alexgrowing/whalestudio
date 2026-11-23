import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MvZOneEqMapUnivSubst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvalAtJetMap
open Formalism.BasicNotions Formalism.L2.DIV MeasureTheory
open scoped Matrix

noncomputable section
open MvPolynomial GlobalTheory.KJInf

namespace GlobalTheory.AvgJet

variable {ι : Type} [Fintype ι]

def evalL {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) : PY ι a →ₗ[ℂ] ℂ where
  toFun := evalAt y
  map_add' F G := by simp [evalAt]
  map_smul' c F := by simp [evalAt, smul_eval]

theorem evalL_apply {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) : evalL y F = evalAt y F := rfl

theorem dual_eq_sum_evalAt {a : ℕ} (V : Submodule ℂ (PY ι a)) [FiniteDimensional ℂ V]
    (hsep : ∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) (Λ : Module.Dual ℂ V) :
    ∃ (S : Finset {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y}) (c : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} → ℂ),
      ∀ v : V, Λ v = ∑ y ∈ S, c y * evalAt y.1 (v : PY ι a) := by
  set E : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ
    (Set.range fun y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} => (evalL y.1).comp V.subtype) with hE
  have hco : E.dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    rw [Submodule.mem_dualCoannihilator] at hv
    have h0 : (v : PY ι a) = 0 := hsep _ fun y hy => hv _ (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    exact Subtype.ext h0
  have htop : E = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := E), hco, Submodule.dualAnnihilator_bot]
  have hΛ : Λ ∈ E := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hΛ
  refine ⟨c.support, c, fun v => ?_⟩
  rw [← hc, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, evalL_apply, smul_eq_mul]

theorem evalAt_rhoK {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (G : VV ℂ lam)
    (Y : ι → Matrix (Fin n) (Fin n) ℂ) :
    evalAt Y ((rhoK lam (invTrK g⁻¹) G : VV ℂ lam) : PY ι n) =
      (∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift) *
        evalAt (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Y τ) (G : PY ι n) := by
  have htr : trAct (invTrK g⁻¹) = lft (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold trAct lft Formalism.GradedWeylDivisibility.blockAct
    congr 1
  have hdet : detTwK lam (invTrK g⁻¹) =
      ∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift := by
    unfold detTwK
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [detPow, invTrK, inside₂, Units.val_zpow_eq_zpow_val]
  show evalAt Y (actP lam (invTrK g⁻¹) G) = _
  rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, htr, hdet]
  rw [evalAt, smul_eval, ← evalAt, evalAt_lft]

theorem integrable_term {a b : ℕ} {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
    [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν] {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r)
    (Λ : FP ι a b →ₗ[ℂ] ℂ) (Q : FP ι a b) (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Integrable (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) Q) * evalAt (fun τ => r k τ * y τ) F) ν := by
  set U := GlobalTheory.KJAvg.univSubst Q with hU
  set p : PY ι a := ∑ m ∈ U.support, C (Λ (monomial m 1)) * coeff m U with hp'
  have hp : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, Λ (mvZ g (fun _ => 1) Q) = eval (fun w => g w.1 w.2.1 w.2.2) p := by
    intro g
    rw [GlobalTheory.KJAvg.mvZ_one_eq_map_univSubst, GlobalTheory.KJAvg.linear_eq_sum_coeff Λ U.support _ (support_map_subset _ _)]
    simp only [hp', map_sum, map_mul, eval_C, coeff_map]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have e : (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) Q) * evalAt (fun τ => r k τ * y τ) F) =
      fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p * evalAt (fun τ => r k τ * y τ) F := by
    funext k
    rw [hp]
    simp only [GlobalTheory.KJAvg.ontoUni_inv hr]
  rw [e]
  exact GlobalTheory.KJAvg.integrable_avg_term ν hr p y F

end GlobalTheory.AvgJet

open GlobalTheory.AvgJet in

theorem GlobalTheory.AvgJet.avg_jet : ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b → 0 < a → ∀ (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (nn : ι → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' nn → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (r : K →* (ι → GL (Fin a) ℂ)), GlobalTheory.KJInf.OntoUni (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) →
    ∀ (Q : MvPolynomial (ι × Fin b × Fin a) ℂ) (Λ : Module.Dual ℂ (VV ℂ lam)), ∃ Λ' : Module.Dual ℂ (VV ℂ lam'),
    ∀ (ℓ : MvPolynomial (ι × Fin b × Fin a) ℂ →ₗ[ℂ] ℂ) (h : ι → GL (Fin b) ℂ) (v : VV ℂ lam),
      ∫ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) ∂ν =
        Λ' (rhoK lam' (invTrK h⁻¹) (Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v)) := by
  intro ι _ a b hab ha lam lam' nn hJ K _ _ _ _ _ ν _ _ r hr Q Λ
  classical
  obtain ⟨-, hcomp, -, -, -, -, hsep, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  obtain ⟨S, c, hΛ⟩ := dual_eq_sum_evalAt (VV ℂ lam) hsep Λ
  have hav := fun y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} =>
    GlobalTheory.KJAvg.avg_span ι a b hab ha lam nn K ν (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) hr y.1 Q
  choose m y' s hinv hspan using hav
  let d : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} → ℂ := fun y => (∏ τ, (y.1 τ).det ^ nn τ)⁻¹
  refine ⟨∑ y ∈ S, (c y * d y) • ∑ j, s y j • (evalL (y' y j)).comp (VV ℂ lam').subtype, fun ℓ h v => ?_⟩
  let hh : ι → Matrix (Fin b) (Fin b) ℂ := fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ)
  let Hh : ℂ := ∏ τ, (hh τ).det ^ (lam' τ).detShift
  let ℓ₀ : FP ι a b →ₗ[ℂ] ℂ := ℓ ∘ₗ (mvZ (fun _ => 1) hh).toLinearMap
  let F : PY ι a := (v : PY ι a) * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ nn τ
  have hFV : F ∈ Vn lam nn := ⟨v, (GlobalTheory.KJInf.ClsVal.cSpan_eq_VV' lam).symm ▸ v.2, rfl⟩

  have hpt : ∀ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) =
        Hh * ∑ y ∈ S, c y * d y * (ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F) := by
    intro k
    have hsub : GlobalTheory.CompactHowe.substF hh (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q =
        mvZ (fun _ => 1) hh (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) := by
      rw [hcomp]
      simp only [mul_one, one_mul, Matrix.coe_units_inv]
      rfl
    rw [map_inv r k, hΛ]
    simp only [evalAt_rhoK]
    rw [hsub]
    set L := ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) with hL
    have hL' : ℓ (mvZ (fun _ => 1) hh (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q)) = L := rfl
    have hH : (∏ τ, ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) = Hh := rfl
    rw [hL', Finset.prod_mul_distrib, hH, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hdet : ∀ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := fun τ => (Matrix.isUnits_det_units _).ne_zero
    have key : (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift)) *
        (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ (lam τ).detShift) =
        ∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [← zpow_add₀ (hdet τ), sub_add_cancel, zpow_natCast]
    have hdy : d y * ∏ τ, (y.1 τ).det ^ nn τ = 1 :=
      inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (y.2 τ).ne_zero)
    have hF : evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F =
        evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a) *
          ((∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ) * ∏ τ, (y.1 τ).det ^ nn τ) := by
      rw [GlobalTheory.KJInf.ValPol.evalAt_mul_prod, ← Finset.prod_mul_distrib]
      simp only [Matrix.det_mul, mul_pow]
    rw [hF]
    linear_combination (Hh * L * c y * evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a)) * key -
      (Hh * L * c y * evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a) *
        ∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ) * hdy
  have hint : ∀ y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y}, Integrable (fun k => c y * d y *
      (ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F)) ν :=
    fun y => (integrable_term ν hr ℓ₀ Q y.1 F).const_mul _
  have hjet : ((Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v : VV ℂ lam') : PY ι b) =
      Formalism.L2.Ker.jetMap (fun m => ℓ (MvPolynomial.monomial m 1)) nn (v : PY ι a) := by
    have hx : Formalism.L2.Ker.jetMap (fun m => ℓ (MvPolynomial.monomial m 1)) nn (v : PY ι a) =
        ((⟨_, hJ _ _ v.2⟩ : VV ℂ lam') : PY ι b) := rfl
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.retrVV, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hx, Submodule.projectionOnto_apply_left]
  have hav' : ∀ y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y},
      ∫ k, ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F ∂ν =
        ∑ j, s y j * ℓ (subY hab (fun τ => hh τ * y' y j τ) F) := by
    intro y
    rw [hspan y F hFV ℓ₀]
    refine Finset.sum_congr rfl fun j _ => ?_
    show s y j * ℓ (mvZ (fun _ => 1) hh (subY hab (y' y j) F)) = _
    rw [mvZ_subY]
  have hH : (∏ τ, ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) = Hh := rfl
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hint y]
  simp only [integral_const_mul, hav']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, evalL_apply,
    smul_eq_mul, evalAt_rhoK, hjet, GlobalTheory.KJInf.ClsVal.evalAt_jetMap hab, hH]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
