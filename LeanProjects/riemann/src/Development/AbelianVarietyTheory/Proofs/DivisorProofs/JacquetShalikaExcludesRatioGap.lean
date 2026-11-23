import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

noncomputable section

namespace GlobalTheory.ThK.DetProdSatake

section Local

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.DetProd ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_norm_eq_rpow {χ : kˣ →* ℂˣ} (h : IsUnram χ) : ∃ s : ℝ, ∀ u : kˣ, ‖(χ u : ℂ)‖ = nabs k u ^ s := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.Published.JacquetShalikaLocalBound.exists_uniformizer (k := k)
  have hq : (1 : ℝ) < resCard k := by exact_mod_cast (Finite.one_lt_card : 1 < resCard k)
  have hq0 : (0 : ℝ) < resCard k := zero_lt_one.trans hq
  have ha : 0 < ‖(χ ϖ : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  refine ⟨-Real.logb (resCard k) ‖(χ ϖ : ℂ)‖, fun u => ?_⟩
  have e : χ u = χ ϖ ^ ord k u := DFunLike.congr_fun (eq_unrChar h hϖ) u
  rw [e, GlobalTheory.LGrp.nabs_eq_zpow, Units.val_zpow_eq_zpow_val, norm_zpow, ← Real.rpow_intCast (resCard k : ℝ),
    ← Real.rpow_mul hq0.le, Int.cast_neg, neg_mul_neg, mul_comm, Real.rpow_mul hq0.le,
    Real.rpow_logb hq0 hq.ne' ha, Real.rpow_intCast]

theorem exists_unitary {χ : kˣ →* ℂˣ} (h : IsUnram χ) {s : ℝ} (hs : ∀ u : kˣ, ‖(χ u : ℂ)‖ = nabs k u ^ s) :
    ∃ ψ : kˣ →* ℂˣ, IsUnram ψ ∧ (∀ u, ‖(ψ u : ℂ)‖ = 1) ∧ χ = ψ * absPow k (s : ℂ) := by
  refine ⟨χ * absPow k (-(s : ℂ)), fun x hx => ?_, fun u => ?_, ?_⟩
  · rw [MonoidHom.mul_apply, h x hx, isUnram_absPow k _ x hx, one_mul]
  · have hp := Real.rpow_pos_of_pos (nabs_pos' k u) s
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hs, absPow_neg, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
      norm_inv, val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg hp.le, mul_inv_cancel₀ hp.ne']
  · rw [mul_assoc, ← absPow_add, neg_add_cancel, absPow_zero, mul_one]

theorem isSubquotient_prod₂ {x x' : ℕ} {χ₁ χ₂ : kˣ →* ℂˣ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin (x + x')) k) V} (h : IsDetProdConst x x' χ₁ χ₂ π) :
    IsSubquotient π (prod₂ (detRep (Fin x) χ₁) (detRep (Fin x') χ₂)) := by
  obtain ⟨e, he⟩ := h
  let d : Fin 2 → ℕ := ![x, x']
  let χ : Fin 2 → kˣ →* ℂˣ := ![χ₁, χ₂]
  let σ : ∀ a : Fin 2, Representation ℂ (GL (Fin (d a)) k) ℂ := fun a => detRep (Fin (d a)) (χ a)
  have hd : ∑ a, d a = d 0 + d 1 := Fin.sum_univ_two d
  obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd σ
  obtain ⟨ψ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks d hd) ℂ).1 (ofChar (twoDet x x' χ₁ χ₂))
  let L := (PiTensorProduct.constantBaseRingEquiv (Fin 2) ℂ).toLinearEquiv
  let κ : (piTensor σ).Equiv (ofChar (twoDet x x' χ₁ χ₂)) := .mk L fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun y => ?_)
    simp [L, σ, χ, piTensor_tprod, detRep, ofChar_apply, twoDet, Fin.prod_univ_two]
    exact (mul_mul_mul_comm _ _ _ _).trans rfl
  let Φ := (ψ.trans (GlobalTheory.LocGL.parIndEquiv (stdBlocks d hd) κ.symm)).trans φ.symm
  exact he.trans (.of_injective Φ.toIntertwiningMap Φ.toLinearEquiv.injective)

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open NumberField IsDedekindDomain GlobalTheory.ThK.DetProd GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem false_of_ratioGap : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (τ : GlobalTheory.CuspRep.CuspSub E 2)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin 2) (w.adicCompletion E)))
    (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ), GlobalTheory.Published.JacquetShalikaBound → (GlobalTheory.CuspRep.CG.mk τ).IsUnitary →
    τ.IsLocComp w ρ → IsUnramAt w χ₁ → IsUnramAt w χ₂ → IsDetProdConstAt w 1 1 χ₁ χ₂ ρ.ρ → RatioGapAt w χ₁ χ₂ → False := by
  intro E _ _ _ τ w ρ χ₁ χ₂ hJ _ ⟨f, hf0, hf⟩ h₁ h₂ hP ⟨c, hc, hr⟩
  obtain ⟨s, hs⟩ := exists_norm_eq_rpow h₂
  have hs' : ∀ u, ‖(χ₁ u : ℂ)‖ = nabs _ u ^ (c + s) := fun u => by
    have := hr u
    rw [norm_div, hs, div_eq_iff (Real.rpow_pos_of_pos (nabs_pos' _ u) s).ne'] at this
    rw [this, Real.rpow_add (nabs_pos' _ u)]
  have hQ := isSubquotient_prod₂ (x := 1) (x' := 1) hP
  obtain ⟨ψ₁, u₁, n₁, rfl⟩ := exists_unitary h₁ hs'
  obtain ⟨ψ₂, u₂, n₂, rfl⟩ := exists_unitary h₂ hs
  refine GlobalTheory.T.unramified_principal_series_irreducible E τ w ψ₁ ψ₂ (c + s) s hJ u₁ u₂ n₁ n₂ (by rwa [add_sub_cancel_right]) _ ρ.ρ hQ
    ⟨f, fun g => LinearMap.ext fun v => hf g v⟩ fun e => hf0 ?_
  exact congrArg Representation.IntertwiningMap.toLinearMap e

end GlobalTheory.ThK.DetProdSatake
