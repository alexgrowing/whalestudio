import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TSchur
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TUnitcent

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

theorem UpperTheory.Lit.Cas.centred :
    GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL k), IsLSeg Δ y.rep → (∀ (t : kˣ) (c : ℂ), ScalarBy y t c → ‖c‖ = 1) → IsSqIntCoeff y.rep := by
  intro H HA k _ _ _ _ _ Δ δ h hu
  have hpos : 0 < δ.1 := by
    obtain ⟨hd, -⟩ := h
    rw [← hd]
    have h1 : ∀ a, (Δ.term a).1 = Δ.first.1 := fun a => rfl
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact Nat.mul_pos Δ.len_pos Δ.isCusp_first.1
  obtain ⟨χ, hχ, hsq⟩ := (H k δ hpos).2 ⟨Δ, h⟩
  let e := δ.twEquiv χ hχ
  let τ := (δ.tw χ hχ).rep
  have he : ∀ g w, e.toLinearEquiv.symm (τ g w) =
      ((detChar (Fin δ.1) χ g : ℂˣ) : ℂ) • δ.rep g (e.toLinearEquiv.symm w) := fun g w => by
    obtain ⟨u, rfl⟩ := e.toLinearEquiv.surjective w
    have := e.toIntertwiningMap.isIntertwining _ _ g u
    rw [LinearEquiv.symm_apply_apply]
    refine e.toLinearEquiv.injective ?_
    rw [LinearEquiv.apply_symm_apply]
    exact this.symm
  have hτ : UnitaryCentral τ :=
    UpperTheory.Lit.Cas.unitcent k _ _ τ 2 (δ.tw χ hχ).2.rep.smooth (δ.tw χ hχ).2.rep.irr hsq
  have hχ1 : ∀ a : kˣ, ‖((χ a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    let z := Matrix.GeneralLinearGroup.scalar (Fin δ.1) a
    obtain ⟨c, hc⟩ := (UpperTheory.Lit.Cas.schur HA k δ a).1
    have hc1 := hu a c hc
    have hz1 : ‖((detChar (Fin δ.1) χ z : ℂˣ) : ℂ) * c‖ = 1 := by
      refine hτ a _ fun w => ?_
      refine e.toLinearEquiv.symm.injective ?_
      refine (he z w).trans ?_
      rw [map_smul, mul_smul]
      exact congrArg _ (hc _)
    rw [norm_mul, hc1, mul_one] at hz1
    have hdz : ((detChar (Fin δ.1) χ z : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) ^ δ.1 := by
      have hdet : Matrix.GeneralLinearGroup.det z = a ^ δ.1 := Units.ext (by
        simp [z, Matrix.GeneralLinearGroup.scalar, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal])
      rw [detChar_apply, hdet, map_pow, Units.val_pow_eq_pow_val]
    rw [hdz, norm_pow] at hz1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 hz1
  intro m bm μ hμ v ℓ hℓ'
  let l' : Module.Dual ℂ _ := ℓ ∘ₗ e.toLinearEquiv.symm.toLinearMap
  have hc : ∀ g, ‖l' (τ g (e.toLinearEquiv v))‖ = ‖((detChar (Fin δ.1) χ g : ℂˣ) : ℂ)‖ * ‖ℓ (δ.rep g v)‖ := fun g => by
    simp only [l', LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearEquiv.symm_apply_apply, map_smul, smul_eq_mul,
      norm_mul]
  have hFc0 : ∀ g : GL (Fin δ.1) k, ‖l' (τ g (e.toLinearEquiv v))‖ = ‖((detChar (Fin δ.1) χ g : ℂˣ) : ℂ)‖ * ‖ℓ (δ.rep g v)‖ :=
    fun g => hc g
  have hopen : IsOpen {g : GL (Fin δ.1) k | l' ∘ₗ τ g = l'} := by
    have hk : IsOpen ((detChar (Fin δ.1) χ).ker : Set (GL (Fin δ.1) k)) := hχ.detChar
    refine isOpen_iff_mem_nhds.2 fun g hg => ?_
    have hg' : l' ∘ₗ τ g = l' := hg
    have hU : {x | ℓ ∘ₗ δ.rep x = ℓ} ∩ ((detChar (Fin δ.1) χ).ker : Set (GL (Fin δ.1) k)) ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact Filter.inter_mem (hℓ'.mem_nhds (by show ℓ ∘ₗ δ.rep 1 = ℓ; rw [map_one, Module.End.one_eq_id, LinearMap.comp_id]))
        (hk.mem_nhds (one_mem _))
    refine Filter.mem_of_superset ((continuous_const_mul g⁻¹).continuousAt.preimage_mem_nhds hU) fun x hx => ?_
    obtain ⟨h1, h2⟩ := hx
    have h1' : ℓ ∘ₗ δ.rep (g⁻¹ * x) = ℓ := h1
    have h2' : detChar (Fin δ.1) χ (g⁻¹ * x) = 1 := h2
    show l' ∘ₗ τ x = l'
    have hx' : τ x = τ g * τ (g⁻¹ * x) := (congrArg τ (mul_inv_cancel_left g x)).symm.trans (map_mul τ g (g⁻¹ * x))
    rw [hx', Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hg']
    ext w
    simp only [l', LinearMap.comp_apply, LinearEquiv.coe_coe]
    refine (congrArg ℓ (he (g⁻¹ * x) w)).trans ?_
    rw [map_smul, h2', Units.val_one, one_smul]
    exact LinearMap.congr_fun h1' _
  obtain ⟨F, hF, hL⟩ := @hsq m bm μ hμ (e.toLinearEquiv v) l' hopen
  refine ⟨F, fun g => ?_, hL⟩
  refine ((hF g).trans (hFc0 g)).trans ?_
  rw [detChar_apply, hχ1, one_mul]
