import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetSeparatingFiniteDimensionalFunctions
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.HCFct

theorem exists_interp {K : Type} (W : Submodule ℂ (K → ℂ)) (hW : FiniteDimensional ℂ W) :
    ∃ (s : Finset K) (b : s → W), ∀ w ∈ W, ∀ k, w k = ∑ i : s, w i.1 * (b i).1 k := by
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.finiteDim_functions_detected_by_finset K W hW
  let ev : W →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun i =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) i.1).comp W.subtype
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hs w.1 w.2 fun k hk => congrFun hw ⟨k, hk⟩)
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective ev hev
  refine ⟨s, fun i => ψ (fun j => if i = j then 1 else 0), fun w hw k => ?_⟩
  have e1 : (⟨w, hw⟩ : W) = ψ (ev ⟨w, hw⟩) := (LinearMap.congr_fun hψ _).symm
  rw [LinearMap.pi_apply_eq_sum_univ ψ (ev ⟨w, hw⟩)] at e1
  have e2 := congrArg (fun u : W => u.1 k) e1
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ev,
    LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply] using e2

theorem constTerm_cptTranslate_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ W := by
  intro E _ _ _ a L W hW X N r _ _ μ 𝓕 hμ h𝓕 _ φ hφ g
  have hP : Continuous φ.1 ∧ (∀ γ h, φ.1 (ratGL E a γ * h) = φ.1 h) ∧
      ∀ h, (fun k : Kinf E a => φ.1 (h * infGL E a (Unitary.toUnits k))) ∈ W := by
    induction hφ using Submodule.span_induction with
    | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left, fun h => hx.2.2.1 h⟩
    | zero => exact ⟨continuous_const, fun _ _ => rfl, fun _ => W.zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2.1 γ h) (hy.2.1 γ h),
        fun h => W.add_mem (hx.2.2 h) (hy.2.2 h)⟩
    | smul c x _ hx =>
      exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2.1 γ h), fun h => W.smul_mem c (hx.2.2 h)⟩
  obtain ⟨hc, hl, hK⟩ := hP
  obtain ⟨s, b, hb⟩ := exists_interp W hW
  haveI := hμ
  have hint : ∀ h, IntegrableOn (fun x => φ.1 (unip x * h)) 𝓕 μ := fun h =>
    CuspidalL2GL.integrableOn_unip hc hl μ h𝓕 h
  have hpt : ∀ k (x : BlockIx a r → Ad E), φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) =
      ∑ i : s, φ.1 (unip x * (g * infGL E a (Unitary.toUnits i.1))) * (b i).1 k := fun k x => by
    have := hb _ (hK (unip x * g)) k
    simpa only [mul_assoc] using this
  have e : (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) =
      ∑ i : s, (∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits i.1))) ∂μ) • (b i).1 := by
    funext k
    simp only [hpt k]
    rw [integral_finsetSum _ fun i _ => (hint _).mul_const _]
    simp only [integral_mul_const, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact W.sum_mem fun i _ => W.smul_mem _ (b i).2

end GlobalTheory.HCFct

end
