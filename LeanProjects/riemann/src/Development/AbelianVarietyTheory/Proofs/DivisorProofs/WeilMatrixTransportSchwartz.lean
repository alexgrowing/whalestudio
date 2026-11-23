import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeilCharacterDetEqAbsDetPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzBStatement
open MeasureTheory Matrix

namespace GlobalTheory.HeisUnitRight

def swapEquiv (k : Type) [AddCommGroup k] [TopologicalSpace k] (a b : Type) : (a × b → k) ≃ₜ+ (b × a → k) where
  toFun y := fun p => y p.swap
  invFun y := fun p => y p.swap
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def transposeHomeo (k : Type) [TopologicalSpace k] (a b : Type) : Matrix a b k ≃ₜ Matrix b a k where
  toFun Y := Yᵀ
  invFun Y := Yᵀ
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {f : Y → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB Y) : f ∘ e ∈ GlobalTheory.WeilM.SB X :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

theorem exists_haar_transport {X Y : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] (e : X ≃ₜ+ Y)
    (μ : @Measure X (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ μ' : @Measure Y (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ' ∧
      (∀ f : Y → ℂ, ∫ y, f y ∂μ' = ∫ x, f (e x) ∂μ) ∧ (∀ f : Y → ENNReal, ∫⁻ y, f y ∂μ' = ∫⁻ x, f (e x) ∂μ) := by
  letI : MeasurableSpace X := borel _
  letI : MeasurableSpace Y := borel _
  haveI : BorelSpace X := ⟨rfl⟩
  haveI : BorelSpace Y := ⟨rfl⟩
  exact ⟨μ.map e, e.isAddHaarMeasure_map μ,
    fun f => integral_map_equiv e.toHomeomorph.toMeasurableEquiv f,
    fun f => lintegral_map_equiv f e.toHomeomorph.toMeasurableEquiv⟩

theorem exists_unitary_factor_right : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin d × Fin n → k) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin n) k → ℂ)),
    Set.BijOn ι (GlobalTheory.WeilM.SB (Fin d × Fin n → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin d) (Fin n) k) : Set _) →
    ∀ (Tr : Matrix (Fin d) (Fin n) k → ((Fin d × Fin n → k) → ℂ) → (Fin d × Fin n → k) → ℂ)
      (Mu : (Matrix (Fin d) (Fin n) k →ₗ[k] k) → ((Fin d × Fin n → k) → ℂ) → (Fin d × Fin n → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @MeasureTheory.Measure (Fin d × Fin n → k) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    (∀ μ : @MeasureTheory.Measure (Fin d × Fin n → k) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin d × Fin n → k) → ℂ) → (Fin d × Fin n → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @MeasureTheory.Measure (Fin d × Fin n → k) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (Y * g.val)) →
    ∃ ν : kˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧ ∀ g : GL (Fin n) k,
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = ν (Matrix.GeneralLinearGroup.det g) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) ((d : ℂ) / 2) := by
  intro k _ _ _ _ n d ψ0 hψc hψ1 ι hι Tr Mu hTr hMu hTrI hMuI S hS hSI χ hχ
  let e := swapEquiv k (Fin n) (Fin d)
  let t := transposeHomeo k (Fin n) (Fin d)
  have hup : ∀ {φ}, φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) → φ ∘ e.symm ∈ GlobalTheory.WeilM.SB (Fin d × Fin n → k) :=
    fun h => comp_mem_SB e.symm.toHomeomorph h
  have hdown : ∀ {φ}, φ ∈ GlobalTheory.WeilM.SB (Fin d × Fin n → k) → φ ∘ e ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) :=
    fun h => comp_mem_SB e.toHomeomorph h
  let ι' : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) :=
    (LinearMap.funLeft ℂ ℂ t) ∘ₗ ι ∘ₗ (LinearMap.funLeft ℂ ℂ e.symm)
  have hι' : ∀ φ Z, ι' φ Z = ι (φ ∘ e.symm) Zᵀ := fun _ _ => rfl
  have hι'' : ∀ φ Z, ι' (φ ∘ e) Z = ι φ Zᵀ := fun _ _ => rfl
  refine GlobalTheory.T.abs_weilCharacter_det_eq_abs_det_pow ψ0 hψc hψ1 ι' ⟨?_, ?_, ?_⟩
    (fun C φ => Tr Cᵀ (φ ∘ e.symm) ∘ e)
    (fun l φ => Mu (l ∘ₗ (Matrix.transposeLinearEquiv (Fin d) (Fin n) k k).toLinearMap) (φ ∘ e.symm) ∘ e)
    ?_ ?_ ?_ ?_ (fun g φ => S g (φ ∘ e.symm) ∘ e) ?_ ?_ χ ?_
  · intro φ hφ
    exact comp_mem_SB t (hι.mapsTo (hup hφ))
  · intro φ hφ φ' hφ' h
    have h1 : ι (φ ∘ e.symm) = ι (φ' ∘ e.symm) := funext fun Y => congrFun h Yᵀ
    have h2 := hι.injOn (hup hφ) (hup hφ') h1
    exact funext fun y => congrFun h2 (e y)
  · intro F hF
    obtain ⟨φ, hφ, hφF⟩ := hι.surjOn (comp_mem_SB t.symm hF)
    refine ⟨φ ∘ e, hdown hφ, funext fun Z => ?_⟩
    rw [hι'', hφF]
    rfl
  · intro C φ hφ
    obtain ⟨h1, h2⟩ := hTr Cᵀ _ (hup hφ)
    refine ⟨hdown h1, funext fun Z => ?_⟩
    rw [hι'', h2, hι', Matrix.transpose_add]
  · intro l φ hφ
    obtain ⟨h1, h2⟩ := hMu (l ∘ₗ (Matrix.transposeLinearEquiv (Fin d) (Fin n) k k).toLinearMap) _ (hup hφ)
    refine ⟨hdown h1, funext fun Z => ?_⟩
    rw [hι'', h2, hι']
    rfl
  · intro μ hμ C φ hφ φ' hφ'
    obtain ⟨μ', hμ', h1, -⟩ := exists_haar_transport e μ hμ
    have h := hTrI μ' hμ' Cᵀ _ (hup hφ) _ (hup hφ')
    rw [h1, h1] at h
    exact h
  · intro μ hμ l φ hφ φ' hφ'
    obtain ⟨μ', hμ', h1, -⟩ := exists_haar_transport e μ hμ
    have h := hMuI μ' hμ' (l ∘ₗ (Matrix.transposeLinearEquiv (Fin d) (Fin n) k k).toLinearMap) _ (hup hφ) _ (hup hφ')
    rw [h1, h1] at h
    exact h
  · intro g φ hφ
    exact hdown (hS g _ (hup hφ))
  · intro g φ hφ μ hμ
    obtain ⟨μ', hμ', -, h1⟩ := exists_haar_transport e μ hμ
    have h := hSI g _ (hup hφ) μ' hμ'
    rw [h1, h1] at h
    exact h
  · intro g φ hφ
    refine funext fun Z => ?_
    rw [hι'', hχ g _ (hup hφ), hι', Matrix.transpose_mul, Matrix.transpose_transpose]

end GlobalTheory.HeisUnitRight
