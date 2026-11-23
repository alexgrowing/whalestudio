import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix

namespace GlobalTheory.WeilTr

open GlobalTheory.WeilM

variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]

def trRep {G : Type} [Group G] (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) (om : G →* Module.End ℂ ((κ → R) → ℂ)) :
    G →* Module.End ℂ ((κ → R) → ℂ) where
  toFun g := T.toLinearMap ∘ₗ om g ∘ₗ T.symm.toLinearMap
  map_one' := by
    ext φ x
    simp
  map_mul' g h := by
    ext φ x
    simp

theorem trRep_apply {G : Type} [Group G] (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) (om : G →* Module.End ℂ ((κ → R) → ℂ))
    (g : G) (φ : (κ → R) → ℂ) : trRep T om g φ = T (om g (T.symm φ)) := rfl

variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}

def IsGoodInt [TopologicalSpace R] (C : TestClass R) (ψ : AddChar R ℂ) (d d₁ : Darboux B κ)
    (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : Prop :=
  (∀ φ, φ ∈ C.sp κ ↔ T φ ∈ C.sp κ) ∧
  (∀ w, ∀ φ ∈ C.sp κ, T (d.rho ψ w φ) = d₁.rho ψ w (T φ)) ∧
  (∀ l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ, l ∈ C.adm κ ↔ l ∘ₗ T.toLinearMap ∈ C.adm κ) ∧
  ∀ μ : @Measure (κ → R) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ c : ℝ≥0∞, ∀ φ ∈ C.sp κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

section Dbl

variable {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

variable (c) in

def HasDbl [TopologicalSpace R] (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (d d₁ : Darboux (symp c ξ JA JB) κ) (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : Prop :=
  ∀ dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ), IsDblCoord c ξ JA JB d dd →
    ∃ (dd₁ : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) (Td : ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ))
      (S : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)), IsDblCoord c ξ JA JB d₁ dd₁ ∧ IsGoodInt C ψ dd dd₁ Td ∧
      (∀ φ, φ ∈ C.sp κ ↔ S φ ∈ C.sp κ) ∧
      ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ, Td (boxFun φ₁ φ₂) = boxFun (T φ₁) (S φ₂)

end Dbl

theorem isUSplitting_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] {C : TestClass R} {ψ : AddChar R ℂ} {d d₁ : Darboux B κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T)
    {G : Type} [Group G] [TopologicalSpace G] {act : G → W → W} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUSplitting C ψ d act om) : IsUSplitting C ψ d₁ act (trRep T om) := by
  obtain ⟨hsp, hheis, hadm, hunit⟩ := hT
  have hinv : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hsp _).2 (by simpa using hφ)
  have hrho : ∀ w, ∀ φ ∈ C.sp κ, T.symm (d₁.rho ψ w φ) = d.rho ψ w (T.symm φ) := fun w φ hφ => by
    rw [LinearEquiv.symm_apply_eq, hheis w _ (hinv φ hφ), LinearEquiv.apply_symm_apply]
  refine ⟨⟨fun g φ hφ => ?_, fun g w φ hφ => ?_, fun g l hl => ?_⟩, fun μ hμ g φ hφ => ?_, fun l hl φ hφ => ?_⟩
  · rw [trRep_apply]
    exact (hsp _).1 (h.pres g _ (hinv φ hφ))
  · rw [trRep_apply, trRep_apply, hrho w φ hφ, h.impl g w _ (hinv φ hφ), hheis _ _ (h.pres g _ (hinv φ hφ))]
  · have h1 : l ∘ₗ T.toLinearMap ∈ C.adm κ := (hadm l).1 hl
    have h2 := h.adm g _ h1
    have h3 : (l ∘ₗ T.toLinearMap ∘ₗ om g) ∘ₗ T.symm.toLinearMap ∈ C.adm κ := by
      rw [hadm]
      convert h2 using 1
      ext φ
      simp
    convert h3 using 1
    ext φ
    simp [trRep_apply]
  · obtain ⟨c, hc⟩ := hunit μ hμ
    rw [trRep_apply, hc _ (h.pres g _ (hinv φ hφ)), h.unit μ hμ g _ (hinv φ hφ)]
    conv_rhs => rw [← LinearEquiv.apply_symm_apply T φ]
    rw [hc _ (hinv φ hφ)]
  · have := h.cont _ ((hadm l).1 hl) _ (hinv φ hφ)
    simpa [trRep_apply] using this

theorem siegelRule_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T)
    {χ : Eˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy : Matrix β ν E} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : SiegelRule c C ψ ξ JA JB d χ Cy om) : SiegelRule c C ψ ξ JA JB d₁ χ Cy (trRep T om) := by
  obtain ⟨hsp, hheis, hadm, -⟩ := hT
  have hinv : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hsp _).2 (by simpa using hφ)
  intro l hl hinvl p t hpt φ hφ
  have key := h (l ∘ₗ T.toLinearMap) ((hadm l).1 hl) (fun z φ' hφ' => by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [hheis _ _ hφ', hinvl z _ ((hsp _).1 hφ')]) p t hpt (T.symm φ) (hinv φ hφ)
  simpa [trRep_apply] using key

theorem isUWeilB_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    [TopologicalSpace E] [IsModuleTopology R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T) (hD : HasDbl c C ψ ξ JA JB d d₁ T)
    {χ : Eˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilB c C ψ ξ JA JB d χ om) : IsUWeilB c C ψ ξ JA JB d₁ χ (trRep T om) := by
  obtain ⟨hs, dd, omd, hdd, ⟨hL, hsd, hsg⟩, hbox⟩ := h
  obtain ⟨dd₁, Td, S, hdd₁, hTd, hS, hTbox⟩ := hD dd hdd
  have hinvT : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hT.1 _).2 (by simpa using hφ)
  have hinvS : ∀ φ ∈ C.sp κ, S.symm φ ∈ C.sp κ := fun φ hφ => (hS _).2 (by simpa using hφ)
  refine ⟨isUSplitting_trRep hT hs, dd₁, trRep Td omd, hdd₁, ⟨hL, isUSplitting_trRep hTd hsd, siegelRule_trRep hTd hsg⟩, fun g gd hg φ₁ hφ₁ φ₂ hφ₂ => ?_⟩
  have hb : Td.symm (boxFun φ₁ φ₂) = boxFun (T.symm φ₁) (S.symm φ₂) := by
    rw [LinearEquiv.symm_apply_eq, hTbox _ (hinvT φ₁ hφ₁) _ (hinvS φ₂ hφ₂), LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  rw [trRep_apply, hb, hbox g gd hg _ (hinvT φ₁ hφ₁) _ (hinvS φ₂ hφ₂),
    hTbox _ (hs.pres g _ (hinvT φ₁ hφ₁)) _ (hinvS φ₂ hφ₂), LinearEquiv.apply_symm_apply, trRep_apply]

theorem symp_transpose {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [Fintype β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix β α E) :
    symp c ξ JB JA x y = symp c ξ JA JB xᵀ yᵀ := by
  unfold symp hTens
  congr 2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  ring

def transpCoord {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {α β : Type} [Fintype α] [Fintype β] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    (d : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans d.e
  form w w' := by
    rw [symp_transpose, d.form]
    rfl

theorem transpCoord_e {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {α β : Type} [Fintype α] [Fintype β] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    (d : Darboux (symp c ξ JA JB) κ) (x : Matrix α β E) : (transpCoord d).e xᵀ = d.e x := rfl

theorem isUWeilPair_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    [TopologicalSpace E] [IsModuleTopology R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T) (hD : HasDbl c C ψ ξ JA JB d d₁ T)
    (hD' : ∀ d' d₁' : Darboux (symp c ξ JB JA) κ, (∀ x : Matrix α β E, d'.e xᵀ = d.e x) → (∀ x : Matrix α β E, d₁'.e xᵀ = d₁.e x) →
      HasDbl c C ψ ξ JB JA d' d₁' T)
    {χA χB : Eˣ →* Circle} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilPair c C ψ ξ JA JB d χA χB om) : IsUWeilPair c C ψ ξ JA JB d₁ χA χB (trRep T om) := by
  have hsplit := isUSplitting_trRep hT h.isUSplitting
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  have hT' : IsGoodInt C ψ d' (transpCoord d₁) T := by
    obtain ⟨h1, h2, h3, h4⟩ := hT
    refine ⟨h1, fun w φ hφ => ?_, h3, h4⟩
    have e1 : d'.e w = d.e wᵀ := by rw [← hd', Matrix.transpose_transpose]
    have e2 : (transpCoord d₁).e w = d₁.e wᵀ := by rw [← transpCoord_e d₁ wᵀ, Matrix.transpose_transpose]
    have := h2 wᵀ φ hφ
    simp only [Darboux.rho] at this ⊢
    rw [e1, e2, this]
  exact ⟨isUWeilB_trRep hT hD hB, ⟨transpCoord d₁, transpCoord_e d₁, isUWeilB_trRep hT' (hD' d' _ hd' (transpCoord_e d₁)) hA⟩, hsplit.cont⟩

end GlobalTheory.WeilTr

end
