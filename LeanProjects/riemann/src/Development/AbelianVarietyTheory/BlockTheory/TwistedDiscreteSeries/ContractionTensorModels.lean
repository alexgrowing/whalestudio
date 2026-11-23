import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]

def IsIsoBilin (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Prop :=
  ∀ x x' y y', ⟪Tm x y, Tm x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ

def IsEquivBilin {G₁ G₂ : Type} [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)) (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂))
    (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Prop :=
  ∀ g h x y, Tm (π₁ g x) (π₂ h y) = ρ (g, h) (Tm x y)

def IsContr (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) (It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁) : Prop :=
  ∀ φ y x, ⟪x, It φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ

def HasWeakDer {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (c : ℝ → H) (v' : H) : Prop :=
  ∀ w : H, HasDerivAt (fun t : ℝ => ⟪w, c t⟫_ℂ) ⟪w, v'⟫_ℂ 0

def IsFiniteVec {G H : Type} [Group G] [AddCommGroup H] [Module ℂ H] (K : Subgroup G) (π : G → H → H) (v : H) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => π k v))

def imSpan (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Submodule ℂ FF :=
  Submodule.span ℂ (Set.range fun p : H₁ × H₂ => Tm p.1 p.2)

structure ContrProps {G₁ G₂ : Type} [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁))
    (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂)) (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF)
    (It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁) : Prop where

  norm_le : ∀ φ y, ‖It φ y‖ ≤ ‖φ‖ * ‖y‖

  equiv : ∀ g φ y, It (ρ (g, 1) φ) y = π₁ g (It φ y)

  inv : ∀ h φ y, It (ρ (1, h) φ) (π₂ h y) = It φ y

  der₁ : ∀ (c : Multiplicative ℝ →* G₁) φ φ' y,
    HasDerivAt (fun t : ℝ => ρ (c (Multiplicative.ofAdd t), 1) φ) φ' 0 →
      HasDerivAt (fun t : ℝ => π₁ (c (Multiplicative.ofAdd t)) (It φ y)) (It φ' y) 0

  weakDer₁ : ∀ (c : Multiplicative ℝ →* G₁) φ φ' y,
    HasWeakDer (fun t : ℝ => ρ (c (Multiplicative.ofAdd t), 1) φ) φ' →
      HasWeakDer (fun t : ℝ => π₁ (c (Multiplicative.ofAdd t)) (It φ y)) (It φ' y)

  der₂ : ∀ (c : Multiplicative ℝ →* G₂) φ φ' y y',
    HasWeakDer (fun t : ℝ => ρ (1, c (Multiplicative.ofAdd t)) φ) φ' →
      HasWeakDer (fun t : ℝ => π₂ (c (Multiplicative.ofAdd t)) y) y' → It φ' y + It φ y' = 0

  ne : ∀ φ, φ ∉ (imSpan Tm)ᗮ → ∀ Y : Set H₂, Dense Y → ∃ y ∈ Y, It φ y ≠ 0

  fin : ∀ (K : Subgroup G₁) φ y, IsFiniteVec K (fun g => ρ (g, 1)) φ → IsFiniteVec K (fun g => π₁ g) (It φ y)

end Hilbert

def ContrHilbert : Prop :=
  ∀ (H₁ H₂ FF : Type)
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]
    (G₁ G₂ : Type) [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)) (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂))
    (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF),
    IsIsoBilin Tm → IsEquivBilin π₁ π₂ ρ Tm →
      (∃! It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It) ∧
      ∀ It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It → ContrProps π₁ π₂ ρ Tm It

def IsTensorIt {ι : Type} [Fintype ι] {σ : ι → Type} {Var : Type} (e : (Σ τ, σ τ) ≃ Var) {A B : ι → Type}
    [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)]
    (Itl : ∀ τ, MvPolynomial (σ τ) ℂ →ₗ[ℂ] A τ →ₗ[ℂ] B τ)
    (It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ) : Prop :=
  ∀ (P : ∀ τ, MvPolynomial (σ τ) ℂ) (v : ∀ τ, A τ),
    It (∏ τ, MvPolynomial.rename (fun s => e ⟨τ, s⟩) (P τ)) (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ fun τ => Itl τ (P τ) (v τ)

def ContrTensor : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : ι → Type) (Var : Type) (e : (Σ τ, σ τ) ≃ Var) (A B : ι → Type)
    [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)]
    (Itl : ∀ τ, MvPolynomial (σ τ) ℂ →ₗ[ℂ] A τ →ₗ[ℂ] B τ),
    ∃ It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ,
      IsTensorIt e Itl It ∧ ((∀ τ, Itl τ ≠ 0) → It ≠ 0)

def Contraction : Prop := ContrHilbert ∧ ContrTensor

section Models

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ContrTensorModels : Prop :=
  ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (Itl : ∀ τ, MvPolynomial (Fin W.rank × Fin V.rank) ℂ →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ),
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      (∀ (P : D.what₂.Tau → MvPolynomial (Fin W.rank × Fin V.rank) ℂ) (v : M'.Vec),
        It (∏ τ, MvPolynomial.rename (fun s => (τ, s)) (P τ)) (PiTensorProduct.tprod ℂ v) =
          PiTensorProduct.tprod ℂ fun τ => Itl τ (P τ) (v τ)) ∧
      ((∀ τ, Itl τ ≠ 0) → It ≠ 0)

theorem contrTensorModels_of (h : ContrTensor) : ContrTensorModels := fun D V W _ _ M M' Itl =>
  h D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) _ (Equiv.sigmaEquivProd _ _) (fun τ => M'.sm τ)
    (fun τ => M.sm τ) Itl

end Models

example (a b x y : ℂ) : LinearMap.mul ℂ ℂ (a * x) (b * y) = (a * b) * LinearMap.mul ℂ ℂ x y := by
  simp only [LinearMap.mul_apply']; ring

example (It : ℂ →ₗ[ℂ] ℂ →ₛₗ[starRingEnd ℂ] ℂ) (h : IsContr (LinearMap.mul ℂ ℂ) It) (φ y : ℂ) :
    It φ y = φ * starRingEnd ℂ y := by
  have := h φ y 1
  simpa using this

theorem contrProps_of {H₁ H₂ FF : Type}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]
    {G₁ G₂ : Type} [Group G₁] [Group G₂] {π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)} {π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂)}
    {ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)} {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm)
    (hE : IsEquivBilin π₁ π₂ ρ Tm) {It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁} (hC : IsContr Tm It) :
    ContrProps π₁ π₂ ρ Tm It := by
  have hn : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hI x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hb : ∀ φ y, ‖It φ y‖ ≤ ‖φ‖ * ‖y‖ := by
    intro φ y
    have h := hC φ y (It φ y)
    have h1 : ‖It φ y‖ * ‖It φ y‖ ≤ ‖It φ y‖ * (‖φ‖ * ‖y‖) := by
      have := norm_inner_le_norm (𝕜 := ℂ) (Tm (It φ y) y) φ
      rw [← h, hn, inner_self_eq_norm_sq_to_K] at this
      simp at this
      nlinarith
    rcases (norm_nonneg (It φ y)).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_left h1 h0
  have hall : ∀ g h φ y, It (ρ (g, h) φ) (π₂ h y) = π₁ g (It φ y) := by
    intro g h φ y
    apply ext_inner_left ℂ
    intro x
    obtain ⟨x, rfl⟩ := (π₁ g).surjective x
    rw [hC, hE, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map, hC]
  have he : ∀ g φ y, It (ρ (g, 1) φ) y = π₁ g (It φ y) := fun g φ y => by simpa using hall g 1 φ y
  have hi : ∀ h φ y, It (ρ (1, h) φ) (π₂ h y) = It φ y := fun h φ y => by simpa using hall 1 h φ y
  refine ⟨hb, he, hi, ?_, ?_, ?_, ?_, ?_⟩
  · intro c φ φ' y hd
    let L : FF →L[ℂ] H₁ := (It.flip y).mkContinuous ‖y‖ fun φ => by simpa [mul_comm] using hb φ y
    have := ((L.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hd
    simpa [L, Function.comp_def, he] using this
  · intro c φ φ' y hd w
    simpa only [← he, hC _ _ _] using hd (Tm w y)
  · intro c φ φ' y y' hd hd'
    apply ext_inner_left ℂ
    intro x
    let ℓ : H₂ →L[ℂ] ℂ := ((innerₛₗ ℂ φ) ∘ₗ Tm x).mkContinuous (‖φ‖ * ‖x‖) fun y => by
      simpa [hn, mul_assoc] using norm_inner_le_norm (𝕜 := ℂ) φ (Tm x y)
    obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℂ H₂).surjective ℓ
    have hw' : ∀ z, ⟪w, z⟫_ℂ = ⟪φ, Tm x z⟫_ℂ := fun z => by
      have := congrArg (fun f : H₂ →L[ℂ] ℂ => f z) hw
      simpa [ℓ] using this
    have h1 := hd (Tm x y)
    have h2 := ((hd' w).scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)).star
    have h3 : (fun t : ℝ => ⟪Tm x y, ρ (1, c (Multiplicative.ofAdd t)) φ⟫_ℂ) =
        fun t : ℝ => star (((fun t : ℝ => ⟪w, π₂ (c (Multiplicative.ofAdd t)) y⟫_ℂ) ∘ Neg.neg) t) := by
      funext t
      have hy : y = π₂ (c (Multiplicative.ofAdd t)) (π₂ (c (Multiplicative.ofAdd (-t))) y) := by
        change y = (π₂ _ * π₂ _) y
        rw [← map_mul, ← map_mul, ← ofAdd_add]; simp
      simp only [Function.comp, hw']
      rw [← hC, Complex.star_def, inner_conj_symm, ← hC]
      conv_lhs => rw [hy, hi]
    rw [h3] at h1
    have h4 := h1.unique h2
    rw [inner_add_right, hC, hC, h4, hw']
    simp
  · intro φ hφ Y hY
    by_contra hcon
    push_neg at hcon
    apply hφ
    let L : H₂ →SL[starRingEnd ℂ] H₁ := (It φ).mkContinuous ‖φ‖ (hb φ)
    have h0 : ∀ y, It φ y = 0 := fun y =>
      congrFun (Continuous.ext_on hY L.continuous (continuous_const (y := (0 : H₁))) hcon) y
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨p, rfl⟩ := hu; simp [← hC φ, h0]
    | zero => simp
    | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
    | smul a b _ hb => simp [inner_smul_left, hb]
  · intro K φ y hf
    unfold IsFiniteVec at *
    have : (Set.range fun k : K => π₁ k (It φ y)) = It.flip y '' Set.range fun k : K => ρ (k, 1) φ := by
      rw [← Set.range_comp]; congr 1; funext k; simp [he]
    rw [this, ← Submodule.map_span]
    infer_instance

def contrMul : ℂ →ₗ[ℂ] ℂ →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun φ y => φ * starRingEnd ℂ y)
    (fun a b y => by ring) (fun c a y => by simp [mul_assoc]) (fun a y z => by simp [mul_add])
    (fun c a y => by simp; ring)

def circ : Circle →* (ℂ ≃ₗᵢ[ℂ] ℂ) where
  toFun a := { LinearEquiv.smulOfNeZero ℂ ℂ (a : ℂ) a.coe_ne_zero with norm_map' := fun z => by simp [Circle.norm_coe a] }
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

end
