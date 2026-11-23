import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.SplitUnitary

open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)

section Group

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)

def stdJ (ν E : Type) [DecidableEq ν] [Field E] : Matrix (ν ⊕ ν) (ν ⊕ ν) E := fromBlocks 0 1 (-1) 0

variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem stdJ_mul_stdJ : stdJ ν E * stdJ ν E = -1 := by
  simp [stdJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem mem_UG_iff (g : GL (ν ⊕ ν) E) :
    g ∈ UG c (stdJ ν E) ↔
      (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E) * stdJ ν E * ((g : Matrix (ν ⊕ ν) (ν ⊕ ν) E).map c)ᵀ = stdJ ν E := by
  have hT : (stdJ ν E)ᵀ = -stdJ ν E := by simp [stdJ, fromBlocks_transpose, fromBlocks_neg]
  have key : ∀ A B : Matrix (ν ⊕ ν) (ν ⊕ ν) E, A * stdJ ν E * B = stdJ ν E → B * stdJ ν E * A = stdJ ν E := by
    intro A B h
    have h1 : A * (stdJ ν E * B * -stdJ ν E) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_neg, stdJ_mul_stdJ, neg_neg]
    have h2 := mul_eq_one_comm.mp h1
    calc B * stdJ ν E * A = (stdJ ν E * stdJ ν E) * (B * -stdJ ν E * A) := by
          rw [stdJ_mul_stdJ]; simp
      _ = stdJ ν E * (stdJ ν E * B * -stdJ ν E * A) := by simp only [Matrix.mul_assoc]
      _ = stdJ ν E := by rw [h2, Matrix.mul_one]
  have tr : ∀ A B : Matrix (ν ⊕ ν) (ν ⊕ ν) E, A * stdJ ν E * B = stdJ ν E → Bᵀ * stdJ ν E * Aᵀ = stdJ ν E := by
    intro A B h
    have h1 := congrArg Matrix.transpose h
    rw [transpose_mul, transpose_mul, hT, ← Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul] at h1
    exact neg_injective h1
  constructor
  · intro h
    have h1 := tr _ _ (show (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E)ᵀ * stdJ ν E * (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E).map c = _ from h)
    rw [transpose_transpose] at h1
    exact key _ _ h1
  · intro h
    have h1 := tr _ _ (key _ _ h)
    rw [transpose_transpose] at h1
    exact h1

def levi (hc : ∀ z, c (c z) = z) (a : GL ν E) : UG c (stdJ ν E) :=
  ⟨⟨fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ,
    fromBlocks ((a⁻¹ : GL ν E) : Matrix ν ν E) 0 0 ((a : Matrix ν ν E).map c)ᵀ, by
      rw [fromBlocks_multiply, ← transpose_mul, ← Matrix.map_mul (f := c), Units.mul_inv,
        Matrix.map_one _ (map_zero c) (map_one c)]
      simp, by
      rw [fromBlocks_multiply, ← transpose_mul, ← Matrix.map_mul (f := c), Units.inv_mul,
        Matrix.map_one _ (map_zero c) (map_one c)]
      simp⟩, by
    rw [mem_UG_iff]
    have h1 : ∀ A : Matrix ν ν E, (A.map c)ᵀ.map c = Aᵀ := fun A => by ext i j; simp [hc]
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    simp only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h1, h0, transpose_transpose,
      transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, neg_zero]
    rw [← transpose_mul, ← Matrix.map_mul (f := c), Units.mul_inv,
      Matrix.map_one _ (map_zero c) (map_one c), transpose_one]⟩

theorem levi_val (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    ((levi c hc a : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) =
      fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ := rfl

def form (Q : Matrix α α E) (w w' : Matrix α (ν ⊕ ν) E) : F :=
  2⁻¹ * Algebra.trace F E (hTens c Q (stdJ ν E) w w')

def heisFun (ψ : AddChar F ℂ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  fun x => ψ (form c Q (fromCols x 0) (fromCols 0 w.toCols₂) +
    2⁻¹ * form c Q (fromCols w.toCols₁ 0) (fromCols 0 w.toCols₂)) * φ (x + w.toCols₁)

omit [DecidableEq α] in
theorem hTens_eq (Q : Matrix α α E) (w w' : Matrix α (ν ⊕ ν) E) :
    hTens c Q (stdJ ν E) w w' = ∑ i, ∑ k, Q i k * (w * stdJ ν E * (w'.map c)ᵀ) i k := by
  simp only [hTens, mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq α] in

theorem form_mul (Q : Matrix α α E) (g : UG c (stdJ ν E)) (w w' : Matrix α (ν ⊕ ν) E) :
    form c Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (w' * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) =
      form c Q w w' := by
  have h := (mem_UG_iff c _).mp g.2
  rw [form, form, hTens_eq, hTens_eq, Matrix.map_mul (f := c), transpose_mul]
  conv_rhs => rw [← h]
  simp only [Matrix.mul_assoc]

omit [DecidableEq α] in
theorem form_add_left (Q : Matrix α α E) (w₁ w₂ w' : Matrix α (ν ⊕ ν) E) :
    form c Q (w₁ + w₂) w' = form c Q w₁ w' + form c Q w₂ w' := by
  simp only [form, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]

omit [DecidableEq α] in
theorem form_add_right (Q : Matrix α α E) (w w₁ w₂ : Matrix α (ν ⊕ ν) E) :
    form c Q w (w₁ + w₂) = form c Q w w₁ + form c Q w w₂ := by
  simp only [form, hTens, Matrix.add_apply, Finset.sum_add_distrib, map_add, mul_add]

theorem form_swap (hc : ∀ z, c (c z) = z) {Q : Matrix α α E} (hQ : IsHerm c Q) (w w' : Matrix α (ν ⊕ ν) E) :
    form c Q w' w = -form c Q w w' := by
  have hJ : ∀ j l, c (stdJ ν E j l) = -stdJ ν E l j := by
    rintro (j | j) (l | l) <;> simp [stdJ, one_apply, eq_comm]
  have h : hTens c Q (stdJ ν E) w' w = -c (hTens c Q (stdJ ν E) w w') := by
    simp only [hTens, map_sum, map_mul, hc, hJ, hQ.1, ← Finset.sum_neg_distrib]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    exact Fintype.sum_equiv ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by simp only [Equiv.coe_fn_mk]; ring
  have ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z
  rw [form, form, h, map_neg, ht, mul_neg]

omit [DecidableEq α] in

theorem form_left_left (Q : Matrix α α E) (x x' : Matrix α ν E) : form c Q (fromCols x 0) (fromCols x' 0) = 0 := by
  simp [form, hTens, stdJ, Fintype.sum_sum_type]

omit [DecidableEq α] in

theorem form_right_right (Q : Matrix α α E) (y y' : Matrix α ν E) : form c Q (fromCols 0 y) (fromCols 0 y') = 0 := by
  simp [form, hTens, stdJ, Fintype.sum_sum_type]

theorem heisFun_heisFun [CharZero F] (hc : ∀ z, c (c z) = z) (ψ : AddChar F ℂ) {Q : Matrix α α E} (hQ : IsHerm c Q)
    (w w' : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) :
    heisFun c ψ Q w (heisFun c ψ Q w' φ) = ψ (2⁻¹ * form c Q w w') • heisFun c ψ Q (w + w') φ := by
  have e1 : ∀ x x' : Matrix α ν E, fromCols (x + x') (0 : Matrix α ν E) = fromCols x 0 + fromCols x' 0 := fun x x' => by
    ext i (j | j) <;> simp
  have e2 : ∀ y y' : Matrix α ν E, fromCols (0 : Matrix α ν E) (y + y') = fromCols 0 y + fromCols 0 y' := fun x x' => by
    ext i (j | j) <;> simp
  have e3 : ∀ u : Matrix α (ν ⊕ ν) E, u = fromCols u.toCols₁ 0 + fromCols 0 u.toCols₂ := fun u => by
    ext i (j | j) <;> simp
  have e4 : form c Q w w' = form c Q (fromCols w.toCols₁ 0) (fromCols 0 w'.toCols₂) -
      form c Q (fromCols w'.toCols₁ 0) (fromCols 0 w.toCols₂) := by
    conv_lhs => rw [e3 w, e3 w']
    rw [form_add_left, form_add_right, form_add_right, form_left_left, form_right_right,
      form_swap c hc hQ (fromCols w'.toCols₁ 0)]
    ring
  funext x
  rw [Pi.smul_apply, heisFun, heisFun, heisFun, show (w + w').toCols₁ = w.toCols₁ + w'.toCols₁ from rfl,
    show (w + w').toCols₂ = w.toCols₂ + w'.toCols₂ from rfl, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x, e4]
  congr 2
  simp only [e1, e2, form_add_left, form_add_right]
  ring

omit [DecidableEq α] in

theorem heisFun_levi (hc : ∀ z, c (c z) = z) (ψ : AddChar F ℂ) (Q : Matrix α α E) (a : GL ν E) (w : Matrix α (ν ⊕ ν) E)
    (φ : Matrix α ν E → ℂ) :
    heisFun c ψ Q w (fun x => φ (x * (a : Matrix ν ν E))) =
      fun x => heisFun c ψ Q (w * ((levi c hc a : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) φ (x * (a : Matrix ν ν E)) := by
  have e : ∀ x y : Matrix α ν E, fromCols x y * ((levi c hc a : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) =
      fromCols (x * (a : Matrix ν ν E)) (y * (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ) := fun x y => by
    rw [levi_val, fromCols_mul_fromBlocks]; simp
  have f : ∀ x y : Matrix α ν E, form c Q (fromCols (x * (a : Matrix ν ν E)) 0)
      (fromCols 0 (y * (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ)) = form c Q (fromCols x 0) (fromCols 0 y) := fun x y => by
    rw [← form_mul c Q (levi c hc a) (fromCols x 0), e, e, Matrix.zero_mul, Matrix.zero_mul]
  funext x
  conv_rhs => rw [← fromCols_toCols w, e]
  simp only [heisFun, toCols₁_fromCols, toCols₂_fromCols, f, Matrix.add_mul]

end Group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem continuous_form_left (Q : Matrix α α E) (w' : Matrix α (ν ⊕ ν) E) :
    Continuous fun x : Matrix α ν E => form c Q (fromCols x 0) w' := by
  have h : ∀ e : E, Continuous fun z : E => Algebra.trace F E (z * e) := fun e =>
    IsModuleTopology.continuous_of_linearMap ((Algebra.trace F E).comp (LinearMap.mulRight F e))
  simp only [form, hTens, map_sum, mul_assoc]
  refine continuous_const.mul (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ => (h _).comp ?_)
  rcases j with j | j
  · exact continuous_id.matrix_elem i j
  · exact continuous_const

theorem heisFun_mem {ψ : AddChar F ℂ} (hψ : Continuous ψ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E)
    {φ : Matrix α ν E → ℂ} (hφ : φ ∈ SB (Matrix α ν E)) : heisFun c ψ Q w φ ∈ SB (Matrix α ν E) := by
  haveI := IsModuleTopology.topologicalAddGroup F E
  haveI := GlobalTheory.WeilM.nonarch_field F
  have h1 := (GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous
    ((continuous_form_left c Q (fromCols 0 w.toCols₂)).add (continuous_const
      (y := 2⁻¹ * form c Q (fromCols w.toCols₁ 0) (fromCols 0 w.toCols₂))))
  exact ⟨h1.mul (hφ.1.comp_continuous (continuous_id.add continuous_const)),
    (hφ.2.comp_homeomorph (Homeomorph.addRight w.toCols₁)).mul_left⟩

def Heisenberg₂ {ψ : AddChar F ℂ} (hψ : Continuous ψ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E) :
    Module.End ℂ (SB (Matrix α ν E)) where
  toFun φ := ⟨heisFun c ψ Q w φ, heisFun_mem c hψ Q w φ.2⟩
  map_add' φ φ' := Subtype.ext (funext fun x => mul_add _ _ _)
  map_smul' z φ := Subtype.ext (funext fun x => mul_left_comm _ _ _)

theorem heis_apply {ψ : AddChar F ℂ} (hψ : Continuous ψ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E)
    (φ : SB (Matrix α ν E)) : (Heisenberg₂ c hψ Q w φ : Matrix α ν E → ℂ) = heisFun c ψ Q w φ := rfl

end Local

end GlobalTheory.SplitUnitary

namespace GlobalTheory.Published

open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.SplitUnitary

def KudlaSplittingSplitUnitary : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ)
    (α ν : Type) [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
    (Q : Matrix α α E) (_ : IsHerm c Q)
    (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1)
    (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)),
    ∃ ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E)),
      IsSmoothRep ω ∧
      (∀ μ : @Measure (Matrix α ν E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)),
          ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ) ∧
      (∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E),
        Heisenberg₂ c hψ Q w * ω g =
          ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) ∧
      ∀ (a : GL ν E) (φ : SB (Matrix α ν E)) (x : Matrix α ν E),
        (ω (levi c hE.invol a) φ : Matrix α ν E → ℂ) x =
          (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
            ((nabs F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) ^
              ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) *
            (φ : Matrix α ν E → ℂ) (x * (a : Matrix ν ν E))

end GlobalTheory.Published

end
