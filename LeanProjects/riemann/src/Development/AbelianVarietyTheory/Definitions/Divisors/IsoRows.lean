import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

section Coord

variable {R : Type} [CommRing R] {κ κ₁ : Type}

def ext0 (j : κ₁ → κ) (x : κ₁ → R) : κ → R := Function.extend j x 0

def ev (j : κ₁ → κ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ) := LinearMap.funLeft ℂ ℂ (ext0 j)

variable [Fintype κ] [Fintype κ₁] {W W₁ : Type} [AddCommGroup W] [Module R W] [AddCommGroup W₁] [Module R W₁]
  {B : W → W → R} {B₁ : W₁ → W₁ → R}

def Over (j : κ₁ → κ) (d : Darboux B κ) (d₁ : Darboux B₁ κ₁) (v : W) (z : W₁) : Prop :=
  (d.e v).1 = ext0 j (d₁.e z).1 ∧ (d.e v).2 ∘ j = (d₁.e z).2

structure IsAct {G : Type} [Group G] (act : G → W → W) : Prop where
  one : ∀ w, act 1 w = w
  mul : ∀ g h w, act (g * h) w = act g (act h w)
  add : ∀ g w w', act g (w + w') = act g w + act g w'

end Coord

section Frame

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α α₁ ν : Type} [Fintype α] [DecidableEq α] [Fintype α₁] [DecidableEq α₁] [Fintype ν] [DecidableEq ν]

structure IsFrame (J : Matrix α α A) (C D : Matrix α ν A) (ι : Matrix α α₁ A) : Prop where
  cc : Cᵀ * J * C.map c = 0
  dd : Dᵀ * J * D.map c = 0
  cd : Cᵀ * J * D.map c = 1
  ic : ιᵀ * J * C.map c = 0
  ci : Cᵀ * J * ι.map c = 0
  id : ιᵀ * J * D.map c = 0
  di : Dᵀ * J * ι.map c = 0
  basis : ∃ M : Matrix ((ν ⊕ ν) ⊕ α₁) α A, Matrix.fromCols (Matrix.fromCols C D) ι * M = 1 ∧
    M * Matrix.fromCols (Matrix.fromCols C D) ι = 1

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def ratV {κ : Type} (ξ : κ → F) : κ → AF F := fun i => algebraMap F (AF F) (ξ i)

def IsRat {α β κ : Type} [Fintype κ] {B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F} (d : Darboux B κ) : Prop :=
  ∀ x : Matrix α β E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

structure IsInter (ψ : AddChar (AF F) ℂ) {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (d : Darboux B κ) (d' : Darboux B κ') (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ))
    (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop where
  pres : ∀ φ ∈ schA F κ, S φ ∈ schA F κ'
  pres' : ∀ φ ∈ schA F κ', S' φ ∈ schA F κ
  left : ∀ φ ∈ schA F κ, S' (S φ) = φ
  right : ∀ φ ∈ schA F κ', S (S' φ) = φ
  adm : ∀ l ∈ (adeleClass F).adm κ', l ∘ₗ S ∈ (adeleClass F).adm κ
  adm' : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ S' ∈ (adeleClass F).adm κ'
  Heisenberg₂ : ∀ w, ∀ φ ∈ schA F κ, S (d.rho ψ w φ) = d'.rho ψ w (S φ)
  theta : ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F κ, thetaSum F (S φ) = c * thetaSum F φ
  norm : ∀ (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ' →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

variable (σ : E →ₐ[F] E)

abbrev sy {n m : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin n) (Fin m) (AE F E) → Matrix (Fin n) (Fin m) (AE F E) → AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)

def unipU {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (C : Matrix (Fin n) (Fin r) E) : Subgroup (UA σ J) :=
  Subgroup.closure {g | (mat g - 1) * incM F C = 0 ∧ (mat g - 1)ᵀ * incM F (J * C.map σ) = 0 ∧
    ∀ x : Fin n → E, x ᵥ* (J * C.map σ) = 0 →
      ∃ a : Fin r → AE F E, (mat g - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = incM F C *ᵥ a}

def IsCuspU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : UA σ J → ℂ) : Prop :=
  ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E), 0 < r → LinearIndependent E C.transpose → Cᵀ * J * C.map σ = 0 →
    ∀ (μ : Measure (unipU σ J C)) (𝓕 : Set (unipU σ J C)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ J).subgroupOf (unipU σ J C)) 𝓕 μ → ∀ g, ∫ u in 𝓕, f (u.1 * g) ∂μ = 0

structure IsMixL {n m n₁ r : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin m) (Fin m) E}
    {J₁ : Matrix (Fin n₁) (Fin n₁) E} (C D : Matrix (Fin n) (Fin r) E) (ι : Matrix (Fin n) (Fin n₁) E) {κ κ₁ : Type}
    [Fintype κ] [Fintype κ₁] (j : κ₁ → κ) (co : Darboux (sy σ JX JW) κ) (co₁ : Darboux (sy σ J₁ JW) κ₁) : Prop where
  frame : IsFrame σ JX C D ι
  gram : J₁ = ιᵀ * JX * ι.map σ
  inj : Function.Injective j
  rat : IsRat co
  rat₁ : IsRat co₁
  ovr : ∀ v z, Over j co co₁ v z ↔ ∃ y : Matrix (Fin r) (Fin m) (AE F E), v = incM F ι * z + incM F C * y
  dual : ∀ v, ((co.e v).2 = 0 ∧ (co.e v).1 ∘ j = 0) ↔ ∃ w : Matrix (Fin r) (Fin m) (AE F E), v = incM F D * w
  dualRat : ∀ ξ : κ → F, ξ ∘ j = 0 → ∃ w : Matrix (Fin r) (Fin m) E, co.e (incM F (D * w)) = (ratV F ξ, 0)

structure IsMixR {n m m₁ r : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin m) (Fin m) E}
    {J₁ : Matrix (Fin m₁) (Fin m₁) E} (C D : Matrix (Fin m) (Fin r) E) (ι : Matrix (Fin m) (Fin m₁) E) {κ κ₁ : Type}
    [Fintype κ] [Fintype κ₁] (j : κ₁ → κ) (co : Darboux (sy σ JX JW) κ) (co₁ : Darboux (sy σ JX J₁) κ₁) : Prop where
  frame : IsFrame σ JW C D ι
  gram : J₁ = ιᵀ * JW * ι.map σ
  inj : Function.Injective j
  rat : IsRat co
  rat₁ : IsRat co₁
  ovr : ∀ v z, Over j co co₁ v z ↔ ∃ y : Matrix (Fin n) (Fin r) (AE F E), v = z * (incM F ι)ᵀ + y * (incM F C)ᵀ

variable {σ}

def term (ψ : AddChar (AF F) ℂ) {n m r : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin m) (Fin m) E}
    (D : Matrix (Fin n) (Fin r) E) {κ κ₁ : Type} [Fintype κ] (j : κ₁ → κ) (co : Darboux (sy σ JX JW) κ)
    (w : Matrix (Fin r) (Fin m) E) (Φ : (κ → AF F) → ℂ) : ℂ :=
  thetaSum F (ev j (co.rho ψ (incM F (D * w)) Φ))

variable (σ) in

abbrev IsoRows {m : ℕ} (JW : Matrix (Fin m) (Fin m) E) (r : ℕ) : Type :=
  {w : Matrix (Fin r) (Fin m) E // w ≠ 0 ∧ w * JW * (w.map σ)ᵀ = 0}

example {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsFrame σ J (0 : Matrix (Fin n) (Fin 0) E) 0 (1 : Matrix (Fin n) (Fin n) E) := by
  refine ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
    Subsingleton.elim _ _, Subsingleton.elim _ _, Matrix.fromRows 0 1, ?_, ?_⟩
  · simp [Matrix.fromCols_mul_fromRows]
  · ext (a | a) (b | b)
    · rcases a with a | a <;> exact a.elim0
    · rcases a with a | a <;> exact a.elim0
    · rcases b with b | b <;> exact b.elim0
    · simp [Matrix.one_apply]

end GlobalTheory.TowU

end
