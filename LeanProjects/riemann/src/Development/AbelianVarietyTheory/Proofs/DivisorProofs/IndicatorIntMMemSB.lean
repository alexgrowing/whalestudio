import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

open MeasureTheory ValuativeRel Matrix Filter Topology
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

namespace GlobalTheory.KSplit

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSmU (χ : kˣ →* ℂˣ) : Prop := IsOpen (χ.ker : Set kˣ) ∧ ∀ x, ‖(χ x : ℂ)‖ = 1

theorem isSmU_one : IsSmU (1 : kˣ →* ℂˣ) := ⟨by simp, by simp⟩

variable (k) in

def intM (m n : Type) : Set (Matrix m n k) := {X | ∀ i j, X i j ∈ 𝒪[k]}

def IsEqv {n : ℕ} (ν : kˣ →* ℂˣ) (z : ℂ) (l : (Matrix (Fin n) (Fin n) k → ℂ) → ℂ) : Prop :=
  (∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∀ φ' ∈ SB (Matrix (Fin n) (Fin n) k), l (φ + φ') = l φ + l φ') ∧
  (∀ c : ℂ, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), l (c • φ) = c * l φ) ∧
  ∀ g₁ g₂ : GL (Fin n) k, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k),
    (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) z * l (fun X => φ (g₁.val * X * g₂.val)) = l φ

example (n : ℕ) : IsEqv (n := n) (1 : kˣ →* ℂˣ) 0 (fun φ => φ 0) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => by simp⟩

def indSp (a a' : ℕ) (α β : kˣ →* ℂˣ) : Submodule ℂ (GL (Fin (a + a')) k → ℂ) where
  carrier := {f | (∀ (b : GL (Fin (a + a')) k) (A : GL (Fin a) k) (D : GL (Fin a') k) (N : Matrix (Fin a) (Fin a') k),
      b.val.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks A.val N 0 D.val → ∀ h, f (b * h) =
        (α (gdet A) : ℂ) * β (gdet D) * apow (gdet A) ((a' : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * f h) ∧
    ∀ᶠ u in 𝓝 (1 : GL (Fin (a + a')) k), ∀ h, f (h * u) = f h}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun b A D N hb h => ?_, (h2.and h2').mono fun u hu h => ?_⟩
    · simp only [Pi.add_apply, h1 b A D N hb, h1' b A D N hb, mul_add]
    · simp only [Pi.add_apply, hu.1, hu.2]
  zero_mem' := ⟨fun _ _ _ _ _ _ => by simp, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun b A D N hb h => ?_, h2.mono fun u hu h => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, h1 b A D N hb]; ring
    · simp only [Pi.smul_apply, hu]

def mapA {a : ℕ} (a' : ℕ) (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (ν β : kˣ →* ℂˣ)
    (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (h : GL (Fin (a + a')) k) : ℂ :=
  l fun g => omA ν β 1 h Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))

def mapB (a : ℕ) {a' : ℕ} (l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ) (ν α : kˣ →* ℂˣ)
    (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ) (h : GL (Fin (a + a')) k) : ℂ :=
  l fun g => omB ν α 1 h Ψ (g * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))

section Frames

variable {R S D : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

theorem restrict_mem_SB {P : Matrix R D k} {P' : Matrix D R k} (hP : P * P' = 1) {Φ : Matrix R D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix R D k)) : (fun g : Matrix R R k => Φ (g * P)) ∈ SB (Matrix R R k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have c1 : Continuous fun g : Matrix R R k => g * P := continuous_id.matrix_mul continuous_const
  have c2 : Continuous fun X : Matrix R D k => X * P' := continuous_id.matrix_mul continuous_const
  have e : IsClosedEmbedding fun g : Matrix R R k => g * P :=
    Function.LeftInverse.isClosedEmbedding (f := fun X : Matrix R D k => X * P')
      (fun g => by simp only [Matrix.mul_assoc, hP, Matrix.mul_one]) c2 c1
  exact ⟨hΦ.1.comp_continuous c1, hΦ.2.comp_isClosedEmbedding e⟩

omit [DecidableEq R] [DecidableEq D] in

theorem indicator_intM_mem_SB : (intM k R D).indicator (1 : Matrix R D k → ℂ) ∈ SB (Matrix R D k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact (intM k R D) := isCompact_intMatrix
  have hK : IsClopen (intM k R D) := ⟨hc.isClosed, isOpen_intMatrix⟩
  exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩

theorem exists_extend_SB {P : Matrix R D k} {Q : Matrix S D k} (hP : P * Pᵀ = 1) (hQ : P * Qᵀ = 0)
    (hPQ : Pᵀ * P + Qᵀ * Q = 1) {φ : Matrix R R k → ℂ} (hφ : φ ∈ SB (Matrix R R k)) :
    ∃ Φ ∈ SB (Matrix R D k), ∀ g, Φ (g * P) = φ g := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hI := indicator_intM_mem_SB (k := k) (R := R) (D := S)
  have c1 : Continuous fun X : Matrix R D k => X * Pᵀ := continuous_id.matrix_mul continuous_const
  have c2 : Continuous fun X : Matrix R D k => X * Qᵀ := continuous_id.matrix_mul continuous_const
  have c3 : Continuous fun x : Matrix R R k × Matrix R S k => x.1 * P + x.2 * Q :=
    (continuous_fst.matrix_mul continuous_const).add (continuous_snd.matrix_mul continuous_const)
  refine ⟨fun X => φ (X * Pᵀ) * (intM k R S).indicator 1 (X * Qᵀ),
    ⟨(hφ.1.comp_continuous c1).mul (hI.1.comp_continuous c2), ?_⟩, fun g => ?_⟩
  · refine HasCompactSupport.intro ((hφ.2.isCompact.prod hI.2.isCompact).image c3) fun X hX => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    refine hX ⟨(X * Pᵀ, X * Qᵀ), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩
    simp only [Matrix.mul_assoc, ← Matrix.mul_add, hPQ, Matrix.mul_one]
  · simp only [Matrix.mul_assoc, hP, hQ, Matrix.mul_one, Matrix.mul_zero]
    rw [Set.indicator_of_mem (show (0 : Matrix R S k) ∈ intM k R S from fun _ _ => zero_mem _)]
    simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem frame_rel (σ : R ⊕ S ≃ D) : X0 k σ * (X0 k σ)ᵀ = 1 ∧ Y0 k σ * (Y0 k σ)ᵀ = 1 ∧ X0 k σ * (Y0 k σ)ᵀ = 0 ∧
    Y0 k σ * (X0 k σ)ᵀ = 0 ∧ (X0 k σ)ᵀ * X0 k σ + (Y0 k σ)ᵀ * Y0 k σ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; rw [frameMatrixFirstColumnBlock_mul_apply]; simp [X0, one_apply, eq_comm]
  · ext i j; rw [frameMatrixSecondColumnBlock_mul_apply]; simp [Y0, one_apply, eq_comm]
  · ext i j; simp [frameMatrixFirstColumnBlock_mul_apply, Y0]
  · ext i j; simp [frameMatrixSecondColumnBlock_mul_apply, X0]
  · ext i j
    obtain ⟨i | i, rfl⟩ := σ.surjective i <;> obtain ⟨j | j, rfl⟩ := σ.surjective j <;>
      simp [X0, Y0, Matrix.mul_apply, one_apply, eq_comm]

end Frames

variable {a a' : ℕ} {z : ℂ} {ν α β : kˣ →* ℂˣ}

theorem restrict_X0 {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (hΦ : Φ ∈ SB (Matrix (Fin a) (Fin (a + a')) k)) :
    (fun g : Matrix (Fin a) (Fin a) k => Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _ :=
  restrict_mem_SB (frame_rel _).1 hΦ

theorem restrict_Y0 {Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ} (hΨ : Ψ ∈ SB (Matrix (Fin a') (Fin (a + a')) k)) :
    (fun g : Matrix (Fin a') (Fin a') k => Ψ (g * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _ :=
  restrict_mem_SB (frame_rel _).2.1 hΨ

theorem mapA_omA_right (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ)
    (x h : GL (Fin (a + a')) k) : mapA a' l ν β (omA ν β 1 x Φ) h = mapA a' l ν β Φ (h * x) := by
  unfold mapA
  rw [← omA_mul, one_mul]

theorem mapB_omB_right (l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ) (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ)
    (x h : GL (Fin (a + a')) k) : mapB a l ν α (omB ν α 1 x Ψ) h = mapB a l ν α Ψ (h * x) := by
  unfold mapB
  rw [← omB_mul, one_mul]

end Local

section Adelic

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def locMat {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v)) :
    UA σ J →* GL (Fin n) (Fv F v) where
  toFun g := b⁻¹ * Matrix.GeneralLinearGroup.map (piW t) g.1 * b
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

theorem locMat_val {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v))
    (g : UA σ J) : (locMat t b g).val = (b⁻¹).val * (mat g).map (piW t) * b.val := rfl

end Adelic

end GlobalTheory.KSplit

end
