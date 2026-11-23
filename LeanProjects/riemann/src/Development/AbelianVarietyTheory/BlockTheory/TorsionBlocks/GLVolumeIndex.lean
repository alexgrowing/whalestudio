import Mathlib
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex

open MeasureTheory Matrix Finset ValuativeRel
open Formalism.MainNotions.ZetaProductPairs (qE zetaProd idxPar Lpair)
open scoped Classical

section Levels

variable {O : Type} [CommRing O] [IsLocalRing O]

abbrev red {m n : Type} (A : Matrix m n O) : Matrix m n (IsLocalRing.ResidueField O) :=
  A.map (IsLocalRing.residue O)

def princ (O : Type) [CommRing O] [IsLocalRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Subgroup (GL n O) :=
  (Matrix.GeneralLinearGroup.map (n := n) (IsLocalRing.residue O)).ker

theorem isUnit_of_red {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n O)
    (h : IsUnit (red A)) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
  have e : (red A).det = IsLocalRing.residue O A.det := (RingHom.map_det _ _).symm
  rw [e] at h
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h.ne_zero

theorem red_mul {l m n : Type} [Fintype m] (A : Matrix l m O) (B : Matrix m n O) :
    red (A * B) = red A * red B := by
  exact Matrix.map_mul

theorem red_add {m n : Type} (A B : Matrix m n O) : red (A + B) = red A + red B := by
  ext i j
  simp [red]

theorem red_eq_zero {m n : Type} (A : Matrix m n O) :
    red A = 0 ↔ ∀ i j, A i j ∈ IsLocalRing.maximalIdeal O := by
  rw [← Matrix.ext_iff]
  simp [red, IsLocalRing.residue_eq_zero_iff]

theorem exists_mem_of_red {n : Type} [Fintype n] [DecidableEq n] {J : Subgroup (GL n O)}
    (hJ : princ O n ≤ J) {k : GL n O} (hk : k ∈ J) {A : Matrix n n O}
    (h : red A = red (k : Matrix n n O)) : ∃ k' ∈ J, (k' : Matrix n n O) = A := by
  have hred1 : red (((k⁻¹ : GL n O) : Matrix n n O) * A) = 1 := by
    rw [red_mul, h, ← red_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    ext i j
    simp [red, Matrix.one_apply]
  have hu : IsUnit (((k⁻¹ : GL n O) : Matrix n n O) * A) := isUnit_of_red _ (by rw [hred1]; exact isUnit_one)
  have hup : hu.unit ∈ princ O n := by
    rw [princ, MonoidHom.mem_ker]
    ext1
    simpa using hred1
  refine ⟨k * hu.unit, J.mul_mem hk (hJ hup), ?_⟩
  simp [← Matrix.mul_assoc]

theorem blocks_mul {a t : Type} [Fintype a] [Fintype t] (g h : Matrix (a ⊕ t) (a ⊕ t) O) :
    (g * h).toBlocks₁₁ = g.toBlocks₁₁ * h.toBlocks₁₁ + g.toBlocks₁₂ * h.toBlocks₂₁ ∧
    (g * h).toBlocks₂₁ = g.toBlocks₂₁ * h.toBlocks₁₁ + g.toBlocks₂₂ * h.toBlocks₂₁ ∧
    (g * h).toBlocks₂₂ = g.toBlocks₂₁ * h.toBlocks₁₂ + g.toBlocks₂₂ * h.toBlocks₂₂ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;>
    simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

def level {a : ℕ} (t : ℕ) (J' : Subgroup (GL (Fin a) O)) (hJ : princ O (Fin a) ≤ J') :
    Subgroup (GL (Fin a ⊕ Fin t) O) where
  carrier := {g | (∃ k ∈ J', (k : Matrix (Fin a) (Fin a) O) = g.val.toBlocks₁₁) ∧
    (∀ i j, g.val.toBlocks₂₁ i j ∈ IsLocalRing.maximalIdeal O) ∧
    ∃ d : GL (Fin t) O, (d : Matrix (Fin t) (Fin t) O) = g.val.toBlocks₂₂}
  one_mem' := by
    refine ⟨⟨1, J'.one_mem, ?_⟩, ?_, ⟨1, ?_⟩⟩
    · ext i j; simp [toBlocks₁₁, Matrix.one_apply]
    · intro i j; simp [toBlocks₂₁]
    · ext i j; simp [toBlocks₂₂, Matrix.one_apply]
  mul_mem' := by
    rintro g h ⟨⟨k, hk, e1⟩, c1, d, f1⟩ ⟨⟨k', hk', e2⟩, c2, d', f2⟩
    obtain ⟨b1, b2, b3⟩ := blocks_mul g.val h.val
    rw [← red_eq_zero] at c1 c2
    refine ⟨exists_mem_of_red hJ (J'.mul_mem hk hk') ?_, ?_, ?_⟩
    · rw [Units.val_mul, b1, red_add, red_mul _ (toBlocks₂₁ _), c2, ← e1, ← e2]; simp
    · rw [← red_eq_zero, Units.val_mul, b2, red_add, red_mul, red_mul, c1, c2]; simp
    · apply isUnit_of_red
      rw [Units.val_mul, b3, red_add, red_mul (toBlocks₂₁ _), c1, ← f1, ← f2, Matrix.zero_mul,
        zero_add, ← Units.val_mul]
      exact (d * d').isUnit.map (IsLocalRing.residue O).mapMatrix
  inv_mem' := by
    rintro g ⟨⟨k, hk, e1⟩, c1, d, f1⟩
    obtain ⟨b1, b2, b3⟩ := blocks_mul g.val (g⁻¹).val
    rw [Units.mul_inv] at b1 b2 b3
    rw [← red_eq_zero] at c1
    have o1 : (1 : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) O).toBlocks₁₁ = 1 := by
      ext i j; simp [toBlocks₁₁, Matrix.one_apply]
    have o2 : (1 : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) O).toBlocks₂₁ = 0 := by
      ext i j; simp [toBlocks₂₁]
    have o3 : (1 : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) O).toBlocks₂₂ = 1 := by
      ext i j; simp [toBlocks₂₂, Matrix.one_apply]
    rw [o1, ← e1] at b1
    rw [o2, ← f1] at b2
    rw [o3, ← f1] at b3
    have r1 : ∀ n : ℕ, red (1 : Matrix (Fin n) (Fin n) O) = 1 := fun n => by simp [red]
    have c2 : red (g⁻¹).val.toBlocks₂₁ = 0 := by
      have := congrArg (fun X => red (d⁻¹).val * red X) b2
      simp only [red_add, red_mul (toBlocks₂₁ _), c1, Matrix.zero_mul, zero_add] at this
      rw [← red_mul, ← red_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
      rw [← this]; simp [red]
    refine ⟨exists_mem_of_red hJ (J'.inv_mem hk) ?_, (red_eq_zero _).1 c2, ?_⟩
    · have := congrArg (fun X => red (k⁻¹).val * red X) b1
      simp only [red_add, red_mul _ (toBlocks₂₁ _), c2, Matrix.mul_zero, add_zero] at this
      rw [← red_mul, ← red_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
        Matrix.mul_one] at this
      exact this.symm
    · apply isUnit_of_red
      have := congrArg red b3
      rw [red_add, red_mul (toBlocks₂₁ _), c1, Matrix.zero_mul, zero_add, red_mul, r1] at this
      exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse this.symm)

def parahoric (O : Type) [CommRing O] [IsLocalRing O] (r s : ℕ) : Subgroup (GL (Fin r ⊕ Fin s) O) :=
  level s (⊤ : Subgroup (GL (Fin r) O)) le_top

end Levels

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def resCard (F : Type) [Field F] [ValuativeRel F] : ℝ := (Nat.card 𝓀[F] : ℝ)

def unitIn (u : 𝒪[F]ˣ) : Fˣ := Units.map (𝒪[F].subtype : 𝒪[F] →* F) u

def entries {m n : Type} (A : Matrix m n 𝒪[F]) : m → n → F := fun i j => (A i j : F)

def idealSet (F : Type) [Field F] [ValuativeRel F] (m n : Type) : Set (m → n → F) :=
  {x | ∀ i j, ∃ y ∈ 𝓂[F], (y : F) = x i j}

def groupSet {n : Type} [Fintype n] [DecidableEq n] (H : Subgroup (GL n 𝒪[F])) : Set (n → n → F) :=
  {x | ∃ k ∈ H, entries k.val = x}

def IsUnitary (χ : Fˣ →* ℂˣ) : Prop := ∀ x, ‖(χ x : ℂ)‖ = 1

def IsTame (χ : Fˣ →* ℂˣ) : Prop := ∀ u : 𝒪[F]ˣ, (u : 𝒪[F]) - 1 ∈ 𝓂[F] → χ (unitIn u) = 1

def IsUnram (χ : Fˣ →* ℂˣ) : Prop := ∀ u : 𝒪[F]ˣ, χ (unitIn u) = 1

def IsUnif (ϖ : Fˣ) : Prop := ∃ p : 𝒪[F], 𝓂[F] = Ideal.span {p} ∧ (p : F) = (ϖ : F)

def datum {a : ℕ} (t : ℕ) (J' : Subgroup (GL (Fin a) 𝒪[F])) (lam : J' →* ℂˣ) (μ : Fˣ →* ℂˣ)
    (x : Fin a ⊕ Fin t → Fin a → F) : ℂ :=
  if h : (∃ k : J', entries k.val.val = fun i j => x (Sum.inl i) j) ∧
      (fun i j => x (Sum.inr i) j) ∈ idealSet F (Fin t) (Fin a) then
    ((lam h.1.choose * (μ (unitIn (Matrix.GeneralLinearGroup.det h.1.choose.val)))⁻¹ : ℂˣ) : ℂ)
  else 0

def eulerFactor (ϖ : Fˣ) (χ : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if IsUnram χ then (1 - (χ ϖ : ℂ) * (resCard F : ℂ) ^ (-s))⁻¹ else 1

def splitL (ϖ : Fˣ) (χ : Fˣ →* ℂˣ) (s : ℂ) : ℂ := eulerFactor ϖ χ s * eulerFactor ϖ χ⁻¹ s

def blockL (ϖ : Fˣ) (t : ℕ) (χ : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∏ l ∈ range t, splitL ϖ χ (s + ((t : ℂ) - 1) / 2 - (l : ℂ))

def zetaFrom (q : ℝ) (c n : ℕ) : ℝ := (qE q (c + 1) n)⁻¹

def chainScalar (ϖ : Fˣ) (r t j : ℕ) (μ : ℕ → Fˣ →* ℂˣ) : ℂ :=
  ((resCard F ^ (-((j * t * r : ℕ) : ℤ)) * qE (resCard F) 1 r : ℝ) : ℂ) *
    (∏ i ∈ Ico 1 j, blockL ϖ t (μ i / μ j) ((1 + (t : ℂ)) / 2)) /
      ((zetaFrom (resCard F) t (j * t) : ℝ) : ℂ)

variable [MeasurableSpace F]

def volAdd (ν : Measure F) (m n : Type) [Fintype m] [Fintype n] : Measure (m → n → F) :=
  Measure.pi fun _ : m => Measure.pi fun _ : n => ν

def volGroup (ν : Measure F) {n : Type} [Fintype n] [DecidableEq n] (H : Subgroup (GL n 𝒪[F])) : ℝ :=
  (volAdd ν n n).real (groupSet H)

def volIdeal (ν : Measure F) (m n : Type) [Fintype m] [Fintype n] : ℝ :=
  (volAdd ν m n).real (idealSet F m n)

def normSq (ν : Measure F) {m n : Type} [Fintype m] [Fintype n] (Φ : (m → n → F) → ℂ) : ℝ :=
  ∫ x, ‖Φ x‖ ^ 2 ∂(volAdd ν m n)

def VolumeOfGL (ν : Measure F) : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n],
    volGroup ν (⊤ : Subgroup (GL n 𝒪[F])) = qE (resCard F) 1 (Fintype.card n)

def LevelIdentity (ν : Measure F) : Prop :=
  ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) 𝒪[F])) (hJ : princ 𝒪[F] (Fin a) ≤ J')
    (lam : J' →* ℂˣ) (μ : Fˣ →* ℂˣ),
    (∀ k : J', k.val ∈ princ 𝒪[F] (Fin a) → lam k = 1) → (∀ k, IsOfFinOrder (lam k)) →
    IsUnitary μ → IsTame μ →
    let q := resCard F
    let J := level t J' hJ
    let z := normSq ν (datum t J' lam μ)
    Integrable (fun x => ‖datum t J' lam μ x‖ ^ 2) (volAdd ν (Fin a ⊕ Fin t) (Fin a)) ∧
    z = volGroup ν J' * volIdeal ν (Fin t) (Fin a) ∧
    J.index ≠ 0 ∧ 0 < volGroup ν J ∧
    (J.index : ℝ) * zetaProd q (a + t) = 1 / volGroup ν J ∧
    volGroup ν J =
      volGroup ν J' * volIdeal ν (Fin t) (Fin a) * volGroup ν (⊤ : Subgroup (GL (Fin t) 𝒪[F])) ∧
    (J.index : ℝ) * zetaProd q (a + t) * z = zetaProd q t ∧
    (J.index : ℝ) * zetaFrom q t (a + t) * z = 1

def ParahoricIndex (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Prop :=
  ∀ r s : ℕ, (parahoric 𝒪[F] r s).index ≠ 0 ∧
    ((parahoric 𝒪[F] r s).index : ℝ) = idxPar (resCard F) r s

def ParahoricIdentity (ν : Measure F) : Prop :=
  ∀ (ϖ : Fˣ) (r t j : ℕ) (ξ : Fˣ →* ℂˣ) (μ : ℕ → Fˣ →* ℂˣ),
    IsUnif ϖ → 1 ≤ j → IsUnitary ξ → IsTame ξ → ¬ IsUnram ξ →
    (∀ i ∈ Icc 1 j, IsUnitary (μ i)) →
    ((∀ i ∈ Icc 1 j, ∀ u : 𝒪[F]ˣ, μ i (unitIn u) = ξ (unitIn u)) ∨
      (∀ i ∈ Icc 1 j, ∀ u : 𝒪[F]ˣ, μ i (unitIn u) = (ξ (unitIn u))⁻¹)) →
    let q := resCard F
    let N : ℝ := ((parahoric 𝒪[F] r (j * t)).index : ℝ)
    let d := zetaFrom q t (r + j * t)
    let Φ := datum t (⊤ : Subgroup (GL (Fin r) 𝒪[F])) 1 ξ
    (∀ i ∈ Ico 1 j, ∀ s : ℕ, 1 ≤ s →
      ‖((μ i / μ j) ϖ : ℂ)‖ = 1 ∧
      1 - ((μ i / μ j) ϖ : ℂ) * (q : ℂ) ^ (-(s : ℤ)) ≠ 0 ∧
      splitL ϖ (μ i / μ j) (s : ℂ) =
        (((‖1 - ((μ i / μ j) ϖ : ℂ) * (q : ℂ) ^ (-(s : ℤ))‖ ^ 2)⁻¹ : ℝ) : ℂ)) ∧
    ((N * d : ℝ) : ℂ) * chainScalar ϖ r t j μ =
      ∏ i ∈ Ico 1 j, blockL ϖ t (μ i / μ j) ((1 + (t : ℂ)) / 2) ∧
    ∏ i ∈ Ico 1 j, blockL ϖ t (μ i / μ j) ((1 + (t : ℂ)) / 2) =
      ∏ i ∈ Ico 1 j, ∏ s ∈ Icc 1 t, splitL ϖ (μ i / μ j) (s : ℂ) ∧
    ∏ i ∈ Ico 1 j, ∏ s ∈ Icc 1 t, splitL ϖ (μ i / μ j) (s : ℂ) =
      ∏ i ∈ Ico 1 j, Lpair q t ((μ i / μ j) ϖ : ℂ) ∧
    (j = 1 →
      normSq ν Φ = volGroup ν (⊤ : Subgroup (GL (Fin r) 𝒪[F])) * q ^ (-((r * t : ℕ) : ℤ)) ∧
      chainScalar ϖ r t j μ = ((normSq ν Φ : ℝ) : ℂ) ∧
      N * d * normSq ν Φ = 1)

end Local

def RationalIdentity : Prop :=
  ∀ (q : ℝ) (r t j : ℕ), 1 < q → 1 ≤ j →
    idxPar q r (j * t) * zetaFrom q t (r + j * t) *
      (q ^ (-((j * t * r : ℕ) : ℤ)) * qE q 1 r / zetaFrom q t (j * t)) = 1

def IndexIdentities : Prop :=
  RationalIdentity ∧
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure],
    ν (𝒪[F] : Set F) = 1 →
      VolumeOfGL ν ∧ LevelIdentity ν ∧ ParahoricIndex F ∧ ParahoricIdentity ν

example (q : ℝ) (r s : ℕ) :
    idxPar q r s = q ^ (r * s) * qE q 1 (r + s) / (qE q 1 r * qE q 1 s) := rfl

example : idxPar 3 1 (1 * 1) * zetaFrom 3 1 (1 + 1 * 1) *
    ((3 : ℝ) ^ (-((1 * 1 * 1 : ℕ) : ℤ)) * qE 3 1 1 / zetaFrom 3 1 (1 * 1)) = 1 := by
  have h : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  simp only [idxPar, Formalism.BasicNotions.TH.parIdx, zetaFrom, qE]
  norm_num [h]

example {O : Type} [CommRing O] [IsLocalRing O] (r s : ℕ) (g : GL (Fin r ⊕ Fin s) O) :
    g ∈ parahoric O r s ↔ IsUnit g.val.toBlocks₁₁ ∧
      (∀ i j, g.val.toBlocks₂₁ i j ∈ IsLocalRing.maximalIdeal O) ∧ IsUnit g.val.toBlocks₂₂ :=
  ⟨fun ⟨⟨k, _, e⟩, c, d⟩ => ⟨⟨k, e⟩, c, d⟩, fun ⟨⟨k, e⟩, c, d⟩ => ⟨⟨k, trivial, e⟩, c, d⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex
