import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws

namespace UpperTheory.V.Sd.S3

abbrev M2 (R : Type) : Type := Matrix (Fin 2) (Fin 2) R

section Alg

variable {R R' : Type} [CommRing R] [CommRing R']

def low (x : R) : M2 R := !![1, 0; x, 1]

def s3 (u : R) (g : M2 R) : M4 R := Matrix.diagonal ![1, 1, -1, 3] * symCubeMatrixHom R g * Matrix.diagonal ![1, 1, -1, u]

theorem symmetric_cube_explicit (u : R) (g : M2 R) : s3 u g =
    !![g 0 0 ^ 3, g 0 0 ^ 2 * g 0 1, -(g 0 0 * g 0 1 ^ 2), u * g 0 1 ^ 3;
    3 * g 0 0 ^ 2 * g 1 0, g 0 0 ^ 2 * g 1 1 + 2 * g 0 0 * g 0 1 * g 1 0, -(2 * g 0 0 * g 0 1 * g 1 1 + g 0 1 ^ 2 * g 1 0),
      3 * u * g 0 1 ^ 2 * g 1 1;
    -(3 * g 0 0 * g 1 0 ^ 2), -(2 * g 0 0 * g 1 0 * g 1 1 + g 0 1 * g 1 0 ^ 2), g 0 0 * g 1 1 ^ 2 + 2 * g 0 1 * g 1 0 * g 1 1,
      -(3 * u * g 0 1 * g 1 1 ^ 2);
    3 * g 1 0 ^ 3, 3 * g 1 0 ^ 2 * g 1 1, -(3 * g 1 0 * g 1 1 ^ 2), 3 * u * g 1 1 ^ 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s3, symCubeMatrixHom, Matrix.diagonal_mul, Matrix.mul_diagonal] <;> ring

theorem symmetric_cube_map (f : R →+* R') (u : R) (g : M2 R) : (s3 u g).map f = s3 (f u) (g.map f) := by
  ext i j
  rw [symmetric_cube_explicit, symmetric_cube_explicit]
  fin_cases i <;> fin_cases j <;> simp [map_ofNat]

theorem low_map (f : R →+* R') (x : R) : (low x).map f = low (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [low]

variable {u : R} (hu : 3 * u = 1)
include hu

theorem symmetric_cube_one : s3 u 1 = 1 := by
  ext i j
  rw [symmetric_cube_explicit]
  fin_cases i <;> fin_cases j <;> simp [hu]

theorem symmetric_cube_mul (g h : M2 R) : s3 u (g * h) = s3 u g * s3 u h := by
  have e : (Matrix.diagonal ![1, 1, -1, u] * Matrix.diagonal ![1, 1, -1, 3] : M4 R) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm u 3, hu]
  simp only [s3, map_mul, mul_assoc]
  rw [← mul_assoc (Matrix.diagonal ![1, 1, -1, u]), e, one_mul]

theorem adjoint_symmetric_cube (g : M2 R) : adj (s3 u g) = s3 u g.adjugate := by
  ext i j
  rw [adj_apply, symmetric_cube_explicit, symmetric_cube_explicit, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [sgn, Fin.rev, hu] <;> ring

theorem symmetric_cube_smul (a : R) (g : M2 R) : s3 u (a • g) = a ^ 3 • s3 u g := by
  ext i j
  rw [symmetric_cube_explicit, symmetric_cube_explicit]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem symmetric_cube_symplectic_similitude (a : R) (g : M2 R) : IsGSp (a ^ 2 * g.det ^ 3) (a • s3 u g) := by
  have e : adj (a • s3 u g) = a • adj (s3 u g) := by
    ext i j
    simp only [adj_apply, Matrix.smul_apply]
    rw [smul_comm]
  rw [IsGSp, e, adjoint_symmetric_cube hu, Matrix.smul_mul, Matrix.mul_smul, ← symmetric_cube_mul hu, Matrix.adjugate_mul, symmetric_cube_smul hu, symmetric_cube_one hu,
    smul_smul, smul_smul, ← sq]

theorem adjoint_symmetric_cube_lower (x : R) : adj (s3 u (low x)) = s3 u (low (-x)) := by
  rw [adjoint_symmetric_cube hu]
  congr 1
  simp [low, Matrix.adjugate_fin_two]

theorem symmetric_cube_lower_unipotent (x : R) : IsLow (s3 u (low x)) := by
  refine ⟨?_, fun i => ?_, fun i j h => ?_⟩
  · simpa [low] using symmetric_cube_symplectic_similitude hu 1 (low x)
  · rw [symmetric_cube_explicit]
    fin_cases i <;> simp [low, hu]
  · rw [symmetric_cube_explicit]
    fin_cases i <;> fin_cases j <;> simp [low] at h ⊢

theorem conjugate_symmetric_cube_flags (a x y : R) (g : M2 R) : adj (s3 u (low y)) * (a • s3 u g) * s3 u (low x) =
    a • s3 u !![g 0 0 + g 0 1 * x, g 0 1; g 1 0 + g 1 1 * x - (g 0 0 + g 0 1 * x) * y, g 1 1 - y * g 0 1] := by
  rw [adjoint_symmetric_cube_lower hu, Matrix.mul_smul, Matrix.smul_mul, ← symmetric_cube_mul hu, ← symmetric_cube_mul hu]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [low, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] <;> ring

omit hu in
theorem symmetric_cube_upper_triangular (a : R) {g : M2 R} (h : g 1 0 = 0) : IsUp (a • s3 u g) := by
  intro i j hij
  rw [symmetric_cube_explicit]
  fin_cases i <;> fin_cases j <;> simp [h] at hij ⊢

omit hu in
theorem symmetric_cube_lower_entries_zero (a : R) {g : M2 R} (h : g 0 1 = 0) {i j : Fin 4} (hij : i < j) : (a • s3 u g) i j = 0 := by
  rw [symmetric_cube_explicit]
  fin_cases i <;> fin_cases j <;> simp [h] at hij ⊢

theorem symmetric_cube_diagonal_entries (a : R) {g : M2 R} (h : g 0 1 * g 1 0 = 0) (i : Fin 4) :
    (a • s3 u g) i i = a * (g 0 0 ^ (3 - (i : ℕ)) * g 1 1 ^ (i : ℕ)) := by
  rw [symmetric_cube_explicit]
  fin_cases i <;> simp [hu]
  · linear_combination (2 * a * g 0 0) * h
  · linear_combination (2 * a * g 1 1) * h

def rep {Γ : Type} [Group Γ] (δ : Γ →* Rˣ) (ρ : Γ →* M2 R) : Γ →* M4 R where
  toFun g := (δ g : R) • s3 u (ρ g)
  map_one' := by simp [symmetric_cube_one hu]
  map_mul' g h := by simp [symmetric_cube_mul hu, smul_smul, mul_comm]

theorem rep_apply {Γ : Type} [Group Γ] (δ : Γ →* Rˣ) (ρ : Γ →* M2 R) (g : Γ) : rep hu δ ρ g = (δ g : R) • s3 u (ρ g) := rfl

end Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

def toB {Γ : Type} [Group Γ] (χ : Γ →* c.Oˣ) : Γ →* (Qbar l)ˣ :=
  (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp χ

def toC {Γ : Type} [Group Γ] {c₁ : Coef l} (h : c.O ≤ c₁.O) (χ : Γ →* c.Oˣ) : Γ →* c₁.Oˣ :=
  (Units.map (inc h).toMonoidHom).comp χ

structure Tw {D : Raw Ω c} (T₀ : Tower D) (k : ℕ) (δ : G ℚ Ω →* c.Oˣ) : Prop where
  cont : AdicCont (maximalIdeal c.O) fun g => (δ g : c.O)
  mul : ∀ g ∈ T₀.F.fixingSubgroup, δ g ^ 2 * (chiO ℚ Ω l c.O g ^ (k - 1) * D.ξ g) ^ 3 = D.th g
  red : ∀ g ∈ T₀.F.fixingSubgroup, ∀ i : Fin 4, Raw.bar (chi D T₀.pr i) g = Raw.bar δ g * Raw.bar D.ξ g ^ (3 - (i : ℕ))
  kill : ∀ g, cycZ ℚ Ω l g = 1 → D.rbar g = 1 → δ g = 1 ∧ D.ξ g = 1
  wt : ∃ (U : Subgroup (G ℚ Ω)) (j : ℤ), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ g ∈ U, δ g ^ 2 = chiO ℚ Ω l c.O g ^ j

structure ModB (ξ θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ) (g0 : G ℚ Ω) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (x : ValuationSubring Ω → Qbar l) : Prop where
  cont : Continuous ρ
  red : ∀ g, ‖ρ g 0 0 - ξ g‖ < 1 ∧ ‖ρ g 1 1 - 1‖ < 1 ∧ ‖ρ g 0 1‖ < 1 ∧ ‖ρ g 1 0‖ ≤ 1
  ne : ∃ g, ‖ρ g 1 0‖ = 1
  nrm : ρ g0 0 1 = 0 ∧ ρ g0 1 0 = 0
  det : Matrix.GeneralLinearGroup.det.comp ρ = cycBar ℚ Ω l ^ (k - 1) * (ξ * θ)
  away : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, ξ g = 1 → θ g = 1 → ρ g = 1
  int : ∀ A, ‖x A‖ ≤ 1
  mem : ∀ E : IntermediateField ℚ_[l] (Qbar l), (∀ g i j, ρ g i j ∈ E) → ∀ A, x A ∈ E
  flag : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Dec (F := ℚ) A,
    ρ s 1 0 + ρ s 1 1 * x A = (ρ s 0 0 + ρ s 0 1 * x A) * x A
  ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) A,
    ρ s 0 0 + ρ s 0 1 * x A = (cycBar ℚ Ω l s ^ (k - 1) : (Qbar l)ˣ) ∧ ρ s 1 1 - x A * ρ s 0 1 = 1

structure Mod (D : Raw Ω c) (θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ) (g0 : G ℚ Ω) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) {c₁ : Coef l}
    (h : c.O ≤ c₁.O) (ρ₁ : G ℚ Ω →* M2 c₁.O) (x : ValuationSubring Ω → c₁.O) : Prop where
  iso : RepIso ρ (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁).toHomUnits
  cont : ∀ i j, AdicCont (maximalIdeal c₁.O) fun g => ρ₁ g i j
  red : ∀ g, ρ₁ g 0 0 - inc h (D.ξ g) ∈ maximalIdeal c₁.O ∧ ρ₁ g 1 1 - 1 ∈ maximalIdeal c₁.O ∧ ρ₁ g 0 1 ∈ maximalIdeal c₁.O
  ne : ∃ g, ρ₁ g 1 0 ∉ maximalIdeal c₁.O
  nrm : ρ₁ g0 0 1 = 0 ∧ ρ₁ g0 1 0 = 0
  det : ∀ g, θ g = 1 → (ρ₁ g).det = inc h ((chiO ℚ Ω l c.O g ^ (k - 1) * D.ξ g : c.Oˣ) : c.O)
  away : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, D.ξ g = 1 → θ g = 1 → ρ₁ g = 1
  flag : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Dec (F := ℚ) A,
    ρ₁ s 1 0 + ρ₁ s 1 1 * x A = (ρ₁ s 0 0 + ρ₁ s 0 1 * x A) * x A
  ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) A,
    ρ₁ s 0 0 + ρ₁ s 0 1 * x A = (chiO ℚ Ω l c₁.O s ^ (k - 1) : c₁.Oˣ) ∧ ρ₁ s 1 1 - x A * ρ₁ s 0 1 = 1

def pd {D : Raw Ω c} (T : Tower D) {c₁ : Coef l} (h : c.O ≤ c₁.O) {u : c₁.O} (hu : 3 * u = 1) (δ : G ℚ Ω →* c.Oˣ)
    (ρ₁ : G ℚ Ω →* M2 c₁.O) (x : ValuationSubring Ω → c₁.O) : PD T.ι (G T.F Ω) c₁.O :=
  ⟨(rep hu (toC h δ) ρ₁).comp (resQ T.F), fun v => s3 u (low (x (T.pl v)))⟩

structure Dat (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] where
  c : Coef l
  D : Raw Ω c
  T₀ : Tower D
  good : D.Good
  k : ℕ
  three : 3 ≤ k
  cong : k ≡ 1 [MOD l - 1]
  δ : G ℚ Ω →* c.Oˣ
  tw : Tw T₀ k δ
  θ : G ℚ Ω →* (Qbar l)ˣ
  ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)
  c₁ : Coef l
  h : c.O ≤ c₁.O
  ρ₁ : G ℚ Ω →* M2 c₁.O
  x : ValuationSubring Ω → c₁.O
  mod : Mod D θ k (resQ T₀.F T₀.g0) ρ h ρ₁ x
  u : c₁.O
  hu : 3 * u = 1

abbrev Dat.Q (d : Dat Ω l) (T : Tower d.D) : PD T.ι (G T.F Ω) d.c₁.O := pd T d.h d.hu d.δ d.ρ₁ d.x

def KillsN : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c), Ctx3 D →
    ∃ N : ℕ, 0 < N ∧ ¬ l ∣ N ∧ KillsMu N D.ξ

def SplitPrime : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    commutator (G ℚ Ω) ≤ U → ∀ M : ℕ, 0 < M → ∃ w : ℕ, w.Prime ∧ M < w ∧ w ≡ 1 [MOD M] ∧
      ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ U

def ThetaEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → w ≡ 1 [MOD l] →
    ∃ θ : G ℚ Ω →* (Qbar l)ˣ, θ ≠ 1 ∧ θ ^ l = 1 ∧ KillsMu w θ

def ThetaUnr : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → ∀ θ : G ℚ Ω →* (Qbar l)ˣ,
    θ ^ l = 1 → KillsMu w θ → (∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) ∧
      ∀ F : IntermediateField ℚ Ω, Dies l w F → F.fixingSubgroup ≤ θ.ker

def AuxiliaryPrimeFunction : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D), Ctx3 D →
    ∃ (N w : ℕ) (θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ ∧ SplitAt N w (toB D.ξ) ∧ T₀.Splits w

def MuIne : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ muOf l (Dec (F := F) A), s ∈ Ine (F := F) A ∧ cycZ F Ω l s = 1

def Teich : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : c.Oˣ) (m : ℕ), l.Coprime m → x ^ m = 1 → residue c.O x = 1 → x = 1

def SqrtChar : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) →
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] (μ : Γ →* Oˣ), (∀ g, residue O (μ g) = 1) →
    AdicCont (maximalIdeal O) (fun g => (μ g : O)) → ∃ η : Γ →* Oˣ, (∀ g, η g ^ 2 = μ g) ∧ (∀ g, residue O (η g) = 1) ∧
      AdicCont (maximalIdeal O) (fun g => (η g : O)) ∧ ∀ g, μ g = 1 → η g = 1

def TwEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D), D.Good →
    T₀.Three → ∀ k : ℕ, 1 ≤ k → k ≡ 1 [MOD l - 1] → ∃ δ, Tw T₀ k δ

def LocNe : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c), D.Good →
    ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ s ∈ Dec (F := ℚ) A, Raw.bar D.ξ s ≠ 1

def LineEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (H : Subgroup Γ) (ρ : Γ →* GL (Fin 2) (Qbar l)) (ξ : Γ →* (Qbar l)ˣ)
    (κ : Fin 2 → ↥H →* (Qbar l)ˣ), (∀ g, ‖ρ g 1 1 - 1‖ < 1 ∧ ‖ρ g 1 0‖ ≤ 1) → IsFlagOn ρ H κ → (∀ s : H, Cong (κ 0 s) (ξ s)) →
    (∃ s ∈ H, ¬ Cong (ξ s) 1) → ∃ x : Qbar l, ‖x‖ ≤ 1 ∧ ∀ s : H, ρ s 0 0 + ρ s 0 1 * x = κ 0 s ∧
      ρ s 1 0 + ρ s 1 1 * x = κ 0 s * x ∧ ρ s 1 1 - x * ρ s 0 1 = κ 1 s

def RootMem : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (Qbar l)) (a b c d x : Qbar l), a ∈ E → b ∈ E → c ∈ E → d ∈ E →
    ‖b‖ < 1 → ‖a - d‖ = 1 → ‖x‖ ≤ 1 → c + d * x = (a + b * x) * x → x ∈ E

def ModBEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ξ θ : G ℚ Ω →* (Qbar l)ˣ)
    (k : ℕ), 1 ≤ k → k ≡ 1 [MOD l - 1] → ∀ ρ, EisRep ι ξ θ k ρ → (∀ g, ‖(ξ g : Qbar l)‖ = 1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ s ∈ Dec (F := ℚ) A, ¬ Cong (ξ s) 1) →
    ∀ g0, ¬ Cong (ξ g0) 1 → ∃ ρ' x, RepIso ρ ρ' ∧ ModB ξ θ k g0 ρ' x

def CoefEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], (∀ (c : Coef l) (E : IntermediateField ℚ_[l] (Qbar l)), FiniteDimensional ℚ_[l] E →
      ∃ c₁ : Coef l, c.O ≤ c₁.O ∧ ∀ y ∈ E, ‖y‖ ≤ 1 → y ∈ c₁.O) ∧
    ∀ (c : Coef l) (Γ : Type) [TopologicalSpace Γ] (f : Γ → c.O),
      AdicCont (maximalIdeal c.O) f ↔ Continuous fun g => (f g : PadicAlgCl l)

def ModEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c)
    (θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ) (g0 : G ℚ Ω) (ρ ρ' : G ℚ Ω →* GL (Fin 2) (Qbar l)) (x : ValuationSubring Ω → Qbar l),
    RepIso ρ ρ' → ModB (toB D.ξ) θ k g0 ρ' x → ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (ρ₁ : G ℚ Ω →* M2 c₁.O)
      (x₁ : ValuationSubring Ω → c₁.O), Mod D θ k g0 ρ h ρ₁ x₁

def PairOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok →
    ∀ (W : Finset ℕ) (R : Type) [CommRing R] (f : d.c₁.O →+* R),
    (∀ g ∈ T.F.fixingSubgroup, f (d.ρ₁ g).det = f (inc d.h ((chiO ℚ Ω l d.c.O g ^ (d.k - 1) * d.D.ξ g : d.c.Oˣ) : d.c.O))) →
    (∀ A, Raw.Away (insert l W) A → ∀ g ∈ Ine (F := T.F) A, d.θ (resQ T.F g) = 1) →
    (T.fr W).IsPair (f.comp (inc d.h)) ((d.Q T).map f)

def ResOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D), d.T₀.Le T →
    ∀ (W : Finset ℕ) (R : Type) [CommRing R] (f : d.c₁.O →+* R), (∀ y ∈ maximalIdeal d.c₁.O, f y = 0) →
    (T.fr W).Res (f.comp (inc d.h)) ((d.Q T).map f) ∧ Supp nM ((d.Q T).map f).r ∧
      ∀ g, f (d.ρ₁ g).det = f (inc d.h ((chiO ℚ Ω l d.c.O g ^ (d.k - 1) * d.D.ξ g : d.c.Oˣ) : d.c.O))

def ContOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D),
    (d.Q T).Cont (maximalIdeal d.c₁.O) ∧ ∀ (R : Type) [CommRing R] (f : d.c₁.O →+* R), (∀ y ∈ maximalIdeal d.c₁.O, f y = 0) →
      ((d.Q T).map f).Cont ⊥

def EntOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l),
    Raw.bar d.D.ξ (resQ d.T₀.F d.T₀.g0) ≠ 1 → ∀ (R : Type) [Field R] (f : d.c₁.O →+* R), (∀ y ∈ maximalIdeal d.c₁.O, f y = 0) →
    Ent ((d.Q d.T₀).map f).r (-wAl) ∧ Ent ((d.Q d.T₀).map f).r (-wBe)

def OverOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D) (hT : d.T₀.Le T)
    (R : Type) [Field R] (f : d.c₁.O →+* R), (∀ y ∈ maximalIdeal d.c₁.O, f y = 0) →
    d.T₀.OverT hT ((d.Q d.T₀).map f) ((d.Q T).map f)

def WtsOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D),
    ∃ h : Fin 4 → ℤ, (∀ i : Fin 3, ∃ k : ℤ, 2 ≤ k ∧ h i.castSucc = h i.succ + 2 * k) ∧
      T.Wts h ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l)))

def IsoOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l),
    RepIso (tw (sym3 d.ρ) (toB d.δ))
      (mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep d.hu (toC d.h d.δ) d.ρ₁)).toHomUnits

def IrrOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D),
    Continuous d.ρ → IrrOpen (sym3 d.ρ) → Irr (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp T.G'.subtype)

def AutL : Prop :=
  Hypotheses₂ → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 4) (Qbar l)), Continuous r → IrrOpen r → IsAutR ι r → IsAutC ι (r.comp (resQ T.L))

def AutOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D) (ι : Qbar l ≃+* ℂ),
    IsAutC ι ((sym3 d.ρ).comp (resQ T.L)) →
    ∃ (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4), Continuous κ ∧ (CG.mk π).IsRegAlg ∧
      Af.AttC ι (Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp (resLe T.F_le)).toHomUnits κ) π

end UpperTheory.V.Sd.S3

end
