import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ShiftTw
open Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

def matPiEquiv (S : Type) [CommRing S] (n k : ℕ) :
    Matrix (Fin n) (Fin n) (Fin k → S) ≃+* (Fin k → Matrix (Fin n) (Fin n) S) where
  toFun M i := (Pi.evalRingHom (fun _ : Fin k => S) i).mapMatrix M
  invFun N := Matrix.of fun a b i => N i a b
  left_inv M := by ext a b i; rfl
  right_inv N := by funext i; ext a b; rfl
  map_mul' M N := by funext i; exact map_mul ((Pi.evalRingHom (fun _ : Fin k => S) i).mapMatrix) M N
  map_add' M N := by funext i; exact map_add ((Pi.evalRingHom (fun _ : Fin k => S) i).mapMatrix) M N

theorem mem_range_map_subtype_iff {T : Type} [CommRing T] (n : ℕ) (A : Subring T) (g : GL (Fin n) T) :
    g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range ↔
      (∀ a b, (g : Matrix (Fin n) (Fin n) T) a b ∈ A) ∧
        (∀ a b, ((g⁻¹ : GL (Fin n) T) : Matrix (Fin n) (Fin n) T) a b ∈ A) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · change ((x : Matrix (Fin n) (Fin n) A) a b : T) ∈ A
      exact SetLike.coe_mem _
    · rw [← map_inv]
      change (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) a b : T) ∈ A
      exact SetLike.coe_mem _
  · rintro ⟨h1, h2⟩
    let P : Matrix (Fin n) (Fin n) A := Matrix.of fun a b => ⟨_, h1 a b⟩
    let Q : Matrix (Fin n) (Fin n) A := Matrix.of fun a b => ⟨_, h2 a b⟩
    have hP : P.map A.subtype = (g : Matrix (Fin n) (Fin n) T) := by ext a b; rfl
    have hQ : Q.map A.subtype = ((g⁻¹ : GL (Fin n) T) : Matrix (Fin n) (Fin n) T) := by ext a b; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) A => M.map A.subtype) := by
      intro M N h
      funext a b
      exact Subtype.ext (congrFun (congrFun h a) b)
    have hPQ : P * Q = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hP, hQ, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv)
    have hQP : Q * P = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hP, hQ, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul)
    refine ⟨⟨P, Q, hPQ, hQP⟩, ?_⟩
    ext a b
    rfl

def glPiEquiv {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S)) :
    GL (Fin n) R ≃* (Fin (d + 1) → GL (Fin n) S) :=
  (Units.mapEquiv (e.mapMatrix.trans (matPiEquiv S n (d + 1))).toMulEquiv).trans MulEquiv.piUnits

theorem glPiEquiv_val {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (g : GL (Fin n) R) (i : Fin (d + 1)) (a b : Fin n) :
    ((glPiEquiv d n e g i : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) a b = e ((g : Matrix (Fin n) (Fin n) R) a b) i :=
  rfl

theorem glPiEquiv_inv_val {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (g : GL (Fin n) R) (i : Fin (d + 1)) (a b : Fin n) :
    (((glPiEquiv d n e g i)⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) a b =
      e (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b) i :=
  rfl

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem glPiEquiv_mem_iff {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (A : Subring R) (B : Subring S) (hAB : ∀ x : R, x ∈ A ↔ ∀ i, e x i ∈ B) (g : GL (Fin n) R) :
    g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range ↔
      ∀ i, glPiEquiv d n e g i ∈ (GeneralLinearGroup.map (n := Fin n) B.subtype).range := by
  simp only [mem_range_map_subtype_iff, glPiEquiv_val, glPiEquiv_inv_val, hAB]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨fun a b => h1 a b i, fun a b => h2 a b i⟩
  · intro h
    exact ⟨fun a b i => (h i).1 a b, fun a b i => (h i).2 a b⟩

end GlobalTheory.LKRes
