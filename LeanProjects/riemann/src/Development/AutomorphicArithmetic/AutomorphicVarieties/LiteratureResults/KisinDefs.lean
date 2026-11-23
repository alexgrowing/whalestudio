import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinLit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems

noncomputable section

namespace UpperTheory.V.Lit

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc IsLocalRing Matrix

def dualTw {G A : Type} [Group G] [CommRing A] {n : ℕ} (χ : G →* Aˣ) (r : G →* GL (Fin n) A) : G →* GL (Fin n) A where
  toFun g :=
    { val := (χ g : A) • (r g⁻¹ : Matrix (Fin n) (Fin n) A)ᵀ
      inv := (χ g⁻¹ : A) • (r g : Matrix (Fin n) (Fin n) A)ᵀ
      val_inv := by
        rw [smul_mul_smul_comm, ← transpose_mul, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]; simp
      inv_val := by
        rw [smul_mul_smul_comm, ← transpose_mul, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]; simp }
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by
    simp only [Units.val_mul, _root_.mul_inv_rev, map_mul, transpose_mul, smul_mul_smul_comm])

section

variable (l : ℕ) [Fact l.Prime]

def HodgeDual : Prop :=
  ∀ (K : FinExt l) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] ℚ_[l] B] (n : ℕ) (ρ : ↥(GK K) →* GL (Fin n) B),
    (∀ i j, QCont l fun g => (ρ g : Matrix (Fin n) (Fin n) B) i j) → PotCr K (colRep ρ) →
    ∀ (a : ℤ) (h : ℕ) (m : ℤ → ℕ), (∀ i, i < a ∨ a + h < i → m i = 0) → ∑ i ∈ Finset.range (h + 1), m (a + i) = n →
      (HodgeType K (colRep ρ) m ↔
        HodgeLit K (colRep (dualTw (((cycA l l B).comp (GK K).subtype) ^ (-a)) ρ)) h fun i => m (a + i))

def TypeDual : Prop :=
  ∀ (K : FinExt l) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] ℚ_[l] B] (n : ℕ) (ρ : ↥(GK K) →* GL (Fin n) B),
    (∀ i j, QCont l fun g => (ρ g : Matrix (Fin n) (Fin n) B) i j) → ∀ (a : ℤ) (t : ↥(GK K) → B),
      (PotCr K (colRep ρ) ↔ PotCr K (colRep (dualTw (((cycA l l B).comp (GK K).subtype) ^ (-a)) ρ))) ∧
      ((∃ (L : FinExt l) (h : K.1 ≤ L.1), CrysTypeOver K L h (colRep ρ) n t) ↔
        PotCr K (colRep ρ) ∧ TypeLit K (colRep (dualTw (((cycA l l B).comp (GK K).subtype) ^ (-a)) ρ)) n t)

def HodgeSum : Prop :=
  ∀ (K : FinExt l) (B : Type) [CommRing B] [Nontrivial B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (n : ℕ)
    (ρ : ↥(GK K) →* GL (Fin n) B), (∀ i j, QCont l fun g => (ρ g : Matrix (Fin n) (Fin n) B) i j) →
    ∀ (m : ℤ → ℕ) (t : ↥(GK K) → B), PotCrysType K (colRep ρ) n m t →
      ∃ (a : ℤ) (h : ℕ), (∀ i, i < a ∨ a + h < i → m i = 0) ∧ ∑ i ∈ Finset.range (h + 1), m (a + i) = n

def TypeProd : Prop :=
  ∀ (K : FinExt l) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (J : Type) [Finite J] (C : J → Type)
    [∀ j, CommRing (C j)] [∀ j, Algebra ℚ_[l] (C j)] (p : ∀ j, B →ₐ[ℚ_[l]] C j), Function.Bijective (fun b j => p j b) →
    ∀ (n : ℕ) (ρ : ↥(GK K) →* GL (Fin n) B), (∀ i j, QCont l fun g => (ρ g : Matrix (Fin n) (Fin n) B) i j) →
    ∀ (m : ℤ → ℕ) (t : ↥(GK K) → B), PotCrysType K (colRep ρ) n m t ↔
      ∀ j, PotCrysType K (colRep ((GeneralLinearGroup.map (p j : B →+* C j)).comp ρ)) n m fun γ => p j (t γ)

def MapCont : Prop :=
  ∀ (A₀ : Type) [CommRing A₀] [IsLocalRing A₀] [IsNoetherianRing A₀] [IsAdicComplete (maximalIdeal A₀) A₀]
    [Finite (ResidueField A₀)] [CharP (ResidueField A₀) l] [Algebra ℤ_[l] A₀] (B : Type) [CommRing B] [Algebra ℚ_[l] B]
    [Module.Finite ℚ_[l] B] (x : A₀ →+* B), (∀ z : ℤ_[l], x (algebraMap ℤ_[l] A₀ z) = algebraMap ℚ_[l] B (z : ℚ_[l])) →
    ∀ (X : Type) [TopologicalSpace X] (f : X → A₀),
      (∀ N : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal A₀ ^ N) (f g)) → QCont l fun g => x (f g)

end

end UpperTheory.V.Lit
