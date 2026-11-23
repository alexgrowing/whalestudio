import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.SecondLeviFamily
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction

noncomputable section

open Finset

namespace PositivityTheory.RgBcC.RealD

open Formalism.REAL (GlRel)

def LeviCommutantWordReduction : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), InvLv lev b →
    ∀ ν : Fin n → ℝ, (∀ a c, lev a = lev c → ν a = ν c) → ∃ z : FreeAlgebra ℂ (ℕ × ℂ),
      ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 →
        ∀ h : H, (∀ a c, lev a = lev c → (F1 a c + F2 a c) h = if a = c then (ν a : ℂ) • h else 0) →
          evLv lev F1 F2 b h = evCap lev F1 z h

def CapelliProductsScalar : Prop :=
  ∀ (n : ℕ) (L : Fin n → ℝ), StrictAnti L → ∀ lev : Fin n → ℕ, Monotone lev → ∀ (ν : Fin n → ℝ) (σ1 σ2 : ℕ → ℂ),
    (∀ j, (∑ a ∈ blk lev j, (ν a : ℂ)) - ((blk lev j).card : ℂ) * (σ1 j + σ2 j) = 2 * ∑ a ∈ blk lev j, (L a : ℂ)) →
    ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 →
    ∀ c : H, (∀ a b, lev a = lev b → (F1 a b + F2 a b) c = if a = b then (ν a : ℂ) • c else 0) →
      (∀ u : ℂ, capProd F1 lev σ1 u c = (∏ a, (u + (L a : ℂ))) • c) →
      (∀ u : ℂ, capProd F2 lev σ2 u c = (∏ a, (u + (L a : ℂ))) • c) →
      ∀ j u, capS F1 lev j u c = (∏ a ∈ blk lev j, (u + σ1 j + (L a : ℂ))) • c

def InvPick : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), AdmFor lam lev E1 E2 → ∀ (μ : Fin n → ℝ) (v w : V),
    v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → v ≠ 0 → (∃ x ∈ alg E1 E2, x v = w) → ∃ a, InvKP n a ∧ evKP E1 E2 a v = w

def LevStab : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 → ∀ p q, lev p = lev q →
      ∀ x ∈ bdSub lev E1 E2, firstLeviFamily lev E1 E2 p q x ∈ bdSub lev E1 E2 ∧ secondLeviFamily lev E1 E2 p q x ∈ bdSub lev E1 E2

def LevRel : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 → IsLevPairA lev (firstLeviFamily lev E1 E2) (secondLeviFamily lev E1 E2)

def SemiCls : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ v ∈ hwSp E1 E2 (muQ lam lev), ∀ a c, lev a = lev c →
        (firstLeviFamily lev E1 E2 a c + secondLeviFamily lev E1 E2 a c) (Pi.single (omU lev) v) =
          if a = c then ((muQ lam lev a + 2 * rhoU lev a : ℝ) : ℂ) • Pi.single (omU lev) v else 0

def CapCls : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∃ σ1 σ2 : ℕ → ℂ,
    (∀ j, (∑ a ∈ blk lev j, ((muQ lam lev a + 2 * rhoU lev a : ℝ) : ℂ)) - ((blk lev j).card : ℂ) * (σ1 j + σ2 j) =
      2 * ∑ a ∈ blk lev j, (Lr lam a : ℂ)) ∧
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ v ∈ hwSp E1 E2 (muQ lam lev), ∀ u : ℂ,
        capProd (firstLeviFamily lev E1 E2) lev σ1 u (Pi.single (omU lev) v : Cq n V) - (∏ a, (u + (Lr lam a : ℂ))) • (Pi.single (omU lev) v : Cq n V) ∈
            bdSub lev E1 E2 ∧
        capProd (secondLeviFamily lev E1 E2) lev σ2 u (Pi.single (omU lev) v : Cq n V) - (∏ a, (u + (Lr lam a : ℂ))) • (Pi.single (omU lev) v : Cq n V) ∈
            bdSub lev E1 E2

def MultiplicityAssembly : Prop :=
  InvPick → InjUU → HCdecLv → ActUU → LevStab → LevRel → SemiCls → CapCls → LeviCommutantWordReduction → CapelliProductsScalar → MultFor

end PositivityTheory.RgBcC.RealD
