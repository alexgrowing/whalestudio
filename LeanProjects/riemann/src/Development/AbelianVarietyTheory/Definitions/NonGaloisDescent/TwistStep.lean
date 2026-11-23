import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

def MatThm : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → AdmSt P ρ

def FrameEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (AdmDR P ρ ↔ ∃ w : Fin r → n → ℤ, Framed P ρ w)

def TwistStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ), IsRat r ρ → Framed P ρ w →
    ∃ (K' : FinExt l) (r' : ℕ) (ρ' : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)) (w' : Fin r' → n → ℤ),
      IsRat r' ρ' ∧ Framed P ρ' w' ∧ ∑ m, ∑ j, w' m j = 0 ∧ (AdmSt P ρ' → AdmSt P ρ)

def SenFinite : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]),
    (∀ i j, Continuous fun g => (ρ g : Matrix n n ℚ_[l]) i j) →
    ∀ M : GL n ℂ_[l], (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) *
      (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) →
    (ρ '' (IK K : Set ↥(GK K))).Finite

def UnrStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (ρ '' (IK K : Set ↥(GK K))).Finite → AdmSt P ρ

def SenStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → Framed P ρ (0 : Fin r → n → ℤ) → AdmSt P ρ

def Hyodo : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    (∀ v : V, Continuous fun g => ρ g v) → IsSst P ρ →
    ∀ c : ↥(GK K) → V, Continuous c → (∀ g h, c (g * h) = c g + ρ g (c h)) →
    (∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) →
    ∃ b : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g b - b

def ExtStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) →
    AdmDR P ρ → AdmSt P ρ₁ → AdmSt P ρ₂ → AdmSt P ρ

def SubQuot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) →
    AdmDR P ρ → AdmDR P ρ₁ ∧ AdmDR P ρ₂

def RedStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → Splits r ρ →
    (∀ (a : Type) [Fintype a] [DecidableEq a], Fintype.card a < Fintype.card n →
      ∀ ρ' : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l), IsRat r ρ' → AdmDR P ρ' → AdmSt P ρ') → AdmSt P ρ

def ModStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (x y : Fin r × n), x ≠ y →
    IsRat r ρ → Framed P ρ w → ¬ Splits r ρ →
    ∃ ρ' : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l), IsRat r ρ' ∧ Framed P ρ' (fun m j => w m j + eps x y (m, j)) ∧
      (AdmSt P ρ' → AdmSt P ρ)

def FLAt (r : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (U : Fin r → GL n P.R.BdR) (x y : Fin r × n), x ≠ y → (∀ m, UnitM P (U m)) →
    (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) →
      ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) →
    ∃ A : GL n P.R.B, (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) ∧
      ∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) =
        (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (eps x y (m, j))) * (W : Matrix n n P.R.BdR)

def Ratio : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h s : ℕ), s < h →
    ∀ ω ω' : P.R.B, Plus T ω → Plus T ω' → P.φB^[h] ω = (l : P.R.B) ^ s * ω → P.φB^[h] ω' = (l : P.R.B) ^ s * ω' →
    ω' ≠ 0 → P.φB ω * ω' = ω * P.φB ω' → ∃ c : ℚ_[l], ω = c • ω'

def Moore : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h k : ℕ), k ≤ h →
    ∀ a : Fin k → P.R.B, (∀ j, Plus T (a j)) → (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) →
    LinearIndependent ℚ_[l] a → (Matrix.of fun i j : Fin k => P.φB^[i] (a j)).det ≠ 0

def ExI : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h →
    ∀ μ : Fin h → P.R.BdR, (∀ i, μ i ∈ Fil P 0) → (∃ i, μ i ∉ Fil P 1) →
    ∃ b : Fin h → P.R.B, (∀ j, Plus T (b j)) ∧ (∀ j, P.φB^[h] (b j) = (l : P.R.B) * b j) ∧
      LinearIndependent ℚ_[l] b ∧ ∀ j, ∑ i, μ i * ev P i (b j) ∈ Fil P 1

def ExII : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h →
    ∀ lam : Fin h → P.R.BdR, (∀ j, lam j ∈ Fil P 0) →
    (∀ c : Fin h → ℚ_[l], ∑ j, c j • lam j ∈ Fil P 1 → c = 0) →
    ∃ a : Fin h → P.R.B, a ≠ 0 ∧ (∀ j, Plus T (a j)) ∧ (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) ∧
      ∀ i : Fin h, ∑ j, lam j * ev P i (a j) ∈ Fil P 1

def WeilRes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, fr l r ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) = (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) ∧
      ∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))

end GlobalTheory.PMon

end
