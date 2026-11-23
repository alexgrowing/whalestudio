import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyDef

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def fvec {m : Type} [DecidableEq m] (a : ℕ) (b : ℤ) (d : ℕ) (lam : ℂ) (x y : ℤ) (i₀ : m) : m → ℂ :=
  Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d))

def KeyHyps (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) : Prop :=
  CmOK a b c d ∧ IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ ∧ (∀ z ∈ Λ, cmTheta b d • z ∈ Λ) ∧
  relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0 ∧ relIdx Λ (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
  l.Prime ∧ ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 ∧ i₀ ∉ T ∧
  (∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d))))

def ApproxAt (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (k : ℕ) (w : m → ℂ) : Prop :=
  SatMem l Λ w ∧ (∀ j ∈ T, w j = 0) ∧ ∃ p q : ℤ, ¬ (l : ℤ) ∣ q ∧
    stdH (cmL a b d ha hd lam hlam) m w w =
      stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) * (1 + (l : ℂ) ^ k * p / q)

def KeyStart : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → ∃ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ 1 w

def KeyNewton : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → ∀ k, 1 ≤ k → ∀ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ k w → ∃ w', ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ (2 * k) w'

def KeyExact : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → ∃ K₀ : ℕ, ∀ k, K₀ ≤ k → ∀ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ k w →
    ∃ v : m → ℂ, SatMem l Λ v ∧ (∀ j ∈ T, v j = 0) ∧
      stdH (cmL a b d ha hd lam hlam) m v v =
        stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀)

theorem approx_pow_two (hN : KeyNewton) (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀) (w : m → ℂ) (hw : ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ 1 w) :
    ∀ n : ℕ, ∃ w', ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ (2 ^ n) w' := by
  intro n
  induction n with
  | zero => exact ⟨w, by simpa using hw⟩
  | succ n ih =>
    obtain ⟨w₁, hw₁⟩ := ih
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    obtain ⟨w₂, hw₂⟩ := hN a b c d ha hd lam hlam m Λ l x y T i₀ h (2 ^ n) (by omega) w₁ hw₁
    refine ⟨w₂, ?_⟩
    have he : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
    rw [he]
    exact hw₂

private theorem le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
    rw [pow_succ]
    omega

theorem keyRep_of (hS : KeyStart) (hN : KeyNewton) (hE : KeyExact) : KeyRep := by
  intro a b c d ha hd lam hlam hadm m _ _ Λ hsd hgen hi₁ hi₂ l hl x y hxy T i₀ hi₀ hT
  have h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ :=
    ⟨hadm, hsd, hgen, hi₁, hi₂, hl, hxy, hi₀, hT⟩
  obtain ⟨w, hw⟩ := hS a b c d ha hd lam hlam m Λ l x y T i₀ h
  obtain ⟨K₀, hK⟩ := hE a b c d ha hd lam hlam m Λ l x y T i₀ h
  obtain ⟨w', hw'⟩ := approx_pow_two hN a b c d ha hd lam hlam m Λ l x y T i₀ h w hw K₀
  exact hK (2 ^ K₀) (le_two_pow_self K₀) w' hw'

end PI.UnitaryGroupMassFormula.UnimodLocStd
