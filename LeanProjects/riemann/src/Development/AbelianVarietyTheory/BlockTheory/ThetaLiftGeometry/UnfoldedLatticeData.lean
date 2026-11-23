import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnfoldedLatticeData

open Formalism.L2.Col

section Local

variable (g : ℕ) [Fact g.Prime]

abbrev Aut (N : ℕ) : Type := (Fin N → ℚ_[g]) ≃ₗ[ℚ_[g]] (Fin N → ℚ_[g])

abbrev HomQ (a b : ℕ) : Type := (Fin a → ℚ_[g]) →ₗ[ℚ_[g]] (Fin b → ℚ_[g])

abbrev Lat (N : ℕ) : Type := Submodule ℤ_[g] (Fin N → ℚ_[g])

def diagLat (N : ℕ) (e : ℕ → ℕ) : Lat g N :=
  Submodule.span ℤ_[g]
    (Set.range fun l : Fin N => (g : ℚ_[g]) ^ e l.1 • (Pi.single l 1 : Fin N → ℚ_[g]))

def stdLat (N : ℕ) : Lat g N := diagLat g N fun _ => 0

def lamSt (n c : ℕ) : Lat g (n + c) := diagLat g (n + c) fun l => if l < n then 0 else l - n + 1

def lamBase (hyp : Bool) (n c : ℕ) : Lat g (n + c) := if hyp then stdLat g (n + c) else lamSt g n c

variable {g}

def img {N : ℕ} (h : Aut g N) (Λ : Lat g N) : Lat g N := Λ.map (h.toLinearMap.restrictScalars ℤ_[g])

def GLlat {N : ℕ} (Λ : Lat g N) : Subgroup (Aut g N) where
  carrier := {κ | ∀ v, κ v ∈ Λ ↔ v ∈ Λ}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb v => (ha (b v)).trans (hb v)
  inv_mem' := fun {a} ha v => by
    have h := ha (a.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def InG {N : ℕ} (Λ : Lat g N) (v : Fin N → ℚ_[g]) : Prop := ∃ u ∈ Λ, v = (g : ℚ_[g]) • u

def Into {a b : ℕ} (Λ' : Lat g a) (Λ : Lat g b) (x : HomQ g a b) : Prop := ∀ v ∈ Λ', x v ∈ Λ

def InjMod {a b : ℕ} (Λ' : Lat g a) (Λ : Lat g b) (x : HomQ g a b) : Prop :=
  ∀ v ∈ Λ', InG Λ (x v) → InG Λ' v

def PeriodG {a b : ℕ} {M : Type} (Λ' : Lat g a) (Λ : Lat g b) (F : HomQ g a b → M) : Prop :=
  ∀ x y, Into Λ' Λ y → F (x + (g : ℚ_[g]) • y) = F x

def IsMu (g : ℕ) (ζ : ℂ) : Prop := ζ ^ (g * (g - 1)) = 1

def ZMu (g : ℕ) : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {ζ | IsMu g ζ}

def CondO (ψ : AddChar ℚ_[g] ℂ) : Prop :=
  (∀ u : ℤ_[g], ψ (u : ℚ_[g]) = 1) ∧ ∃ u : ℤ_[g], ψ ((u : ℚ_[g]) / (g : ℚ_[g])) ≠ 1

def Shape {a b : ℕ} (Λ' : Lat g a) (Λ₀ : Lat g b) (Φ : Loc.SF ℚ_[g] ℂ a b) : Prop :=
  (∀ x, Φ x ≠ 0 → Into Λ' Λ₀ x ∧ InjMod Λ' Λ₀ x ∧ IsMu g (Φ x)) ∧ PeriodG Λ' Λ₀ Φ

def IsLevel {N : ℕ} (Λ₀ : Lat g N) (J : Subgroup (Aut g N)) : Prop :=
  J ≤ GLlat Λ₀ ∧ ∀ κ ∈ GLlat Λ₀, (∀ v ∈ Λ₀, InG Λ₀ (κ v - v)) → κ ∈ J

def omg {a b : ℕ} (μ : ℚ_[g] →*₀ ℂ) (g₀ : Aut g a) (h : Aut g b) (Φ : Loc.SF ℚ_[g] ℂ a b) :
    Loc.SF ℚ_[g] ℂ a b :=
  Loc.om μ Padic.valuation ((Real.sqrt g : ℝ) : ℂ) g₀ h Φ

def PartialFourierTransformFinite {n' n c : ℕ} (ψ : AddChar ℚ_[g] ℂ) (A B : ℕ) (Φ : Loc.SF ℚ_[g] ℂ (n' + (c + 1)) (n + c)) :
    Loc.SF ℚ_[g] ℂ n' n :=
  Loc.E1 (fun t => ψ t) (LocE.valsQ ℚ_[g] g A B) (((g : ℂ) ^ B)⁻¹) Φ

def IsRationalUnitaryDeterminantMap {n' n c : ℕ} (ψ : AddChar ℚ_[g] ℂ) (Φ : Loc.SF ℚ_[g] ℂ (n' + (c + 1)) (n + c))
    (Ψ : Loc.SF ℚ_[g] ℂ n' n) : Prop :=
  ∃ A₀ B₀ : ℕ, ∀ A B, A₀ ≤ A → B₀ ≤ B → PartialFourierTransformFinite ψ A B Φ = Ψ

def GoodFlag {n c : ℕ} (Λ : Lat g (n + c)) : Prop :=
  (∀ s < c, ∀ z : ℚ_[g],
    (∃ v ∈ Λ, v ∈ Loc.Ufl ℚ_[g] n c (s + 1) ∧ Loc.atN v (n + s) = z) ↔
      ∃ u : ℤ_[g], z = (g : ℚ_[g]) ^ (s + 1) * u) ∧
  (g : ℚ_[g]) • Loc.eN ℚ_[g] (n + c) n ∈ Λ

def scal {a b : ℕ} (μ : ℚ_[g] →*₀ ℂ) (h' : Aut g a) (h : Aut g b) : ℂ :=
  μ (LinearEquiv.det h' : ℚ_[g]ˣ) * (μ (LinearEquiv.det h : ℚ_[g]ˣ))⁻¹ *
    ((Real.sqrt g : ℝ) : ℂ) ^ (Padic.valuation ((LinearEquiv.det h : ℚ_[g]ˣ) : ℚ_[g]) * (a : ℤ))

def volAt {n c : ℕ} (Λ : Lat g (n + c)) (C : Subgroup (Aut g (n + c))) : ℂ :=
  Loc.volN ℂ C (Loc.N1 ℚ_[g] n c ⊓ GLlat Λ)

end Local

def e₁ (n c : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 c, (i * n + i * (i - 1) / 2)

def dimN (n c : ℕ) : ℕ := c * (c - 1) / 2 + (c - 1) * n

def expS (n c : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 c, ∑ i' ∈ Finset.Ico 1 i, (i - i') + n * ∑ i ∈ Finset.Icc 2 c, i

def expSup (n c : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 c, (n + i)

section Clauses

variable (g : ℕ) [Fact g.Prime] (hyp : Bool) (n' n c : ℕ)

def SupportClause : Prop :=
  ∀ (ψ : AddChar ℚ_[g] ℂ) (μ : ℚ_[g] →*₀ ℂ) (Φ : Loc.SF ℚ_[g] ℂ (n' + (c + 1)) (n + c))
    (h' : Aut g (n' + (c + 1))) (h : Aut g (n + c)),
    CondO ψ → Shape (lamSt g n' (c + 1)) (lamBase g hyp n c) Φ → h' ∈ GLlat (lamSt g n' (c + 1)) →
      (∀ x, omg μ h' h Φ x ≠ 0 → Into (lamSt g n' (c + 1)) (img h (lamBase g hyp n c)) x) ∧
      PeriodG (lamSt g n' (c + 1)) (img h (lamBase g hyp n c)) (omg μ h' h Φ) ∧
      (∃ Ψ, IsRationalUnitaryDeterminantMap ψ (omg μ h' h Φ) Ψ) ∧
      (¬ IsRationalUnitaryDeterminantMap ψ (omg μ h' h Φ) 0 →
        GoodFlag (img h (lamBase g hyp n c)) ∧
        (∃ ρ ∈ Loc.R1 ℚ_[g] n c, img ρ (lamSt g n c) = img h (lamBase g hyp n c)) ∧
        ∀ h₀ : Aut g (n + c), img h₀ (lamBase g hyp n c) = lamSt g n c →
          ∃ ρ ∈ Loc.R1 ℚ_[g] n c, ∃ κ ∈ GLlat (lamBase g hyp n c), h = ρ * h₀ * κ)

def ShapeClause : Prop :=
  (∀ h : Aut g (n + c), GoodFlag (img h (lamBase g hyp n c)) →
    ∃ ρ ∈ Loc.R1 ℚ_[g] n c, img ρ (lamSt g n c) = img h (lamBase g hyp n c)) ∧
  (∃ h₀ : Aut g (n + c), img h₀ (lamBase g hyp n c) = lamSt g n c) ∧
  ∀ h : Aut g (n + c), img h (lamBase g hyp n c) = lamSt g n c →
    Padic.valuation ((LinearEquiv.det h : ℚ_[g]ˣ) : ℚ_[g]) =
      if hyp then ((c * (c + 1) / 2 : ℕ) : ℤ) else 0

def EntryClause (m N : ℕ) : Prop :=
  ∀ (J : Subgroup (Aut g (n + c))) (h : Aut g (n + c)),
    IsLevel (lamBase g hyp n c) J → img h (lamBase g hyp n c) = lamSt g n c →
      ∃ e₂ : ℕ, e₂ ≤ dimN n c ∧
        (volAt (lamSt g n c) (Loc.Cbe J h))⁻¹ = (g : ℂ) ^ e₂ ∧
        6 * (e₁ n c + e₂) ≤ 3 * m ^ 2 * N + m ^ 3 + 6 * m ^ 2 + 6 * m * N ∧
        e₁ n c + e₂ ≤ 4 * m ^ 2 * N ∧
        e₁ n c + e₂ + m * (N + m) ≤ 4 * m ^ 2 * N ∧
        ∀ (ψ : AddChar ℚ_[g] ℂ) (μ : ℚ_[g] →*₀ ℂ) (Φ : Loc.SF ℚ_[g] ℂ (n' + (c + 1)) (n + c))
          (h' : Aut g (n' + (c + 1))),
          CondO ψ → Shape (lamSt g n' (c + 1)) (lamBase g hyp n c) Φ →
          h' ∈ GLlat (lamSt g n' (c + 1)) →
            (∃ (Ψ : Loc.SF ℚ_[g] ℂ n' n) (Ψ₀ : HomQ g n' n → ZMu g),
              IsRationalUnitaryDeterminantMap ψ (omg μ h' h Φ) Ψ ∧
              (∀ x, Ψ x = scal μ h' h * (g : ℂ) ^ e₁ n c * (Ψ₀ x : ℂ)) ∧
              (∀ x, (volAt (lamSt g n c) (Loc.Cbe J h))⁻¹ * Ψ x =
                scal μ h' h * (g : ℂ) ^ (e₁ n c + e₂) * (Ψ₀ x : ℂ)) ∧
              (∀ x, Ψ₀ x ≠ 0 → Into (stdLat g n') (stdLat g n) x ∧ InjMod (stdLat g n') (stdLat g n) x) ∧
              PeriodG (stdLat g n') (stdLat g n) Ψ₀ ∧
              (∀ x, ∃ s : Multiset ℂ, Multiset.card s ≤ g ^ expSup n c ∧ Multiset.card s ≤ g ^ (m * (N + m)) ∧
                (∀ ζ ∈ s, IsMu g ζ) ∧ s.sum = (Ψ₀ x : ℂ)) ∧
              ∀ (σ : ZMu g →+* ℂ) (x : HomQ g n' n),
                ‖σ (Ψ₀ x)‖ ≤ (g : ℝ) ^ expSup n c ∧ ‖σ (Ψ₀ x)‖ ≤ (g : ℝ) ^ (m * (N + m))) ∧
            (hyp = false → (∀ u : ℤ_[g]ˣ, μ ((u : ℤ_[g]) : ℚ_[g]) ^ (g - 1) = 1) →
              scal μ h' h ^ (g - 1) = 1)

def MeasureClause (m N : ℕ) : Prop :=
  volAt (stdLat g (n + c)) (GLlat (lamSt g n c)) = (g : ℂ) ^ expS n c ∧
  expS n c ≤ m ^ 3 + m ^ 2 * N ∧ dimN n c ≤ m ^ 2 + m * N ∧ e₁ n c = expS n c + n

end Clauses

def UnfoldedDatum : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (hyp : Bool) (m j c n' t n N : ℕ),
    2 ≤ m → m ≤ N → 1 ≤ j → j + 2 ≤ m → c + j + 1 = m → n = n' + t + 1 → n ≤ N →
      SupportClause g hyp n' n c ∧ ShapeClause g hyp n c ∧ EntryClause g hyp n' n c m N ∧
        MeasureClause g n c m N

example : e₁ 5 2 = 16 ∧ dimN 5 2 = 6 ∧ expS 5 2 = 11 ∧ expSup 5 2 = 13 := by decide

example {g : ℕ} [Fact g.Prime] {a : ℕ} (Λ : Lat g a) :
    Into Λ Λ LinearMap.id ∧ InjMod Λ Λ LinearMap.id := ⟨fun _ h => h, fun _ _ h => h⟩

end GlobalTheory.IndefiniteRowSideFullHecke.UnfoldedLatticeData
