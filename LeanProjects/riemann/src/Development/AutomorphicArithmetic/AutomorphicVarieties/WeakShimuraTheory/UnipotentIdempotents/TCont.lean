import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws.Lk

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

theorem K_le (T : Tower D) : T.K ≤ T.L := by
  rw [T.hL]
  exact le_sup_right

abbrev toQ {Γ : Type} [Group Γ] (χ : Γ →* c.Oˣ) : Γ →* (PadicAlgCl l)ˣ := W.pushCh (algebraMap c.O (PadicAlgCl l)) χ

structure Pre (T : Tower D) where
  κ₀ : G T.K Ω →* (PadicAlgCl l)ˣ
  γ : G ℚ Ω →* (PadicAlgCl l)ˣ
  β : G T.K Ω →* (PadicAlgCl l)ˣ
  t : G T.K Ω →* Multiplicative ℤ_[l]
  κ₀_open : IsOpen (κ₀.ker : Set (G T.K Ω))
  κ₀_ord : ∃ m : ℕ, l.Coprime m ∧ κ₀ ^ m = 1
  κ₀_conj : ∀ σ ∉ T.K.fixingSubgroup, ∀ s s' : G T.K Ω, resQ T.K s' = σ * resQ T.K s * σ⁻¹ →
    (∃ m : ℕ, l.Coprime m ∧ D.ψ (resQ T.K s) ^ m = 1) →
    κ₀ s * κ₀ s' * toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) (resQ T.K s) = 1
  κ₀_unr : ∀ A, Raw.Away D.S A → Ine (F := T.K) A ≤ κ₀.ker
  γ_cont : Continuous γ
  γ_red : ∀ g, ‖(γ g : PadicAlgCl l) - 1‖ < 1
  γ_sq : ∀ g, γ g ^ 2 * toQ D.om g = cycBar ℚ Ω l g
  γ_ker : (cycZ ℚ Ω l).ker ≤ γ.ker
  β_cont : Continuous β
  t_cont : Continuous t
  β_t : t.ker ≤ β.ker
  β_red : ∀ s, ‖(β s : PadicAlgCl l) - 1‖ < 1
  conj : ∀ σ ∉ T.K.fixingSubgroup, ∀ s s' : G T.K Ω, resQ T.K s' = σ * resQ T.K s * σ⁻¹ → β s * β s' = 1 ∧ t s * t s' = 1
  t_unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := T.K) A ≤ t.ker
  cyc : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ s ∈ Ine (F := T.K) A,
    (β s ^ 2 * cycBar T.K Ω l s ^ (-b)) ^ k = 1

namespace Pre

variable {T : Tower D} (P : Pre T)

def βL : G T.L Ω →* (PadicAlgCl l)ˣ := P.β.comp (resLe (K_le T))

def tL : G T.L Ω →* Multiplicative ℤ_[l] := P.t.comp (resLe (K_le T))

def κ : G T.L Ω →* (PadicAlgCl l)ˣ :=
  P.κ₀.comp (resLe (K_le T)) * (P.γ.comp (resQ T.L))⁻¹ ^ (D.e + 4) * P.βL ^ (D.e % 2)

end Pre

structure QCh (T : Tower D) where
  κ : G T.L Ω →* (PadicAlgCl l)ˣ
  β : G T.L Ω →* (PadicAlgCl l)ˣ
  t : G T.L Ω →* Multiplicative ℤ_[l]
  κ_cont : Continuous κ
  β_cont : Continuous β
  t_cont : Continuous t
  β_t : t.ker ≤ β.ker
  β_red : ∀ g, ‖(β g : PadicAlgCl l) - 1‖ < 1
  conj : ∀ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, resQ T.L g' = σ * resQ T.L g * σ⁻¹ →
    κ g * κ g' * toQ D.th (resQ T.L g) * cycBar T.L Ω l g ^ 3 = 1 ∧ β g * β g' = 1 ∧ t g * t g' = 1
  t_unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := T.L) A ≤ t.ker
  unr : ∀ A, Raw.Away D.S A → Ine (F := T.L) A ≤ κ.ker
  tame : ∃ m : ℕ, l.Coprime m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A, κ g ^ m = 1
  mu : ∀ (g : G T.L Ω) (a : ℕ), g ^ l ^ a ∈ (commutator (G T.L Ω)).topologicalClosure → κ g = 1 ∧ t g = 1
  cyc : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (a b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ g ∈ Ine (F := T.L) A,
    (κ g * cycBar T.L Ω l g ^ (-a)) ^ k = 1 ∧ (β g ^ 2 * cycBar T.L Ω l g ^ (-b)) ^ k = 1

structure OCh (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) where
  κ : G T.L Ω →* c'.Oˣ
  β : G T.L Ω →* c'.Oˣ
  t : G T.L Ω →* Multiplicative ℤ_[l]
  κ_cont : AdicCont (maximalIdeal c'.O) fun g => (κ g : c'.O)
  β_cont : AdicCont (maximalIdeal c'.O) fun g => (β g : c'.O)
  t_cont : Continuous t
  β_t : t.ker ≤ β.ker
  β_red : ∀ g, residue c'.O (β g) = 1
  conj : ∀ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, resQ T.L g' = σ * resQ T.L g * σ⁻¹ →
    (κ g * κ g' : c'.O) * inc h (D.th (resQ T.L g)) * chiO T.L Ω l c'.O g ^ 3 = 1 ∧ β g * β g' = 1 ∧ t g * t g' = 1
  t_unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := T.L) A ≤ t.ker
  unr : ∀ A, Raw.Away D.S A → Ine (F := T.L) A ≤ κ.ker
  tame : ∃ m : ℕ, l.Coprime m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A, κ g ^ m = 1
  mu : ∀ (g : G T.L Ω) (a : ℕ), g ^ l ^ a ∈ (commutator (G T.L Ω)).topologicalClosure → κ g = 1 ∧ t g = 1
  cyc : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (a b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ g ∈ Ine (F := T.L) A,
    (κ g * chiO T.L Ω l c'.O g ^ (-a)) ^ k = 1 ∧ (β g ^ 2 * chiO T.L Ω l c'.O g ^ (-b)) ^ k = 1

def OCh.cb {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h) (i : Fin 4) : G T.L Ω →* (ResidueField c'.O)ˣ :=
  W.pushCh (residue c'.O) (X.κ * W.pushCh (inc h) ((chi D T.pr i).comp (resQ T.L)))

theorem OCh.cb_val {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h) (i : Fin 4) (g : G T.L Ω) :
    (X.cb i g : ResidueField c'.O) = residue c'.O (X.κ g * inc h (chi D T.pr i (resQ T.L g))) := rfl

structure SetD (T : Tower D) where
  s : W.HidaSetting l T.L Ω
  e : W.Vl l T.L ≃ T.ι
  hA : ∀ v : W.Vl l T.L, s.A v = T.pl (e v)
  fin : s.S.Finite
  away : ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp T.L)), IsPlaceOver A v → v ∉ s.S → Raw.Away D.S A
  away0 : Raw.Away D.S (s.A s.v0)
  eq0 : ∀ g ∈ Dec (F := T.L) (s.A s.v0), ∀ i j, Raw.bar (chi D T.pr i) (resQ T.L g) = Raw.bar (chi D T.pr j) (resQ T.L g)
  om0 : ∃ g ∈ Dec (F := T.L) (s.A s.v0), Raw.bar D.om (resQ T.L g) ≠ 1
  cc : ∃ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ →
    resQ T.L g' = σ * resQ T.L g * σ⁻¹

end UpperTheory.V.Ws.Lk

end
