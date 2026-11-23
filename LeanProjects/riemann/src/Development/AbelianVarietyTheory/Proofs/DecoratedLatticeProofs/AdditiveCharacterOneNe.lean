import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.LocalOrderMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Formalism.LocalToGlobal.Columns.ChainOneOk
import Formalism.LocalToGlobal.Columns.RowFormsLemmas

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.MatchCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
open GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix

theorem isOrd_ordX (R : Ranks) (j : ℕ) : IsOrd xPos (ordX R j) := by
  rintro ((i | i) | ⟨i, l⟩)
  · rfl
  · rfl
  · rw [ordX_d]; simp only [xPos]; ring

def ordTop (R : Ranks) (s : ℕ) (hm : R.m = s + 2) :
    Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m) :=
  (((ordZ R s hm).sumCongr (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv).trans
    (finCongr (by have := N_m_succ R; omega))

def joinRow {E : Type} [Field E] (R : Ranks) {n : ℕ} (x' : (Fin n → E) →ₗ[E] (Fin (R.N R.m - 1 + 0) → E))
    (η : (Fin n → E) →ₗ[E] E) : (Fin n → E) →ₗ[E] (Fin (R.N R.m) → E) :=
  LinearMap.pi fun i => if h : i.1 < R.N R.m - 1 + 0 then LinearMap.proj (⟨i.1, h⟩ : Fin (R.N R.m - 1 + 0)) ∘ₗ x' else η

section Concl
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Concl

section Arith
variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem intAt_nat (n : ℕ) : IntAt P (n : E) := by simpa using IntAt.coe P (n : 𝓞 E)

theorem reduction_natCast (n : ℕ) : redP P (n : E) = (n : 𝓞 E ⧸ P.asIdeal) := by
  simpa using reduction_coe P (n : 𝓞 E)

theorem reduction_natCast_eq_zero (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : redP P (q : E) = 0 := by
  rw [reduction_natCast]
  simpa using Ideal.Quotient.eq_zero_iff_mem.2 hq

theorem pow_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (n : ℕ) :
    IntAt P ((q : E) ^ (n + 1)) ∧ redP P ((q : E) ^ (n + 1)) = 0 := by
  induction n with
  | zero =>
    rw [zero_add, pow_one]
    exact ⟨intAt_nat q, reduction_natCast_eq_zero hq⟩
  | succ n ih =>
    rw [pow_succ]
    exact ⟨ih.1.mul (intAt_nat q), by rw [reduction_mul ih.1 (intAt_nat q), ih.2, zero_mul]⟩

theorem valuation_one₂ (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) : LocE.vP P q (1 : E) = 0 := by
  have hI : IntAt P (1 : E) := by simpa using intAt_nat (P := P) 1
  have hU : IsUnit (redP P (1 : E)) := by
    have := reduction_natCast (P := P) 1
    rw [Nat.cast_one, Nat.cast_one] at this
    rw [this]; exact isUnit_one
  have hex : ∃ z : ℤ, IsUnit (redP P ((1 : E) / (q : E) ^ z)) := ⟨0, by rwa [zpow_zero, div_one]⟩
  have hspec : IsUnit (redP P ((1 : E) / (q : E) ^ LocE.vP P q (1 : E))) := by
    unfold LocE.vP
    exact Classical.epsilon_spec hex
  by_contra hne
  obtain ⟨n, hk | hk⟩ := Int.eq_nat_or_neg (LocE.vP P q (1 : E))
  · obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
    rw [hk, zpow_natCast] at hspec
    by_cases hI' : IntAt P ((1 : E) / (q : E) ^ (k' + 1))
    · have e : (1 : E) = (q : E) ^ (k' + 1) * ((1 : E) / (q : E) ^ (k' + 1)) := by field_simp
      have h0 : redP P (1 : E) = 0 := by
        rw [e, reduction_mul (pow_red hq k').1 hI', (pow_red hq k').2, zero_mul]
      rw [h0] at hU
      exact not_isUnit_zero hU
    · rw [reduction_eq_zero_of_not_integral P hI'] at hspec
      exact not_isUnit_zero hspec
  · obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
    rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, reduction_mul hI (pow_red hq k').1, (pow_red hq k').2,
      mul_zero] at hspec
    exact not_isUnit_zero hspec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Arith

section Hyp
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k)

def TailTrivial (P : HeightOneSpectrum (𝓞 X.E)) : Prop :=
  ∀ i, R.m ≤ i → ∀ a : X.Eˣ, IsUnit (redP P (a : X.E)) → S.μ (i + 1) (Units.map ι.toMonoidHom a) = 1

end Hyp

section Trunc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def trunc : SymData k s κ :=
  { S with
    μ := fun j => if j ≤ s + 2 then S.μ j else 1
    tame := fun j => by
      split_ifs
      · exact S.tame j
      · exact fun _ _ => rfl }

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Trunc

section Ext
variable {E K K' : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field K'] (φ : K →+* K')
  {P : HeightOneSpectrum (𝓞 E)}

end Ext

section Reparam
variable (X : Fields) (K' : Type) [Field K'] [NumberField K']

abbrev extFields : Fields where
  F := X.F
  E := X.E
  K := K'
  starK := starRingOfComm
  Tau := Empty
  emb := Empty.elim

def onePrimes (π : 𝓞 X.E) : Primes (extFields X K') where
  cond := 0
  g := 0
  piG := fun _ => X.conjO π
  Word := Empty
  T := Empty.elim
  piT := Empty.elim

variable {X K'} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (φ : X.K →+* K') (π : 𝓞 X.E)

def extChars : Chars (extFields X K') (onePrimes X K' π) R.m where
  psi0 := fun w => (φ : X.K →* K').compAddChar (psi0P Ch w.1)
  chi := fun j w => (Units.map (φ : X.K →* K')).comp (chiP Ch w.1 j)
  muVal := 1
  etaVal := 1

variable {π} {P : HeightOneSpectrum (𝓞 X.E)}

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (z : K')

def extCst (π : 𝓞 X.E) : LocCst (extFields X K') (rowSG (onePrimes X K' π) sel (mu0 X.F X.E K' S₀)) where
  psi := fun _ a => φ (cst.psi P a)
  D := fun _ => 1
  sq := fun _ => z
  muq := fun j _ => φ (cst.muq j P)
  A := cst.A
  B := cst.B
  M := 1
  sharp := true

variable {P} (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true) (hq : (qOf P.1 : X.E) ≠ 0) (hP' : P.1 ∈ (onePrimes X K' π).vGs)

end Reparam

end GlobalTheory.MatchCompare
