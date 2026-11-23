import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.Top

namespace UpperTheory.V.HV

structure GD (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (e : ℕ) {O : Type} [CommRing O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) : Prop where
  l_odd : l ≠ 2
  e_pos : 1 ≤ e
  N_even : Even N
  ord : ¬ l ∣ orderOf ψ
  ine : comp l ψ ^ 2 = 1
  par : PsiEven e ψ
  quad : Module.finrank ℚ K = 2
  imag : IsTotallyComplex K
  l_cop : ¬ l ∣ (discr K).natAbs * classNumber K
  cop : (discr K).natAbs.Coprime N
  eta : ¬ (cycMod ℚ Ω l 1).ker ⊓ (Chr.dirG ℚ Ω (chiP l ψ)).ker ≤ galOf ℚ K Ω
  gen : ¬ l - 1 ∣ 2 * e

def CorG : Prop :=
  ∃ c5 : ℝ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (e N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (p p' : ℕ), p.Prime → p'.Prime → p ≠ p' →
    ¬ p ∣ 30 * N * (discr K).natAbs → ¬ p' ∣ 30 * N * (discr K).natAbs →
    ∀ (c : ∀ l : Nat.Primes, Coef l) (Ls : Finset Nat.Primes), (∀ l ∈ Ls, ∃ ψ ∈ orb (c l) H, GD Ω K l e ψ) →
      (∀ l ∈ Ls, ∀ ψ ∈ orb (c l) H, Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ l ∈ Ls, Real.log (l : ℕ) * ∑ ψ ∈ orb (c l) H, Vn Ω (c l) e ψ ≤
        4 * c5 * (Nat.totient H.index) * ((discr K).natAbs : ℝ) ^ 5 * (N : ℝ) ^ 18 * (e : ℝ) ^ 7 * (Real.log p + Real.log p')

def ColumnFamilyFiltrationProperties : Prop :=
  ∃ C2 : ℝ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ),
    l ≠ 2 → 1 ≤ e → ∀ ψ ∈ h.X c e, h.R1 l ψ ≤ 2 ^ c2 ψ →
      VLe Ω c e ψ (C2 * Nat.totient (orderOf ψ) * (h.N : ℝ) ^ 18 * (e : ℝ) ^ 7 * Real.log (Real.log ((l : ℝ) * h.N)))

def pZero (m : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ m}

def leSqrtOfDivSqGeOne (c4 : ℝ) (o l n' N p1 e : ℕ) : ℝ :=
  c4 / 21 * o * l * 2 ^ n' * ((l : ℝ) * 2 ^ n' * N * p1) ^ 16 * (e : ℝ) ^ 5 * Real.log (pZero (l * N * p1))

def ColumnFamilyStandardVectorsBasis : Prop :=
  ∃ c4 : ℝ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t →
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e,
      (h.CaseII l e ψ → VLe Ω c e ψ (leSqrtOfDivSqGeOne c4 h.o l (h.nII l ψ) h.N 1 e)) ∧
      (h.CaseIII l e ψ → VLe Ω c e ψ (leSqrtOfDivSqGeOne c4 h.o l (h.nIII l ψ) h.N (pOne h.chi) e))

def PropZ : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ),
    5 ≤ l → 2 ≤ e → Even e → l - 1 ∣ 2 * e → Chr.V l e (1 : G ℚ Ω →* c.Oˣ) = 0

def CountI : Prop :=
  ∀ χ : PChar, ∃ (C r₁ r₂ : ℕ), r₁.Prime ∧ r₂.Prime ∧ ∀ h : Host, h.chi = χ → r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d →
    ∀ t : ℕ, h.Big t → ∀ e : ℕ, 0 < e → e < t → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
      (c : ∀ l : Nat.Primes, Coef l) (Ls : Finset Nat.Primes), (∀ l ∈ Ls, (l : ℕ) ≠ 2 ∧ h.CaseI l e) →
      (∀ l ∈ Ls, ∀ ψ ∈ h.X (c l) e, Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ l ∈ Ls, Real.log (l : ℕ) * ∑ ψ ∈ h.X (c l) e, Vn Ω (c l) e ψ ≤ ((h.N : ℝ) * t) ^ C

def CountShape (P : ∀ (h : Host) (l : ℕ) [Fact l.Prime] (c : Coef l) (_ : ℕ), DirichletCharacter c.O h.N → Prop) : Prop :=
  ∀ χ : PChar, ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, h.Big t →
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ),
      l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, P h l c e ψ → VLe Ω c e ψ (((l : ℝ) * h.N * e) ^ C)

def CountII : Prop := CountShape fun h l _ _ e ψ => h.CaseII l e ψ

def CountIII : Prop := CountShape fun h l _ _ e ψ => h.CaseIII l e ψ

def CountV : Prop := CountShape fun h l _ _ e ψ => h.CaseV l e ∧ h.R1 l ψ ≤ 2 ^ c2 ψ

def CountVs : Prop := CountShape fun h l _ _ e ψ => h.CaseV l e ∧ 2 ^ c2 ψ < h.R1 l ψ

def CountZ : Prop := CountShape fun h l _ _ e ψ => h.CaseZ l e ψ

end UpperTheory.V.HV

end
