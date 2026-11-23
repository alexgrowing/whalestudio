import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.Top

namespace UpperTheory.V.HV

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)

def Congr (a b : G ℚ Ω →* c.Oˣ) : Prop := ∀ σ, ((a σ : c.Oˣ) : c.O) - ((b σ : c.Oˣ) : c.O) ∈ IsLocalRing.maximalIdeal c.O

def IsOmT (w : G ℚ Ω →* c.Oˣ) : Prop := w ^ (l - 1) = 1 ∧ Congr c w (chiO ℚ Ω l c.O)

structure GDlit (K : Type) [Field K] [NumberField K] [Algebra K Ω] (e : ℕ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N)
    (w η : G ℚ Ω →* c.Oˣ) (a : ℕ) : Prop where
  om : IsOmT c w
  eta_ker : η.ker = galOf ℚ K Ω
  l_odd : l ≠ 2
  e_pos : 1 ≤ e
  N_even : Even N
  ord : ¬ l ∣ orderOf (Chr.dirG ℚ Ω ψ)
  ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω ψ σ = w σ ^ a
  a_lt : a < l - 1
  two_a : l - 1 ∣ 2 * a
  par : ∀ σ : G ℚ Ω, IsCC σ → Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1
  quad : Module.finrank ℚ K = 2
  imag : IsTotallyComplex K
  l_cop : ¬ l ∣ (discr K).natAbs * classNumber K
  cop : (discr K).natAbs.Coprime N
  eta : ∀ i j : ℕ, ¬ Congr c η (w ^ i * (Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹) ^ j)
  gen : ¬ l - 1 ∣ 2 * (e + a)

end UpperTheory.V.HV

end
