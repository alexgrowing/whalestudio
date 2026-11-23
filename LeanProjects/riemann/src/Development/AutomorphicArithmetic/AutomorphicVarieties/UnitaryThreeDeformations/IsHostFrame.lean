import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import ReciprocityTheory.Hypotheses.GalCoh

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3 IsLocalRing

namespace UpperTheory.V.UnitaryThreeInertia

structure HostData (l e : ℕ) {O : Type} [CommRing O] {N : ℕ} (ψ : DirichletCharacter O N) (o₁ : ℕ) : Prop where
  l_odd : l ≠ 2
  e_pos : 1 ≤ e
  N_even : Even N
  par : PsiEven e ψ
  o_pos : 1 ≤ o₁
  ord : ∀ r : ℕ, r.Prime → r ≠ 2 → comp r (th0 l ψ) ^ (2 * o₁) = 1
  R : ∀ v ∈ Tb l ψ, 8 * o₁ * v ^ 2 < 2 ^ c2 ψ
  four_le : 4 ≤ c2 ψ

abbrev Pl : Type := HeightOneSpectrum (𝓞 ℚ)

variable (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

def eta4 : G ℚ Ω →* ℤˣ := Chr.dirG ℚ Ω (ZMod.χ₄ : DirichletCharacter ℤ 4)

abbrev Gam (S : Finset Pl) : Type := GS Ω (S : Set Pl)

variable {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N]

structure IsHostFrame (e : ℕ) (ψ : DirichletCharacter c.O N) (S : Finset Pl) (A : S → ValuationSubring Ω)
    (F : Frame c.O (G ℚ Ω) (Gam Ω S) S) : Prop where
  mem : ∀ v : Pl, v ∈ S ↔ ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  isOver : ∀ v, IsPlaceOver (A v) v.1
  π : F.π = toGS Ω _
  η : F.η.comp F.π = eta4 Ω
  Ψ : F.Ψ.comp F.π = Chr.Psi l e (Chr.dirG ℚ Ω ψ)
  cc : ∃ σ : G ℚ Ω, IsCC σ ∧ F.π σ = F.c
  D : ∀ v, F.D v = Dec (F := ℚ) (A v)
  I : ∀ v, F.I v = Ine (F := ℚ) (A v)
  vl : ((l : ℕ) : 𝓞 ℚ) ∈ F.vl.1.asIdeal
  Sb : ∀ v, v ∈ F.Sb ↔ ∃ p ∈ HV.Sb l ψ, ((p : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal

def vl1 (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) : ℝ := -Real.log ‖x‖ / Real.log l

def XData (l : ℕ) {O : Type} [CommRing O] {N : ℕ} (ψ : DirichletCharacter O N) (q : ℕ) : Prop :=
  0 < q ∧ (th1 l ψ ^ 2).conductor ∣ q ∧ 2 * (l * q) * 4 ^ n0 l ψ ≤ 2 ^ c2 ψ

end UpperTheory.V.UnitaryThreeInertia

end
