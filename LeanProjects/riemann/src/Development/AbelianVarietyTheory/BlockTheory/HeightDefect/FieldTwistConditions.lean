import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (zeta)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.FieldTwistConditions

def condE (D : D7) : ℕ := D.host.QS * D.host.q * D.host.d

def IsSpecial (D : D7) (p : ℕ) : Prop :=
  (p = D.host.pde ∨ p = D.host.pde') ∧ p % Nat.lcm 15 (condE D) = 1

def lev (D : D7) (p : ℕ) : ℕ := D.host.g 0 * D.host.g 1 * p

structure FieldCond (D : D7) (p : ℕ) : Prop where
  full : OFull D
  root : zeta (lev D p) ∈ FO D
  curve : GlobalTheory.CompRat.CurveOver (hostOfRecord D) (FO D) (lev D p)
  typeNorm : OKPsi D

structure FieldCondBoth (D : D7) : Prop where
  full : OFull D
  root : zeta (lev D (D.host.pde * D.host.pde')) ∈ FO D
  curve : GlobalTheory.CompRat.CurveOver (hostOfRecord D) (FO D) (lev D (D.host.pde * D.host.pde'))
  typeNorm : OKPsi D
  curveOverRationalsLevel12 : GlobalTheory.CompRat.CurveOver (hostOfRecord D) (FO D) 12
  rootG : ∀ i, zeta (D.host.g i * (D.host.g i - 1)) ∈ FO D
  root3 : zeta (3 ^ 4) ∈ FO D
  root5 : zeta (5 ^ 4) ∈ FO D

abbrev AfE (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

def bar (D : D7) : AfE D →+* AfE D := sigR (R := Af D.host.F) D.conjF

def barU (D : D7) : (AfE D)ˣ →* (AfE D)ˣ := Units.map (bar D).toMonoidHom

def NormOne (D : D7) (u : (AfE D)ˣ) : Prop := (u : AfE D) * bar D u = 1

def ratU (D : D7) : D.host.Eˣ →* (AfE D)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] AfE D).toRingHom.toMonoidHom

def quotBar (D : D7) : (AfE D)ˣ →* (AfE D)ˣ := MonoidHom.id _ / barU D

def SuppAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (u : (AfE D)ˣ) : Prop :=
  ∀ a : Af D.host.F, a v = 0 → (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((u : AfE D) - 1) = 0

def InertiaAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (u : (AfE D)ˣ) : Prop :=
  NormOne D u ∧ (u : AfE D) ∈ intAE D ∧ SuppAt D v u

def Reads (D : D7) (ξ : (AfE D)ˣ →* ℂˣ) (δ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, ((ξ (quotBar D (Units.map (finPart D).toMonoidHom x)) : ℂˣ) : ℂ) = (δ x : ℂ)

structure TwistCond (D : D7) (p : ℕ) (ξ : (AfE D)ˣ →* ℂˣ) : Prop where
  rat : ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 → ξ (ratU D z) = 1
  tame : ∀ u, NormOne D u → (∃ y ∈ intAE D, (u : AfE D) - 1 = p • y) → ξ u = 1
  inertia : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal →
    ∀ n : ℕ, (∀ u, InertiaAt D v u → ξ u ^ n = 1) ↔ 15 ∣ n
  fin : ∃ n : ℕ, 0 < n ∧ ∀ u, NormOne D u → ξ u ^ n = 1
  val : ∀ u, NormOne D u → ((ξ u : ℂˣ) : ℂ) ∈ FO D

structure RunCond (D : D7) (p : ℕ) (ξ : (AfE D)ˣ →* ℂˣ) : Prop where
  special : IsSpecial D p
  field : FieldCond D p
  twist : TwistCond D p ξ

variable {D : D7}

theorem zeta_mul_pow (n k : ℕ) (hk : k ≠ 0) : zeta (n * k) ^ k = zeta n := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  push_cast
  by_cases hn : (n : ℂ) = 0
  · simp [hn]
  · field_simp

theorem curveOver_of_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {F : IntermediateField ℚ ℂ} {n k : ℕ} (hk : k ≠ 0) (h : GlobalTheory.CompRat.CurveOver H F (n * k)) :
    GlobalTheory.CompRat.CurveOver H F n := by
  intro τ hτ
  obtain ⟨C, ι, h1, h2⟩ := h τ hτ
  refine ⟨C, ι, h1, fun a => ?_⟩
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have e : GlobalTheory.CompRat.wC H (k * a.1, k * a.2) = k * GlobalTheory.CompRat.wC H a := by
    simp only [GlobalTheory.CompRat.wC]; push_cast; ring
  have e1 : ∀ z : ℂ, (k : ℂ) * z / ((n * k : ℕ) : ℂ) = z / n := fun z => by
    rw [Nat.cast_mul, mul_comm (n : ℂ), mul_div_mul_left _ _ hk']
  have h3 := h2 (k * a.1, k * a.2)
  rwa [e, mul_left_comm, e1, e1] at h3

theorem FieldCondBoth.run (h : FieldCondBoth D) {p : ℕ} (hp : p = D.host.pde ∨ p = D.host.pde') : FieldCond D p := by
  obtain ⟨k, hk, e⟩ : ∃ k, k ≠ 0 ∧ lev D (D.host.pde * D.host.pde') = lev D p * k := by
    rcases hp with rfl | rfl
    · exact ⟨_, D.host.pde'_prime.ne_zero, by simp only [lev]; ring⟩
    · exact ⟨_, D.host.pde_prime.ne_zero, by simp only [lev]; ring⟩
  refine ⟨h.full, ?_, curveOver_of_mul hk (e ▸ h.curve), h.typeNorm⟩
  rw [← zeta_mul_pow _ k hk, ← e]
  exact pow_mem h.root k

theorem bar_bar (x : AfE D) : bar D (bar D x) = x := by
  have hc : ∀ e : D.host.E, D.conjF (D.conjF e) = e := fun e => by
    apply D.host.φ₀.injective
    rw [D.conjF_eq, D.conjF_eq]
    have h := fun e => D.host.conjE_apply D.host.φ₀ e
    rw [h, h]
    simp
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [bar, sigR, hc]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.IndefiniteRowSideFullHecke.FieldTwistConditions
