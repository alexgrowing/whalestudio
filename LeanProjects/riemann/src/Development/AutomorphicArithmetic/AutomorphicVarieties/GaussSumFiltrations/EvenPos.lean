import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Hilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
open UpperHalfPlane hiding I
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

abbrev Hn (F : Type) [Field F] [NumberField F] : Type := InfinitePlace F → ℍ

section Slash

variable {F : Type} [Field F] [NumberField F]

def cmp (v : InfinitePlace F) : GL (Fin 2) (InfinitePlace F → ℝ) →* GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v)

def act (h : GL (Fin 2) (InfinitePlace F → ℝ)) (z : Hn F) : Hn F := fun v => cmp v h • z v

def Pos (h : GL (Fin 2) (InfinitePlace F → ℝ)) : Prop := ∀ v, 0 < (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v

def sl0 (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (f : Hn F → ℂ) : Hn F → ℂ :=
  fun z => (∏ v, denom (cmp v h) (z v))⁻¹ ^ k * f (act h z)

def sl (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (f : Hn F → ℂ) : Hn F → ℂ :=
  fun z => (((∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * sl0 k h f z

def Hol (f : Hn F → ℂ) : Prop :=
  DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => f fun v => ofComplex (z v)) {z | ∀ v, 0 < (z v).im}

def Gr (f : Hn F → ℂ) : Prop :=
  ∃ (C : ℝ) (A : ℕ), ∀ z, ‖f z‖ ≤ C * (∏ v, (1 + ‖(z v : ℂ)‖ ^ 2) / (z v).im) ^ A

def et (x : F) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))

def wm {R : Type} [CommRing R] (c : Rˣ) : GL (Fin 2) R where
  val := !![0, -((c⁻¹ : Rˣ) : R); (c : R), 0]
  inv := !![0, ((c⁻¹ : Rˣ) : R); -(c : R), 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

def toFin : GL (Fin 2) F →* GL (Fin 2) (Af F) := Matrix.GeneralLinearGroup.map (algebraMap F (Af F))

def PInt (p : ℕ) (x : F) : Prop := ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → w.valuation F x ≤ 1

def PUnit (p : ℕ) (x : F) : Prop := ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → w.valuation F x = 1

def IsDel (p : ℕ) (δ : F) : Prop := ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
  w.valuation F δ = WithZero.exp (-(ordI w (differentIdeal ℤ (𝓞 F)) : ℤ))

def AtP (p : ℕ) (δ : F) (y : (Af F)ˣ) : Prop := ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
  Valued.v (pLoc F w (y : Af F)) * w.valuation F δ = 1

def InGam (N : ℕ) (γ : GL (Fin 2) F) : Prop :=
  γ.val.det = 1 ∧ IsIntegral ℤ (γ.val 0 0) ∧ IsIntegral ℤ (γ.val 0 1) ∧ IsIntegral ℤ (γ.val 1 0 / N) ∧ IsIntegral ℤ (γ.val 1 1)

variable [IsTotallyReal F]

def TP (x : F) : Prop := ∀ v, 0 < reAt v x

def rhom : F →+* (InfinitePlace F → ℝ) := Pi.ringHom fun v => InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)

def toInf : GL (Fin 2) F →* GL (Fin 2) (InfinitePlace F → ℝ) := Matrix.GeneralLinearGroup.map rhom

def ez (ξ : F) (z : Hn F) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ : ℂ) * (z v : ℂ))

def HasQ (f : Hn F → ℂ) (a : F → ℂ) : Prop :=
  (∃ D : ℕ, 0 < D ∧ ∀ ξ, a ξ ≠ 0 → (ξ = 0 ∨ TP ξ) ∧ IsIntegral ℤ ((D : F) * ξ)) ∧ ∀ z, HasSum (fun ξ => a ξ * ez ξ z) (f z)

def Small {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (r : ℝ) (f : Hn F → ℂ) : Prop :=
  ∃ a, HasQ f a ∧ ∀ ξ, ‖ι.symm (a ξ)‖ ≤ r

def InG (p : ℕ) (δ : F) (γ : GL (Fin 2) F) : Prop :=
  PInt p (γ.val 0 0) ∧ PInt p (δ * γ.val 0 1) ∧ PInt p (γ.val 1 0 / δ) ∧ PInt p (γ.val 1 1) ∧ PUnit p γ.val.det ∧ TP γ.val.det

def Stab (g : GL (Fin 2) (Af F)) (γ : GL (Fin 2) F) : Prop :=
  TP γ.val.det ∧ ∃ (z : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ KLev F 2 1 ∧
    toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g * u

structure Seed {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (δ : F) (θ : Hn F → ℂ) : Prop where
  hol : Hol θ
  gr : Gr θ
  one : ∀ γ, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ) θ - 1)
  lev : ∃ N : ℕ, 0 < N ∧ ∀ γ, InGam N γ → ∃ ζ : ℂ, ζ ^ 8 = 1 ∧ sl0 (p - 1) (toInf γ) θ = ζ • θ

structure Comp {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (δ : F) (k : ℕ) (g : GL (Fin 2) (Af F)) (f : Hn F → ℂ) : Prop where
  hol : Hol f
  gr : Gr f
  inv : ∀ γ, Stab g γ → sl k (toInf γ) f = f
  one : ∀ γ, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 k (toInf γ) f - 1)

structure Sys (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) : Prop where
  hol : ∀ g, Hol (Ψ g)
  gr : ∀ g, Gr (Ψ g)
  left : ∀ γ : GL (Fin 2) F, TP γ.val.det → ∀ g, sl k (toInf γ) (Ψ (toFin γ * g)) = Ψ g
  right : ∀ g, ∀ u ∈ KLev F 2 1, Ψ (g * u) = Ψ g
  cent : ∀ (z : (Af F)ˣ) g, Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = Ψ g

def IsLift (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) : Prop :=
  (∀ γ g, φ (ratGL F 2 γ * g) = φ g) ∧
    ∀ h, Pos h → ∀ g, φ (TR.infGL F 2 h * finGL F 2 g) = sl k h (Ψ g) fun _ => UpperHalfPlane.I

end Slash

section Theta

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

def BF (G : Matrix κ κ ℤ) (x y : κ → F) : F := x ⬝ᵥ (G.map (Int.cast : ℤ → F)) *ᵥ y

def QF (G : Matrix κ κ ℤ) (x : κ → F) : F := BF G x x / 2

variable (F κ) in

def LL : AddSubgroup (κ → F) := AddSubgroup.pi Set.univ fun _ => (integralClosure ℤ F).toSubring.toAddSubgroup

variable (κ) in

def aL (a : F) : AddSubgroup (κ → F) := (LL F κ).map (DistribMulAction.toAddMonoidHom (κ → F) a)

variable (F) in

def dualL (G : Matrix κ κ ℤ) : AddSubgroup (κ → F) where
  carrier := {y | ∀ l ∈ LL F κ, ∃ n : ℤ, Algebra.trace ℚ F (BF G y l) = n}
  zero_mem' := fun l _ => ⟨0, by simp [BF]⟩
  add_mem' {x y} hx hy := fun l hl => by
    obtain ⟨m, hm⟩ := hx l hl
    obtain ⟨n, hn⟩ := hy l hl
    refine ⟨m + n, ?_⟩
    simp only [BF] at hm hn ⊢
    rw [add_dotProduct, map_add, hm, hn, Int.cast_add]
  neg_mem' {x} hx := fun l hl => by
    obtain ⟨m, hm⟩ := hx l hl
    refine ⟨-m, ?_⟩
    simp only [BF] at hm ⊢
    rw [neg_dotProduct, map_neg, hm, Int.cast_neg]

def IsReps {V : Type} [AddCommGroup V] (A B : AddSubgroup V) (T : Finset V) : Prop :=
  (∀ y ∈ T, y ∈ B) ∧ ∀ x ∈ B, ∃! y, y ∈ T ∧ x - y ∈ A

def IsSB (N : ℕ) (Φ : (κ → F) → ℂ) : Prop :=
  (∀ x, Φ x ≠ 0 → x ∈ aL κ (N : F)⁻¹) ∧ ∀ x, ∀ l ∈ aL κ (N : F), Φ (x + l) = Φ x

def EvenPos (G : Matrix κ κ ℤ) : Prop := (G.map (Int.cast : ℤ → ℝ)).PosDef ∧ ∀ i, Even (G i i)

structure LatD (p : ℕ) (G S : Matrix κ κ ℤ) (t : ℕ) : Prop where
  card : Fintype.card κ = 2 * (p - 1)
  pos : EvenPos G
  iso : Sᵀ * G * S = G
  cyc : ∑ i ∈ Finset.range p, S ^ i = 0
  det : G.det = (t : ℤ) ^ 2
  cong : (-1) ^ ((p - 1) / 2) * (t : ℤ) ≡ 1 [ZMOD p]

def Good {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (S : Matrix κ κ ℤ) (Φ : (κ → F) → ℂ) : Prop :=
  (∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ IsSB N Φ) ∧ (∀ x, Φ (S.map (Int.cast : ℤ → F) *ᵥ x) = Φ x) ∧
    (∀ x, ‖ι.symm (Φ x)‖ ≤ 1) ∧ ‖ι.symm (Φ 0) - 1‖ ≤ (p : ℝ)⁻¹

def wC (k t : ℕ) (a c : F) : ℂ :=
  (-Complex.I) ^ (k * Module.finrank ℚ F) * ((Algebra.norm ℚ c : ℚ) : ℂ) ^ k /
    (((Algebra.norm ℚ a : ℚ) : ℂ) ^ (2 * k) * ((discr F).natAbs : ℂ) ^ k * (t : ℂ) ^ Module.finrank ℚ F)

open Classical in

def wT (G : Matrix κ κ ℤ) (k t : ℕ) (a c : F) (T : Finset (κ → F)) (Φ : (κ → F) → ℂ) (y : κ → F) : ℂ :=
  if (a / c) • y ∈ dualL F G then wC k t a c * ∑ x ∈ T, Φ x * et (BF G y x / c) else 0

open Classical in

def oneL (x : κ → F) : ℂ := if x ∈ LL F κ then 1 else 0

variable [IsTotallyReal F]

def th (G : Matrix κ κ ℤ) (Φ : (κ → F) → ℂ) : Hn F → ℂ := fun z => ∑' x, Φ x * ez (QF G x) z

end Theta

end GlobalTheory.HilbertThetaSeries
