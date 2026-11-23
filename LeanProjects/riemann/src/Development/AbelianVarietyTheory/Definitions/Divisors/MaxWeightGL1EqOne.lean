import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped Classical

namespace GlobalTheory.LKLoc

section Generic

variable {G : Type} [Group G]

def locPart (T K : Subgroup G) (x : G) : Subgroup G := T ⊓ K.map (MulAut.conj x).toMonoidHom

def volRat (U V : Subgroup G) : ℝ := (V.relIndex U : ℝ) / (U.relIndex V : ℝ)

def maxWt (T K : Subgroup G) (x : G) : ℝ := ⨆ h : G, volRat (locPart T K h) (locPart T K x)

def orbSum (θ : G →* G) (K : Subgroup G) (δ : G) (w : G → ℝ) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    (w (Quotient.out q) : ℂ) * GlobalTheory.BCT.avg fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))

def twOrbM (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  orbSum θ K δ (maxWt (GlobalTheory.BCT.twCent θ δ) K) f

def twOrbU (θ : G →* G) (K : Subgroup G) (δ : G) (U : Subgroup G) (f : G → ℂ) : ℂ :=
  orbSum θ K δ (fun x => volRat U (locPart (GlobalTheory.BCT.twCent θ δ) K x)) f

theorem volRat_self (V : Subgroup G) : volRat V V = 1 := by
  simp [volRat, Subgroup.relIndex_self]

end Generic

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def frobR (r : ℕ) : Kn p K r →+* Kn p K r where
  toFun x := ⟨frobK p K (x : PadicAlgCl p), Kn_stable p K r (frobK p K) x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def intR (r : ℕ) : Subring (Kn p K r) := (Obar p).toSubring.comap (algebraMap (Kn p K r) (PadicAlgCl p))

def intK : Subring K := (Obar p).toSubring.comap (algebraMap K (PadicAlgCl p))

def sig (n r : ℕ) : GL (Fin n) (Kn p K r) →* GL (Fin n) (Kn p K r) :=
  GeneralLinearGroup.map (frobR p K r)

def Kint (n r : ℕ) : Subgroup (GL (Fin n) (Kn p K r)) :=
  (GeneralLinearGroup.map (intR p K r).subtype).range

def KintK (n : ℕ) : Subgroup (GL (Fin n) K) :=
  (GeneralLinearGroup.map (intK p K).subtype).range

def nrm (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) : GL (Fin n) (Kn p K r) :=
  (List.map (fun i => (⇑(sig p K n r))^[i] δ) (List.range r)).prod

def SigConj (n r : ℕ) (δ δ' : GL (Fin n) (Kn p K r)) : Prop :=
  ∃ g : GL (Fin n) (Kn p K r), δ' = g⁻¹ * δ * sig p K n r g

def twCentR (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) : Subgroup (GL (Fin n) (Kn p K r)) :=
  GlobalTheory.BCT.twCent (sig p K n r) δ

def TO (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) (φ : GL (Fin n) (Kn p K r) → ℂ) : ℂ :=
  twOrbM (sig p K n r) (Kint p K n r) δ φ

def TOU (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) (U : Subgroup (GL (Fin n) (Kn p K r)))
    (φ : GL (Fin n) (Kn p K r) → ℂ) : ℂ :=
  twOrbU (sig p K n r) (Kint p K n r) δ U φ

def Orb (n : ℕ) (γ : GL (Fin n) K) (f : GL (Fin n) K → ℂ) : ℂ :=
  twOrbM (MonoidHom.id _) (KintK p K n) γ f

def OrbU (n : ℕ) (γ : GL (Fin n) K) (U : Subgroup (GL (Fin n) K)) (f : GL (Fin n) K → ℂ) : ℂ :=
  twOrbU (MonoidHom.id _) (KintK p K n) γ U f

def pDiag (n r : ℕ) (a : Fin n → ℤ) : GL (Fin n) (Kn p K r) :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal fun i => (p : Kn p K r) ^ a i) (by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))

def phiR (n r : ℕ) (a : Fin n → ℤ) (g : GL (Fin n) (Kn p K r)) : ℂ :=
  if ∃ k₁ ∈ Kint p K n r, ∃ k₂ ∈ Kint p K n r, g = k₁ * pDiag p K n r a * k₂ then 1 else 0

def unitK (n : ℕ) (g : GL (Fin n) K) : ℂ := if g ∈ KintK p K n then 1 else 0

def KotInv (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) (m : ℤ) : Prop :=
  ‖((GeneralLinearGroup.det δ : (Kn p K r)ˣ) : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ m

def unif : Kˣ :=
  if h : ∃ π : Kˣ, vK p K π = 1 then h.choose
  else Units.mk0 (p : K) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

def unifR (r : ℕ) : (Kn p K r)ˣ :=
  Units.map (IntermediateField.inclusion (show K ≤ Kn p K r from le_sup_left)).toRingHom.toMonoidHom (unif p K)

def piDiag (n r : ℕ) (a : Fin n → ℤ) : GL (Fin n) (Kn p K r) :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal fun i => ((unifR p K r ^ a i : (Kn p K r)ˣ) : Kn p K r)) (by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _)

def phiRu (n r : ℕ) (a : Fin n → ℤ) (g : GL (Fin n) (Kn p K r)) : ℂ :=
  if ∃ k₁ ∈ Kint p K n r, ∃ k₂ ∈ Kint p K n r, g = k₁ * piDiag p K n r a * k₂ then 1 else 0

def KotInvU (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) (m : ℤ) : Prop :=
  vK p (Kn p K r) (GeneralLinearGroup.det δ) = m

end GlobalTheory.LKLoc
