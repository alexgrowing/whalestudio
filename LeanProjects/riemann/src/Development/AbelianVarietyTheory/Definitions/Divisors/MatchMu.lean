import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace

noncomputable section

open Matrix GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.BCFL

variable {p : ℕ} [Fact p.Prime]

def muSet (G : HTGroup p) (r : ℕ) (w₀ : Fin G.m) : Set (Gr G r) :=
  {δ | GlobalTheory.LKLoc.KotInv p (Q0 p) 1 r δ.1 (-1) ∧
    (∀ w, (∀ i j, ((δ.2 w)⁻¹).val i j ∈ intKQ p (G.Fw w) r) ∧
      ‖Algebra.norm ℚ_[p] (δ.2 w).val.det‖ = (p : ℝ) ^ (r * if w = w₀ then 1 else 0)) ∧
    1 < ‖GlobalTheory.LKGeo.mulKQ (G.Fw w₀) r ((sigKQ p (G.Fw w₀) r)^[r - 1] (δ.2 w₀).val.det)‖}

def phiMu (G : HTGroup p) (r : ℕ) (w₀ : Fin G.m) (δ : Gr G r) : ℂ :=
  if δ ∈ muSet G r w₀ then 1 else 0

def MatchMu : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ w₀ : Fin G.m,
    ∃ f' : Gr G 1 → ℂ, IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) (KHT p G.m G.n 1 G.Fw) f' ∧
      (∀ k₁ ∈ KHT p G.m G.n 1 G.Fw, ∀ k₂ ∈ KHT p G.m G.n 1 G.Fw, ∀ g, f' (k₁ * g * k₂) = f' g) ∧
      Match G r (KHT p G.m G.n r G.Fw) (phiMu G r w₀) (KHT p G.m G.n 1 G.Fw) f'

variable (p)

def inclW (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) : GL (Fin n) K →* GL (Fin n) (KQ p K r) :=
  GeneralLinearGroup.map (inclK p K r).toRingHom

def centK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) (γ : GL (Fin n) K) : Subgroup (GL (Fin n) K) :=
  Subgroup.centralizer {γ} ⊓ (Kres p K n 1).comap (inclW p K n 1)

def LMatch (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (φ : GL (Fin n) (KQ p K r) → ℂ)
    (f : GL (Fin n) (KQ p K 1) → ℂ) : Prop :=
  ∀ γ : GL (Fin n) K, (γ : Matrix (Fin n) (Fin n) K).charpoly.Separable →
    (∀ δ z : GL (Fin n) (KQ p K r), nrmRes p K n r δ = z⁻¹ * inclW p K n r γ * z →
      GlobalTheory.LKCount.orbC (sigRes p K n r) (Kres p K n r)
                   ((centK p K n γ).map ((MulAut.conj z⁻¹).toMonoidHom.comp (inclW p K n r))) δ φ =
        GlobalTheory.LKCount.orbC (sigRes p K n 1) (Kres p K n 1) ((centK p K n γ).map (inclW p K n 1))
          (inclW p K n 1 γ) f) ∧
    ((¬ ∃ δ z : GL (Fin n) (KQ p K r), nrmRes p K n r δ = z⁻¹ * inclW p K n r γ * z) →
      GlobalTheory.LKCount.orbC (sigRes p K n 1) (Kres p K n 1) ((centK p K n γ).map (inclW p K n 1))
        (inclW p K n 1 γ) f = 0)

def phiW (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r c : ℕ) (δ : GL (Fin n) (KQ p K r)) : ℂ :=
  if (∀ i j, (δ⁻¹).val i j ∈ intKQ p K r) ∧ ‖Algebra.norm ℚ_[p] δ.val.det‖ = (p : ℝ) ^ (r * c) ∧
      (c = 1 → 1 < ‖GlobalTheory.LKGeo.mulKQ K r ((sigKQ p K r)^[r - 1] δ.val.det)‖) then 1 else 0

def phiS (r : ℕ) (δ : GL (Fin 1) (Qr p r)) : ℂ := if GlobalTheory.LKLoc.KotInv p (Q0 p) 1 r δ (-1) then 1 else 0

def fS (r : ℕ) (g : GL (Fin 1) (Qr p 1)) : ℂ := if GlobalTheory.LKLoc.KotInv p (Q0 p) 1 1 g (-(r : ℤ)) then 1 else 0

def latO (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) : AddSubgroup (Fin n → KQ p K 1) :=
  AddSubgroup.pi Set.univ fun _ => (intKQ p K 1).toAddSubgroup

def rhoD (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) (h : Matrix (Fin n) (Fin n) (KQ p K 1)) : ℕ :=
  Nat.log (ReciprocityTheory.DiscreteGroups.LocalClassField.qK p K)
    (((latO p K n).map (Matrix.mulVecLin h).toAddMonoidHom ⊔
      (latO p K n).map (DistribMulAction.toAddMonoidHom (Fin n → KQ p K 1)
        (inclK p K 1 ((GlobalTheory.LKLoc.unif p K : Kˣ) : K)))).relIndex (latO p K n))

def fW (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r c : ℕ) (g : GL (Fin n) (KQ p K 1)) : ℂ :=
  if c = 0 then (if g ∈ Kres p K n 1 then 1 else 0)
  else if (∀ i j, (g⁻¹).val i j ∈ intKQ p K 1) ∧ ‖Algebra.norm ℚ_[p] g.val.det‖ = (p : ℝ) ^ r then
    ∏ i ∈ Finset.Ico 1 (rhoD p K n (g⁻¹).val), (1 - (ReciprocityTheory.DiscreteGroups.LocalClassField.qK p K : ℂ) ^ i)
  else 0

end GlobalTheory.BCFL
