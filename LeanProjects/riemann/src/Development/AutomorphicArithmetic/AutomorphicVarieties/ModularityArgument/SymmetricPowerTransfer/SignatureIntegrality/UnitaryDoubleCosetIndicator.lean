import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.Wcount
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure Lev where
  c : ℕ
  H : Subgroup kˣ
  le : Uc k (c + 1) ≤ H
  H_le : H ≤ Uo k

theorem Uc_le_Uo (c : ℕ) : Uc k c ≤ Uo k := by
  rintro _ ⟨u, -, rfl⟩
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit

def Lev.iw : Lev k := ⟨0, Uo k, Uc_le_Uo k 1, le_rfl⟩

def Lev.deep (c : ℕ) : Lev k := ⟨c, Uc k (c + 1), le_rfl, Uc_le_Uo k _⟩

variable {k}

abbrev dg {n : ℕ} (d : Fin n → kˣ) : GL (Fin n) k := diagT k (Fin n) d

def SDom {n : ℕ} (d : Fin n → kˣ) : Prop := ∀ i j, i < j → valuation k (d i : k) < valuation k (d j : k)

namespace Lev

variable (V : Lev k)

def TH (n : ℕ) : Subgroup (GL (Fin n) k) := (Subgroup.pi Set.univ fun _ : Fin n => V.H).map (diagT k (Fin n))

def J (n : ℕ) : Subgroup (GL (Fin n) k) := (glIwa k n).N ⊔ V.TH n ⊔ (glIwa k n).Nm V.c

def DC {n : ℕ} (d : Fin n → kˣ) : Set (GL (Fin n) k) := {g | ∃ a ∈ V.J n, ∃ b ∈ V.J n, g = a * dg d * b}

def H2 : Subgroup kˣ := V.H.comap (powMonoidHom 2)

def ZJ (n : ℕ) : Subgroup (GL (Fin n) k) := (GeneralLinearGroup.scalar (Fin n) : kˣ →* GL (Fin n) k).range ⊔ V.J n

def IsSigns (R : Finset kˣ) : Prop := (∀ e ∈ R, e ∈ V.H2) ∧ ∀ u ∈ V.H2, ∃! e, e ∈ R ∧ u / e ∈ V.H

def IsSqReps (R : Finset kˣ) : Prop :=
  (∀ y ∈ R, valuation k (unif k : k) ≤ valuation k (y : k) ∧ valuation k (y : k) ≤ 1) ∧
    ∀ u : kˣ, ∃! y, y ∈ R ∧ ∃ s : kˣ, u / (y * s ^ 2) ∈ V.H

end Lev

variable (k) in

abbrev th (n : ℕ) : GL (Fin n) k →* GL (Fin n) k := GlobalTheory.CuspRep.invT n k

variable (k) in

def Phi : GL (Fin 3) k := ⟨!![0, 0, 1; 0, -1, 0; 1, 0, 0], !![0, 0, 1; 0, -1, 0; 1, 0, 0],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

variable (k) in

def th' : GL (Fin 3) k →* GL (Fin 3) k := (MulAut.conj (Phi k)).toMonoidHom.comp (th k 3)

namespace Lev

variable (V : Lev k)

open Classical in

def unitaryDoubleCosetIndicator (d : Fin 3 → kˣ) (g : GL (Fin 3) k) : ℂ := if g * (Phi k)⁻¹ ∈ V.DC d then 1 else 0

def fG (ω : kˣ →* ℂˣ) (Rs Ry : Finset kˣ) (x z : kˣ) (g : GL (Fin 3) k) : ℂ :=
  ∑ e ∈ Rs, ∑ y ∈ Ry, (ω e : ℂ) * V.unitaryDoubleCosetIndicator ![x * e, y, z] g

open Classical in

def fZ (ω : kˣ →* ℂˣ) {n : ℕ} (d : Fin n → kˣ) (g : GL (Fin n) k) : ℂ :=
  if h : ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * g ∈ V.DC d then (((ω h.choose)⁻¹ : ℂˣ) : ℂ) else 0

def fS (ω : kˣ →* ℂˣ) (t : kˣ) : GL (Fin 2) k → ℂ := V.fZ ω ![t, t⁻¹]

def fK (ω ω' : kˣ →* ℂˣ) (Rs : Finset kˣ) (t : kˣ) (g : GL (Fin 2) k) : ℂ := ∑ e ∈ Rs, (ω e : ℂ) * V.fZ ω' ![t * e, 1] g

open Classical in

def val (ω : kˣ →* ℂˣ) (t a : kˣ) : ℂ := if a / t ∈ V.H2 then (V.H.relIndex (Uo k) : ℂ) * (ω (a / t) : ℂ) else 0

end Lev

structure Cone (t x z : kˣ) : Prop where
  eq : x / z = t
  x_lt : valuation k (x : k) < valuation k (unif k : k)
  z_gt : 1 < valuation k (z : k)

structure Pres (V : Lev k) {n : ℕ} (σ : GL (Fin n) k →* GL (Fin n) k) : Prop where
  cont : Continuous σ
  invol : ∀ g, σ (σ g) = g
  N : ∀ g ∈ (glIwa k n).N, σ g ∈ (glIwa k n).N
  T : ∀ g ∈ V.TH n, σ g ∈ V.TH n
  Nm : ∀ c, ∀ g ∈ (glIwa k n).Nm c, σ g ∈ (glIwa k n).Nm c
  K : ∀ c, ∀ g ∈ Kc k n c, σ g ∈ Kc k n c

theorem pres_id (V : Lev k) (n : ℕ) : Pres V (MonoidHom.id (GL (Fin n) k)) :=
  ⟨continuous_id, fun _ => rfl, fun _ h => h, fun _ h => h, fun _ _ h => h, fun _ _ h => h⟩

end UpperTheory.V.Z.Sym.Sig

end
