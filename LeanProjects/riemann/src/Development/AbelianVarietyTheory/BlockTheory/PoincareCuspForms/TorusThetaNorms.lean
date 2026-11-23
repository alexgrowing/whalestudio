import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusThetaNorms

open NumberField Complex ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def riem (D : FD.Data E r) (v w : Fin r → E) : ℚ :=
  Algebra.trace ℚ E (-(D.κ0 / 2) * FD.herm D.Gm v w)

def Unimodular (D : FD.Data E r) : Prop :=
  (∀ v ∈ D.Λ, ∀ w ∈ D.Λ, ∃ k : ℤ, riem D v w = k) ∧
    ∀ φ : D.Λ →+ ℤ, ∃ v ∈ D.Λ, ∀ w : D.Λ, (φ w : ℚ) = riem D v (w : Fin r → E)

def embR (D : FD.Data E r) (v : Fin r → E) : D.Ψ → Fin r → ℂ := fun τ => FD.Data.emb τ.1 v

def IsAdaptedON (D : FD.Data E r) (x e : FD.Frame D.Ψ r) : Prop :=
  (∃ b ∈ FD.Bor D.Ψ r, e = FD.rmul x b) ∧
    ∀ (τ : D.Ψ) (a b : Fin r),
      (D.c τ : ℂ) * FD.hermC τ.1 D.Gm (FD.col (FD.mat e τ) a) (FD.col (FD.mat e τ) b) =
        if a = b then ((FD.sgn D.p0 a : ℝ) : ℂ) else 0

structure TorusAt (D : FD.Data E r) (w0 : 𝓞 E) (x : FD.Frame D.Ψ r) where

  X : I2.PT E
  rank_eq : X.r = r

  dim_mem : ∀ τ : D.Ψ, X.dim τ.1 = r - D.p0

  dim_conj : ∀ τ : D.Ψ, X.dim (ComplexEmbedding.conjugate τ.1) = D.p0

  e : FD.Frame D.Ψ r
  e_adapted : IsAdaptedON D x e

  φ : (D.Ψ → Fin r → ℂ) → I2.Vsp X.dim

  φ_mem : ∀ (w : D.Ψ → Fin r → ℂ) (τ : D.Ψ) (i : Fin (X.dim τ.1)) (a : Fin r),
    (a : ℕ) = D.p0 + i →
      φ w ⟨τ.1, i⟩ = -((D.c τ : ℂ) * FD.hermC τ.1 D.Gm (w τ) (FD.col (FD.mat e τ) a))

  φ_conj : ∀ (w : D.Ψ → Fin r → ℂ) (τ : D.Ψ)
    (i : Fin (X.dim (ComplexEmbedding.conjugate τ.1))) (a : Fin r),
    (a : ℕ) + i + 1 = D.p0 →
      φ w ⟨ComplexEmbedding.conjugate τ.1, i⟩ =
        conj ((D.c τ : ℂ) * FD.hermC τ.1 D.Gm (w τ) (FD.col (FD.mat e τ) a))

  lattice : ∀ y : I2.Vsp X.dim, y ∈ X.L ↔ ∃ v ∈ D.Λ, y = φ (embR D v)

  eps_eq : ∀ v ∈ D.Λ,
    (X.eps (φ (embR D v)) : ℝ) = Real.cos (Real.pi * (riem D v ((w0 : E) • v) : ℝ))

  s : (Fin 1 → I2.Vsp X.dim) → ℂ
  s_mem : s ∈ X.Sec 1 1
  s_ne : s ≠ 0
  s_gen : ∀ F ∈ X.Sec 1 1, ∃ z : ℂ, F = z • s

def TorusExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (D : FD.Data E r) (w0 : 𝓞 E),
    (w0 : E) + FD.cc (w0 : E) = 1 → Unimodular D → ∀ x ∈ D.dom, Nonempty (TorusAt D w0 x)

def TorusCompatible : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (D : FD.Data E r) (w0 : 𝓞 E)
    (x : FD.Frame D.Ψ r) (T : TorusAt D w0 x),
    (∀ (α : 𝓞 E) (v : Fin r → E), T.φ (embR D ((α : E) • v)) = I2.act α (T.φ (embR D v))) ∧
    (∀ v w : Fin r → E, (I2.Hf (T.φ (embR D v)) (T.φ (embR D w))).im = (riem D v w : ℝ)) ∧
    ∀ w : D.Ψ → Fin r → ℂ, (I2.Hf (T.φ w) (T.φ w)).re = ∑ τ, D.c τ * D.maj x τ (w τ)

def actL {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : I2.Vsp dim →ₗ[ℂ] I2.Vsp dim where
  toFun := I2.act α
  map_add' v w := by ext i; simp [I2.act, mul_add]
  map_smul' z v := by ext i; simp [I2.act, mul_left_comm]

namespace TorusAt

variable {D : FD.Data E r} {w0 : 𝓞 E} {x : FD.Frame D.Ψ r} (T : TorusAt D w0 x)

def sNorm : ℝ := Real.sqrt (T.X.l2 1 T.s)

def thetaVal {n : ℕ} (q : ℕ) (π : I2.Vsp T.X.dim →ₗ[ℂ] I2.Vsp T.X.dim)
    (P : MvPolynomial (I2.Letter n T.X.dim) ℂ) (b : Fin n → I2.Vsp T.X.dim) : ℂ :=
  I2.polyDeriv P I2.dir (T.X.U q b (I2.s0 T.X π T.s)) 0 / (T.sNorm : ℂ) ^ n

def IsThetaDatum {n : ℕ} (q : ℕ) (α : 𝓞 E) (d : ℕ) (P : MvPolynomial (I2.Letter n T.X.dim) ℂ)
    (y : Fin n → Fin r → E) : Prop :=
  1 ≤ q ∧ (α : E) * FD.cc (α : E) = q ∧ P.IsHomogeneous d ∧ ∀ k, FD.cc (α : E) • y k ∈ D.Λ

def thetaNorm {n : ℕ} (q : ℕ) (α : 𝓞 E) (d : ℕ) (P : MvPolynomial (I2.Letter n T.X.dim) ℂ)
    (y : Fin n → Fin r → E) : ℝ :=
  Real.pi ^ (-(d : ℝ) / 2) * ‖T.thetaVal q (actL α) P fun k => -T.φ (embR D (y k))‖

theorem exists_col_mem (τ : D.Ψ) (i : Fin (T.X.dim τ.1)) : ∃ a : Fin r, (a : ℕ) = D.p0 + i := by
  have h1 := T.dim_mem τ
  have h2 := i.isLt
  exact ⟨⟨D.p0 + i, by omega⟩, rfl⟩

theorem exists_col_conj (τ : D.Ψ) (i : Fin (T.X.dim (ComplexEmbedding.conjugate τ.1))) :
    ∃ a : Fin r, (a : ℕ) + i + 1 = D.p0 := by
  have h1 := T.dim_conj τ
  have h2 := i.isLt
  have h3 := D.p0_le
  exact ⟨⟨D.p0 - 1 - i, by omega⟩, by simp only; omega⟩

end TorusAt

end

end GlobalTheory.IndefiniteRowSideFullHecke.TorusThetaNorms
