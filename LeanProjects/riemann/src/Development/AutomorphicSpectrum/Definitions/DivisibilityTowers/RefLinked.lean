import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Top

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

structure RealTie (M : RootModel Ψ N) (S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))) (n : ℕ) where

  Re : PB.Realis S M.P
  δ_eq : M.δ = n * Re.deg
  fund_deg : ∀ τ i, (Re.ref (some (τ, i))).a = -∑ k ∈ Finset.Iic i, M.xdeg (τ, k)
  fund_reg : ∀ τ i t, 0 < t → t ≤ S.t₀ → ∀ z ∈ mcPts M.P,
    Real.log ((Re.line (some (τ, i)) t).h z) = -∑ k ∈ Finset.Iic i, Real.log ((M.x t (τ, k)).h z)
  ref_none : (Re.ref none).a = M.A.a ∧ ∀ z ∈ mcPts M.P, (Re.ref none).h z = M.A.h z
  phT_none : ∀ t x, S.phT none t x = 0

structure RealTower (T : RootTower Ψ N) where

  Sys : T.Comp → PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))

  n : T.Comp → ℕ

  tie : ∀ B c, RealTie (T.M B c) (Sys c) (n c)
  kA_eq : ∀ B B' c, (T.M B c).kA = (T.M B' c).kA

namespace RealTower

variable {T : RootTower Ψ N} (R : RealTower T)

def Smooth : Prop :=
  ∀ B c, (R.tie B c).Re.J = ⊤ ∧ ∃ _ : Algebra ℚ (T.M B c).Ω, SmoothGenericFibreM (T.M B c).y

def Flat : Prop :=
  ∀ c τ (i : Fin N), (i : ℕ) + 1 = N → ∀ t, IsPsh (R.Sys c).A (((R.Sys c).potT (some (τ, i)) t).rsmul (-1)) ∧
    IsPsh (R.Sys c).A ((R.Sys c).potT (some (τ, i)) t)

def Pos : Prop := ∀ c, IsPosPot (R.Sys c).A ((R.Sys c).th none)

def Unif : Prop := ∀ c, PB.IsUniformised (R.Sys c).A (R.Sys c).open' T.j fun p => (R.Sys c).potH (some p)

def Squares (II : IntersectionSystem) : Prop :=
  ∀ B c, ∃ (d : ℕ) (S : PB.AnSys (d + 1) (Ψ × Fin N)) (K : Type) (_ : Fintype K) (ι : K → Type)
    (_ : ∀ k, Fintype (ι k)) (P : Ideal (MRing ι)) (Re : PB.Realis S P), Nonempty (PB.FlagSys Re T.j) ∧
      PB.toWt (Re.PB II) = (R.tie B c).Re.PBwt II ∧ S.degPoly = ((R.Sys c).comap some).degPoly

def RefLinked (II : IntersectionSystem) : Prop :=
  ∃ (C : ℝ) (thH : ∀ c, LocPot (R.Sys c).X) (Pfix : T.Comp → RPA Ψ N), (∀ c, IsPotential (R.Sys c).A (thH c)) ∧
    ∀ B : ℕ, 2 ≤ B → ∀ c, ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (P : Ideal (MRing ι))
      (Re Re' : PB.Realis (R.Sys c) P) (S : Finset ℕ) (α : ℕ → ℝ) (H : HermLine ι),
      Re.PBs II = (R.tie B c).Re.PBs II ∧ Re'.PBs II = Pfix c ∧ Re'.deg = Re.deg ∧ (∀ p ∈ S, p.Prime ∧ 0 ≤ α p) ∧
      IsSmoothHerm H ∧ PB.SamePot Re.R.A Set.univ (potOf Re.R H) ((thH c).pullback Re.π Re.holo.1) ∧
      (∀ a t, 0 < t → t ≤ (R.Sys c).t₀ → PB.VertClose P S α (Re.line a t) (Re'.line a t)) ∧
      (∀ p ∈ S, PB.NefAt P p H.a ∧ ∀ a, PB.NefAt P p ((Re.ref a).a + H.a) ∧ PB.NefAt P p ((Re'.ref a).a + H.a)) ∧
      ∑ p ∈ S, α p * Real.log p ≤ C * Real.log B

end RealTower

end GlobalTheory.CompanionTheory.Ar.Top
