import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulPowApp
import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RedQuot

open Coalgebra Bialgebra

theorem semi_app_mulP {p : ℕ} {R R₀ : Type} [CommRing R] [CommRing R₀] {σ : R →+* R₀}
    {G : PDivGroup p R} {G₀ : PDivGroup p R₀} (s : SemiHom σ G₀ G) (n : ℕ) (a : G.A n) :
    s.app (n + 1) (G.mulP n a) = G₀.mulP n (s.app n a) := by
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [mulP_res, semi_mulBy, ← s.res_app, mulP_res]

theorem cancel (p : ℕ) [Fact p.Prime] (R R₀ : Type) [CommRing R] [CommRing R₀] [Algebra R R₀]
    (G' G : PDivGroup p R) (G₀ : PDivGroup p R₀) (s : SemiHom (algebraMap R R₀) G₀ G)
    (s' : SemiHom (algebraMap R R₀) G₀ G') (ψ : G ⟶ G') (χ : G' ⟶ G) (m N d e : ℕ)
    (hNe : N + e = m + d)
    (h1 : ∀ n a, s.app n (ψ.app n a) = s'.app n (Hom.app (((p : ℤ_[p]) ^ m) • 𝟙 G') n a))
    (h2 : ψ ≫ χ = ((p : ℤ_[p]) ^ N) • 𝟙 G) (n : ℕ) (a : G.A n) :
    s'.app n (χ.app n (Hom.app (((p : ℤ_[p]) ^ e) • 𝟙 G) n a)) =
      s.app n (Hom.app (((p : ℤ_[p]) ^ d) • 𝟙 G) n a) := by
  rw [smul_pow_app, smul_pow_app]

  let X : ∀ n, G.A n → G₀.A n := fun n a => s'.app n (χ.app n (mulBy R (G.A n) (p ^ e) a))
  let Y : ∀ n, G.A n → G₀.A n := fun n a => s.app n (mulBy R (G.A n) (p ^ d) a)
  have hX : ∀ n z, X (n + 1) (G.mulP n z) = G₀.mulP n (X n z) := fun n z => by
    simp only [X]
    rw [← map_mulBy (G.mulP n), app_mulP, semi_app_mulP]
  have hY : ∀ n z, Y (n + 1) (G.mulP n z) = G₀.mulP n (Y n z) := fun n z => by
    simp only [Y]
    rw [← map_mulBy (G.mulP n), semi_app_mulP]

  have base : ∀ n b, X n (mulBy R (G.A n) (p ^ m) b) = Y n (mulBy R (G.A n) (p ^ m) b) := by
    intro n b
    have h := ident s s' ψ χ m N h1 h2 n (mulBy R (G.A n) (p ^ e) b)
    simp only [X, Y]
    rw [mulBy_mulBy, ← pow_add, hNe, pow_add, mul_comm, ← mulBy_mulBy] at h
    rw [h, ← semi_mulBy (s'.app n), ← map_mulBy (χ.app n), mulBy_mulBy, mulBy_mulBy, mul_comm]

  have step : ∀ k, (∀ n b, X n (mulBy R (G.A n) (p ^ (k + 1)) b) =
      Y n (mulBy R (G.A n) (p ^ (k + 1)) b)) →
      ∀ n b, X n (mulBy R (G.A n) (p ^ k) b) = Y n (mulBy R (G.A n) (p ^ k) b) := by
    intro k hk n b
    obtain ⟨c, rfl⟩ := G.res_surjective n b
    apply GlobalTheory.PDivGroup.Test.mulP_injective G₀ n
    have e1 : G.mulP n (mulBy R (G.A n) (p ^ k) (G.res n c)) =
        mulBy R (G.A (n + 1)) (p ^ (k + 1)) c := by
      rw [map_mulBy, mulP_res, mulBy_mulBy, ← pow_succ]
    rw [← hX, ← hY, e1, hk]
  have all : ∀ j, j ≤ m → ∀ n b, X n (mulBy R (G.A n) (p ^ (m - j)) b) =
      Y n (mulBy R (G.A n) (p ^ (m - j)) b) := by
    intro j
    induction j with
    | zero => intro _; simpa using base
    | succ j ih =>
      intro hj
      have h := ih (by omega)
      rw [show m - j = (m - (j + 1)) + 1 by omega] at h
      exact step _ h
  have e0 : ∀ k (z : G.A k), mulBy R (G.A k) 1 z = z := fun k z => by
    simp [mulBy]
  have h0 := all m le_rfl n a
  simp only [X, Y, Nat.sub_self, pow_zero, e0] at h0
  exact h0

end GlobalTheory.RedQuot
