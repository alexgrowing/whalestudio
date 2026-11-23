import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

namespace Formalism.BasicNotions

structure GatTies (D : D7) where

  gat_k : ∀ u w h, (D.gat u w h).P.m + 1 = D.R.k

  gat_n : ∀ u w h (v : Fin (D.gat u w h).P.nV) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})] (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P →
    (D.gat u w h).P.n' v = orderOf (D.host.galE σ).2

  gat_pos : ∀ u w h, (Σ v : Fin (D.gat u w h).P.nV, Fin ((D.gat u w h).P.n' v)) ≃ D.what₂.Tau

  gat_step : ∀ u w h (v : Fin (D.gat u w h).P.nV) (s : Fin ((D.gat u w h).P.n' v))
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P →
    ((D.eTau (gat_pos u w h ⟨v, posAdd s 1⟩) : D.R.Psi) : D.R.GG) =
      ((D.eTau (gat_pos u w h ⟨v, s⟩) : D.R.Psi) : D.R.GG) *
        D.host.galE σ * D.R.cc

  gat_lam : ∀ u w h (v : Fin (D.gat u w h).P.nV) (s : Fin ((D.gat u w h).P.n' v))
    (i : Fin ((D.gat u w h).P.m + 1)),
    (D.gat u w h).P.lam0 v s i =
      ((D.fm u).lam 0 (gat_pos u w h ⟨v, s⟩)).w
        ⟨i.1, by have h1 := gat_k u w h; have h2 := i.2; simp only [Ranks.N]; omega⟩

end Formalism.BasicNotions
