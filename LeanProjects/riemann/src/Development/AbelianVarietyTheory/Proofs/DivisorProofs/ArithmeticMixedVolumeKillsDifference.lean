import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialEqProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAtOfLocalFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFlagRootSymbolsPrimeStatement

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
open MvPolynomial

open Formalism.BasicNotions.DV in

theorem GlobalTheory.TrivFlag.arIn_powerSum_mul_vertical (h2 : Hypotheses2) (hH : HypothesesH) {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j}
    {κ : Lv A} (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (hd : ∀ c, (Φ.C c).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N)
    (Sx : Finset ℕ) (R : ℝ) (hR : 2 ≤ R) (p : ℕ) (hp : p.Prime) (τ : D.what₂.Tau) (k : ℕ) (hk : 1 ≤ k)
    (y : Rt D.what₂.Tau N) (g : MvPolynomial (Vm D.what₂.Tau N) ℝ) :
    (arIn s Φ (metsOf x Φ)).arMix Sx R p
      (tagHT D.what₂.Tau _ (pk D _ τ k) * ((X (Sum.inl (false, y)) - X (Sum.inl (true, y))) * g)) = 0 := by
  rw [ArIn.arMix, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  let ι : Type := (Bool × Rt D.what₂.Tau N) ⊕ (Bool × (Fin (D.R.f * N) ⊕ Fin (D.R.f * N)))
  let a : Bool → ℕ → Bool := fun b => Function.update (ArIn.ind Sx) p b
  let w : ι → Sym D.host.E →₀ ℤ := Sum.elim (fun q => rootSym S.Dw (a q.1) (some R) (tauEmb D q.2.1) q.2.2)
    fun q => wholeSym (a q.1) (some R) q.2
  have ha (b : Bool) : {q | a b q = true}.Finite := (insert p Sx).finite_toSet.subset fun q hq => by
    by_cases e : q = p
    · simp [e]
    · simpa [a, ArIn.ind, e] using hq
  obtain ⟨M, L, m, Ψ, hI, hΨ, hnum⟩ := (GlobalTheory.ArTopTrue.arTop_true h2.p4 hH.deg HTBound.htBound D _ _ _ _ _ s x Φ c R hR).2
    ι w fun i b hb => by
      rcases i with q | q
      · obtain ⟨e₁, e₂⟩ := mem_support_rootSym hb
        exact ⟨e₁ ▸ ha _, e₂⟩
      · obtain ⟨e₁, e₂⟩ := mem_support_wholeSym hb
        exact ⟨e₁ ▸ ha _, e₂⟩
  let ev : MvPolynomial (Vm D.what₂.Tau N) ℝ →ₐ[ℝ] MvPolynomial ι ℝ := aeval fun v => match v with
    | Sum.inl q => X (Sum.inl q)
    | Sum.inr (b, k) => C ((k.factorial : ℝ)⁻¹) * ∑ l, X (Sum.inr (b, l)) ^ k
  have hev : (arIn s Φ (metsOf x Φ)).mixEv Sx R p c = (rename w).comp ev := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rcases v with ⟨b, z⟩ | ⟨b, k⟩
    · refine (aeval_X _ _).trans (Eq.symm ?_)
      change rename w (ev (X (Sum.inl (b, z)))) = X (w (Sum.inl (b, z)))
      simp only [ev, aeval_X, rename_X]
    · refine (aeval_X _ _).trans (Eq.symm ?_)
      change rename w (ev (X (Sum.inr (b, k)))) =
        (C ((k.factorial : ℝ)⁻¹) : MvPolynomial (Sym D.host.E →₀ ℤ) ℝ) * ∑ l, X (w (Sum.inr (b, l))) ^ k
      simp only [ev, aeval_X, rename_X, map_mul, rename_C, map_sum, map_pow]
      rfl
  change numL _ _ ((arIn s Φ (metsOf x Φ)).mixEv Sx R p c _) = 0
  rw [hev, ← hd c]
  refine (numL_rename w _ _ Ψ _ hΨ.2 hnum _).trans (div_eq_zero_iff.2 (.inl ?_))
  have key := powerSum_mul_vertical h2 M _ L m Ψ hI hΨ p hp (fun i : Fin N => (Sum.inl (true, (τ, i)) : ι))
    (GlobalTheory.T.flag_at_of_local_flag _ _ _ _ _ p hp (GlobalTheory.T.local_flag_root_symbols_prime h2 hH D _ _ _ _ _ s Φ c _ p hp (a true) (by simp [a]) (some R) τ))
    (Sum.inl (false, y)) (Sum.inl (true, y))
    (adlOf_rootSym_eq _ _ _ _ _ _ _) _
    (add_nonneg (div_nonneg zero_le_one (sub_nonneg.2 (by exact_mod_cast hp.one_le))) (by unfold vDiff; positivity))
    (abs_lgOf_update_sub_le _ _ p _ _ _) k hk (ev g)
  rw [← key]
  congr 1
  simp [ev, tagHT, pk]

open Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.Mean4 Formalism.BasicNotions.DV in

theorem GlobalTheory.TrivFlag.arMix_powerSum_mul_vertical : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ (p : ℕ), p.Prime → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ (y : Rt D.what₂.Tau O.Y.N) (g : MvPolynomial (Vm D.what₂.Tau O.Y.N) ℝ), O.Y.arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) * ((X (Sum.inl (false, y)) - X (Sum.inl (true, y))) * g)) = 0 := by
  intro h2 hH D O hO Sx R hR p hp τ k hk y g
  obtain ⟨x, P, h⟩ := hO
  change (arIn O.s O.Φ O.met.hm).arMix Sx R p _ = 0
  rw [h.hm_eq]
  exact arIn_powerSum_mul_vertical h2 hH O.s x O.Φ O.dim_eq Sx R hR p hp τ k hk y g
