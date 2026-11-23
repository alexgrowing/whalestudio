import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDeRhamFlagStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineModelTrueOfFalseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelWithRatioStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasRatioOfHasDRGaloisStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.HTLine

theorem exists_lineModel_hodgeTate : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (i : Idx H p) (n : ℕ), i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → p ^ n ∣ i.l.A → 1 + 1 / ((p : ℝ) - 1) < n → ∀ st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧ (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z true st x) := by
  intro hB E _ _ _ hG H Dw Xo p W Y i₀ hp hW hY i n hd hF hpn hn st x hx
  obtain ⟨Z₀, rfl, hty, hL⟩ := GlobalTheory.T.local_system_model_exists E H Dw Xo p W Y i₀ hp hW hY i hd hF st x hx
  obtain ⟨Z₁, h₁, hDR, ⟨f₁, hf₁⟩, -⟩ := GlobalTheory.T.exists_de_rham_flag E H Dw Xo p W hp hW Y i₀ Z₀ (fun σ => by rw [hty])
  have hn1 : 1 ≤ n := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h3 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    have h4 : (1 : ℝ) < n := by linarith
    exact_mod_cast h4.le
  have full₀ : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z₀.ty τ := fun τ k hk => by
    rw [hty]; exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  have full₁ : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z₁.ty τ := fun τ k hk => by
    rw [hDR.1]; exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  have hR := GlobalTheory.T.hasRatio_of_hasDR_galois hB E H Dw Xo p W Y i₀ hp hW hG Z₁ hDR (h₁ ▸ (dvd_pow_self p (by omega)).trans hpn) st x hx
  obtain ⟨Z₂, f₂, h₂, hty₂, hf₂, hP⟩ := GlobalTheory.T.exists_model_with_ratio hB E H Dw Xo p W Y i₀ hp hW hY.1 Z₁ st x hx full₁ hR
  have hL₁ := GlobalTheory.T.local_system_model_map hB E H Dw Xo p W Y i₀ hp hW hY Z₀ Z₁ f₁ hf₁ full₀ false st x hx hL
  have hL₂ := GlobalTheory.T.local_system_model_map hB E H Dw Xo p W Y i₀ hp hW hY Z₁ Z₂ f₂ hf₂ full₁ false st x hx hL₁
  exact ⟨Z₂, h₂.trans h₁, hty₂.trans (funext hDR.1), GlobalTheory.T.lineModel_true_of_false E H Dw Xo p W Y i₀ hp hW Z₂ st x hP hL₂⟩

end GlobalTheory.HTLine
