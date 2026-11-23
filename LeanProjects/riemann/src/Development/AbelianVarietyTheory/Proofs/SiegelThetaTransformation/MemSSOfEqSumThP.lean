import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExpansionOfRowHighest

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.Dict.CuspSum

theorem mem_SS_of_eq_sum_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → ∀ (J : Type) [Fintype J] (φ : J → TF n g) (P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), (∀ j, IsSB (φ j)) → (∀ j, P j ∈ Harm.rowHighest ℂ k k') → ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = ∑ j, thP X hr bas idx (φ j) (P j) x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk J _ φ P hφ hP Q hQ hΓ
  choose m a b t h using fun j =>
    (GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn).2 (φ j) (hφ j)
  have hQ' : ∀ x ∈ X.dom, Q x = ∑ p ∈ (Finset.univ : Finset (Σ j : J, Fin (m j))), t p.1 p.2 *
      thFr X hr bas idx n (fun k i => (a p.1 p.2 k i : ℝ)) (fun k i => (b p.1 p.2 k i : ℝ)) (P p.1) x := by
    intro x hx
    rw [hQ x hx, Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun j _ => h j (P j) x hx
  rcases hk with ⟨τ, hτ⟩ | h0
  · exact CuspAny.mem_SS_of_eq_sum_thFr idx hr _ _ _ _ hs hn ⟨τ, Or.inl hτ⟩ (fun p _ => hP p.1) hQ' hΓ
  · exact ThFr.mem_SS_of_eq_sum_thFr idx hr _ _ _ _ hs hn
      (Or.inr (CuspClass.not_isIso_of_definite X (by omega))) (fun p _ => hP p.1) hQ' hΓ

end GlobalTheory.Dict.CuspSum
