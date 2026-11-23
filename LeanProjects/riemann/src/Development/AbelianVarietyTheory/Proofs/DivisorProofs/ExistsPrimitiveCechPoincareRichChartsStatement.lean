import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveCechPoincareRichCharts
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_cech_poincare_rich_charts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (a : ∀ k k', K.le 0 k' k → Hol (K.W k')) (ω : ∀ k, Fin g → Hol (K.W k)), (∀ k k' k'' (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k), a k k'' e'' = sh e' (a k k' e) + a k' k'' e') → (∀ k i j, dw i (ω k j) = dw j (ω k i)) → (∀ k k' (e : K.le 0 k' k) i, ω k' i - sh e (ω k i) = dw i (a k k' e)) → ∃ G : ∀ k, Hol (K.W k), (∀ k i, dw i (G k) = ω k i) ∧ ∀ k k' (e : K.le 0 k' k), a k k' e = G k' - sh e (G k) := by
  first | exact @GlobalTheory.AnPer.Charts.exists_primitive_of_rich | exact GlobalTheory.AnPer.Charts.exists_primitive_of_rich | (intros; apply GlobalTheory.AnPer.Charts.exists_primitive_of_rich <;> assumption)
