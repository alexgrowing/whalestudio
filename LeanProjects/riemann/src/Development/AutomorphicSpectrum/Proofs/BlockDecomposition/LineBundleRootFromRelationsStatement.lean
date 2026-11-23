import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBundleRootFromRelations
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_root_from_relations : ∀ (X : Scheme.{0}) (Q : LB X), Q.IsLB → ∀ (k : ℕ), 1 ≤ k → ∀ (τ : Type) (u : (Fin k → τ) → LB.Sec Q), (∀ w₁ w₂ w₃ w₄ : Fin k → τ, (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c) → (⨆ i : τ, nonzeroLocus (u (fun _ => i)) = ⊤) → ∃ (A : LB X) (ω : LB.Iso (pw A (k : ℤ)) Q), A.IsLB ∧ ω.IsGen ∧ ∀ (Y : Scheme.{0}) (b : Y ⟶ X) (L : LB Y) (d D : ℤ) (hD : d * k = D) (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D)), L.IsLB → θ.IsGen → (∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) → LBIso (A.pull b) (pw L d) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese | exact GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese <;> assumption)
