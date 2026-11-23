import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverRegularisingFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_regularising_functions : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (p : ℕ), p.Prime → ∀ (κ σ : Type) [Fintype κ] [Fintype σ] (f : V.X → κ → σ → V.X.functionField), (∀ x, Ov p x → (∀ i s, RegAt x (f x i s)) ∧ (∀ i, ∃ (s : σ) (a : ℕ), f x i s ≠ 0 ∧ RegAt x ((p : V.X.functionField) ^ a / f x i s)) ∧ ∀ᶠ z in 𝓝 x, Ov p z → ∀ i s, Lc (loc z) (f x i) (f z i s) ∧ Lc (loc z) (f z i) (f x i s)) → ∃ (V' : Cover Y) (π : V'.X ⟶ V.X) (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X), π ≫ V.p = V'.p ∧ Lies V' V π ∧ ∀ x, Ov p x → ∀ i, ∃ η, Gen (loc x) (fun s => SmallSec.fnMap π hπ (f (π x) i s)) η := by
  first | exact @GlobalTheory.LatChain.exists_cover_gen_of_lc | exact GlobalTheory.LatChain.exists_cover_gen_of_lc | (intros; apply GlobalTheory.LatChain.exists_cover_gen_of_lc <;> assumption)
