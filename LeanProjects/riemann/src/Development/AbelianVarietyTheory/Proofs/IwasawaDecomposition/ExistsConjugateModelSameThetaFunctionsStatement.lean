import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateModelSameThetaFunctions
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugateModel_same_thetaFunctions : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ (q0 : ℕ) (hq : X.p0 + q0 = r), ∃ (X' : Data D.host.E T.rank) (m : GlobalTheory.Ker.Match S T X') (hq' : X'.p0 + X.p0 = T.rank) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin T.rank) (hs : IsSympl X' bas') (π : Equiv.Perm (Fin T.rank)), X'.Λ = latW hr X.Λ ∧ (∀ u v : Fin T.rank → D.host.E, EF X' u v = EF X (u ∘ Fin.cast hr.symm) (v ∘ Fin.cast hr.symm)) ∧ (∀ (y : Matrix (Fin S.rank) (Fin r) D.host.E) (φ : TF S.rank g), heisG X' bas' (y.submatrix id (Fin.cast hr)) φ = heisG X bas y φ) ∧ ∀ Z : Fam T, (IsONeg T X.p0 Z ↔ (ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).IsB (fun ρ => (Z ρ).submatrix id π)) ∧ (IsONeg T X.p0 Z → (ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).sB (fun ρ => (Z ρ).submatrix id π) = cartZ T X.p0 Z ∧ (∀ (φ : TF S.rank g) (f : WO S T → ℂ), (ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).IsZak ((ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).xB (fun ρ => (Z ρ).submatrix id π)) φ f ↔ Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f) ∧ ∀ (φ : TF S.rank g) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), thP X' hq' bas' idx' φ ((ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).toH (MvPolynomial.rename (fun v => (v.1, π.symm v.2.1, v.2.2)) Q)) ((ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs).xB (fun ρ => (Z ρ).submatrix id π)) = thP X hq bas idx φ (toP S hr eT hq Q) (frOf hr eT Z)) := by
  first | exact @GlobalTheory.OneMapRef.Flip.exists_flip_model | exact GlobalTheory.OneMapRef.Flip.exists_flip_model | (intros; apply GlobalTheory.OneMapRef.Flip.exists_flip_model <;> assumption)
