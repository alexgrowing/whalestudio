import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapResMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentCombinationEigenAction

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.FlagGen

namespace GlobalTheory.FlagGen

theorem det_uni_eq_one {R : Type} [CommRing R] {m : ℕ} (s : Low m → R) : (Matrix.of (uni s)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [uni]
  · intro i j hij
    have h : i < j := hij
    simp [uni, h.ne, not_lt.2 h.le]

theorem isFrame_uni : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {c : Coeff l} {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (g : c.F →+* R) (x0 : Sp R ⟶ X)
    (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t g x0 u → ∀ s : ∀ τ, Low (Dw.mult τ) → R, ∃ v : Vecs Dw t R,
      GlobalTheory.LocM.IsFrame t g x0 v ∧ ∀ τ i, IsCombAtG t x0 (u τ) (fun j => uni (s τ) j i) (v τ i) := by
  intro E _ _ _ H Dw l c X t R _ g x0 u hu s
  choose v hvt hvc using fun τ (i : Fin (Dw.mult τ)) =>
    GlobalTheory.FlagEmb.exists_comb t (fun j => (hu.1 τ j).1) (fun j => uni (s τ) j i)
  refine ⟨v, ⟨fun τ i => ⟨hvt τ i, fun a => ?_⟩, fun τ w hw hE => ?_⟩, hvc⟩
  · exact GlobalTheory.FlagEmb.eig_of_comb t _ _ _ a _ (fun j => ⟨(hu.1 τ j).1, (hu.1 τ j).2 a⟩) (hvc τ i)
  · exact GlobalTheory.FlagEmb.existsUnique_comb_change t (fun j => (hu.1 τ j).1) (Matrix.of (uni (s τ)))
      (by rw [det_uni_eq_one]; exact isUnit_one) (hvc τ) hw (hu.2 τ w hw hE)

end GlobalTheory.FlagGen
