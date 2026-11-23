import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

attribute [local instance] Over.cartesianMonoidalCategory

theorem isEigBasis_of_mul_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {K : Type} [CommRing K] (φ : c.F →+* K) (y : Sp K ⟶ Z.X) (τ : E →+* ℂ) {m : ℕ} (u w : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)) (P Q : Matrix (Fin m) (Fin m) K), IsEigBasis Z φ y τ u → (∀ a, IsCombAtG Z.t y u (fun b => P a b) (w a)) → Q * P = 1 → IsEigBasis Z φ y τ w := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z K _ φ y τ m u w P Q hu hw hQP
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have ht : ∀ j, IsTanAtG Z.t y (u j) := fun j => (hu.1 j).1
  have hwt : ∀ j, IsTanAtG Z.t y (w j) := fun j => Guard.comb_tan ht (hw j)
  have hw' : ∀ a, IsCombAtG Z.t y u (fun b => P.transpose b a) (w a) := hw
  refine ⟨fun i => ⟨hwt i, fun a => ?_⟩, fun v hv => ?_⟩
  · rw [← (Formalism.L2.Pj.isCombAtG_iff Z.t _ (fun j => Formalism.L2.Pj.ovT (ht j)) _ _).1 (hw i)]
    have := Z.t.act.hom a
    exact congrArg (fun f => f.left) (Formalism.L2.Pj.combT_eig _ (fun j => Formalism.L2.Pj.ovT (ht j)) (Z.t.act.act a) _
      (fun j => Over.OverMorphism.ext ((hu.1 j).2 a)) _)
  · obtain ⟨b, hb, hb'⟩ := hu.2 v hv
    refine ⟨Q.transpose.mulVec b, ?_, fun d hd => ?_⟩
    · obtain ⟨v', -, h2⟩ := Guard.exists_comb hwt (Q.transpose.mulVec b)
      have h3 := Formalism.L2.Pj.tanLinG u ht w P.transpose _ v' hw' h2
      rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hQP, Matrix.transpose_one, Matrix.one_mulVec] at h3
      exact Guard.comb_unique ht h3 hb ▸ h2
    · rw [← hb' _ (Formalism.L2.Pj.tanLinG u ht w P.transpose d v hw' hd), Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hPQ,
        Matrix.transpose_one, Matrix.one_mulVec]

end GlobalTheory.ArLieBase

end
