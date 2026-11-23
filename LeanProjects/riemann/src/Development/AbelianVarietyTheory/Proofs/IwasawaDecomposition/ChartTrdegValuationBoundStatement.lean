import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTrdegValuationBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapResMap
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.FlagGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_trdeg_valuation_bound : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
    (Z : Mdl Y i₀) (a : Fin Z.m) (x : Sp Γ(Z.X, (Z.U a).1)),
    (∀ x' : Sp Γ(Z.X, (Z.U a).1), (Z.chart a ≫ Z.π) x' = (Z.chart a ≫ Z.π) x → x' ⤳ x → x' = x) →
    ∀ (Ω : Type) [Field Ω] (R : ValuationSubring Ω) (ι : (Sp Γ(Z.X, (Z.U a).1)).residueField x →+* R)
      (v : Vecs Dw (Y Z.i).t R),
    GlobalTheory.LocM.IsFrame (Y Z.i).t ((ι.comp (resMap x)).comp (Z.alg a)) (spMap (ι.comp (resMap x)) ≫ Z.chart a ≫ Z.π) v →
    GlobalTheory.LocM.SameFlag Z.ty (Y Z.i).t (spMap ((IsLocalRing.residue R).comp (ι.comp (resMap x))) ≫ Z.chart a ≫ Z.π)
      ((Z.fr a).bc ((IsLocalRing.residue R).comp (ι.comp (resMap x)))) (v.bc (IsLocalRing.residue R)) →
    ∃ σ : (Sp Γ(Z.X, (Z.U a).1)).residueField x →+* Ω,
      σ.comp ((Z.chart a ≫ Z.π).residueFieldMap x).hom = (R.subtype.comp ι).comp ((Z.chart a ≫ Z.π).residueFieldMap x).hom ∧
      σ.comp ((resMap x).comp (Z.alg a)) = (R.subtype.comp ι).comp ((resMap x).comp (Z.alg a)) ∧
      GlobalTheory.LocM.SameFlag Z.ty (Y Z.i).t (spMap ((R.subtype.comp ι).comp (resMap x)) ≫ Z.chart a ≫ Z.π)
        ((Z.fr a).bc (σ.comp (resMap x))) (v.bc R.subtype) := by
  first | exact @GlobalTheory.FlagGen.exists_embedding_of_specialisation | exact GlobalTheory.FlagGen.exists_embedding_of_specialisation | (intros; apply GlobalTheory.FlagGen.exists_embedding_of_specialisation <;> assumption)
