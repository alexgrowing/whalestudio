import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_regular_adapted_local : ∀ {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {s : W ⟶ Sp F} {jB : W ⟶ X} {d : ℕ},
    IsArithVar q d → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPullback jB s q (spMap (algebraMap (𝓞 F) F)) →
    ∀ {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ} (V : X.Opens), IsAffineOpen V → ∀ x₀ ∈ V,
    ∀ A : Matrix (Fin g) κ Γ(W, jB ⁻¹ᵁ V),
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
      (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X), xg ≫ s = spMap (algebraMap F (AlgebraicClosure F)) →
      spMap ε.O.subtype ≫ xt = xg ≫ jB → ⊤ ≤ xt ⁻¹ᵁ V → ∀ hx : ⊤ ≤ xg ⁻¹ᵁ (jB ⁻¹ᵁ V),
      haveI : Fact (resP v).Prime := ⟨hp⟩
      IntAdapted bl (A.map ((ioOf (resP v) ε).comp (TangentOrigin.evalPt xg (jB ⁻¹ᵁ V) hx)))) →
    ∃ (V' : X.Opens) (hV' : V' ≤ V), x₀ ∈ V' ∧ Function.Injective (jB.app V') ∧
      ∃ (C : Matrix (Fin g) κ Γ(X, V')) (C' : Matrix κ (Fin g) Γ(X, V')) (Q : Matrix κ κ Γ(W, jB ⁻¹ᵁ V')),
        C * C' = 1 ∧ C' * C = 1 ∧ BlockUni bl Q ∧ C.map (jB.app V') = A.map (resG W (jB.preimage_mono hV')) * Q := by
  first | exact @GlobalTheory.LieFilt.exists_regular_blockUni_change | exact GlobalTheory.LieFilt.exists_regular_blockUni_change | (intros; apply GlobalTheory.LieFilt.exists_regular_blockUni_change <;> assumption)
