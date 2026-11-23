import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

theorem UpperTheory.lie_combinations_independent_under_iso :
    ∀ (K : Type) [Field K] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] [IsCommMonObj A] [IsCommMonObj A'] (e : A ≅ A'), IsMonHom e.hom → ∀ (g m : ℕ) (b : Fin g → (epsR K ⟶ A)) (u : Fin m → Fin g → K) (w : Fin m → (epsR K ⟶ A)), IsLieBasis b → LinearIndependent K u → (∀ i, IsLieComb (u i) b (w i)) → Indep (fun i => w i ≫ e.hom) := by
  intro K _ A A' _ _ _ _ e he g m b u w hb hu hw
  have tw : ∀ i, IsTangent (w i) := fun i =>
    (GlobalTheory.LieComb.lieComb_algebra K A g b hb.1).2.1 _ _ (hw i)
  refine ⟨fun i => GlobalTheory.CM.DiffCoord.isTangent_comp_hom e.hom (tw i), fun c c' z h h' => ?_⟩
  have key : ∀ c, IsLieComb c (fun i => w i ≫ e.hom) z → IsLieComb (Matrix.vecMul c (Matrix.of u)) b (z ≫ e.inv) := by
    intro c h
    have h1 := GlobalTheory.CM.DiffCoord.isLieComb_comp_hom e.inv h
    simp only [Category.assoc, e.hom_inv_id, Category.comp_id] at h1
    exact (comb_comb (P := Matrix.of u) hb.1 hw c _).1 h1
  exact (Matrix.vecMul_injective_iff (M := Matrix.of u)).2 hu
    ((Indep.of_basis hb).2 _ _ _ (key c h) (key c' h'))
