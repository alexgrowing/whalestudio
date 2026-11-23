import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtMulTriangular
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag
open IsDedekindDomain GlobalTheory.WholeFlag.Glue GlobalTheory.WholeFlag.GlueProof
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WholeFlag.GlueProof

theorem unitAt_minor_of_mem_chartOpen : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ), Hyp A p V W U H J d T L m r → ∀ (q : Idx ι L) (z : V.G), V.j z ∈ chartOpen V U H L m r q → ∀ (k : ℕ) (hk : k ≤ g), UnitAt z (minorAt (H q.1 * ((T (V.π z)).map V.φ)⁻¹) k hk (q.2.1 k)) := by
  intro F _ _ Y C g A p V W ι U H J d T L m r hyp q z hz k hk
  obtain ⟨-, -, -, -, hm, -, -, hT, hGd, hr, -, hreg, -⟩ := hyp
  obtain ⟨h1, h2, h3⟩ := hz
  refine (unitAt_minor_of_nmin V (H q.1) (frames r q.2.2) m hm k hk (q.2.1 k) (T (V.π z)) (d (V.π z))
    (fun i => genAt (A i).D (V.π z)) (hT _).1 (hT _).2 (hreg q.1 z h1) (fun i => V.unitAt_φ (hGd i _))
    (fun i => hr i (fun _ => q.2.2 i) z ?_)).2 ((unitAt_symm V).1 (h3 k hk))
  exact Set.mem_iInter.2 fun _ => h2 i

end GlobalTheory.WholeFlag.GlueProof
