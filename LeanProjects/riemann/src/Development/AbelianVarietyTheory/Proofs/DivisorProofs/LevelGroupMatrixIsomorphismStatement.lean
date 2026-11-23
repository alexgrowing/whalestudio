import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupMatrixIsomorphism
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_group_matrix_isomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl E)), l.Mb = ∏ w ∈ Pg, w.asIdeal → ∀ (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (r : ℕ) (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)), ∃ ψ : Formalism.L2.DIV.G0 Pg r ≃* LevelLiftConditions.LevGrp Dw l, (∀ (g : Formalism.L2.DIV.G0 Pg r) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb)), (∀ q, φ (ψ g q) = Y.mulVec (φ q)) ↔ ∀ w : ↥Pg, Y.map (Ideal.Quotient.factor (hle w)) = (g w).1) ∧ ∀ (g : Formalism.L2.DIV.G0 Pg r) (w : ↥Pg), Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom (LevelLiftConditions.levDet Dw l (ψ g)) = Matrix.GeneralLinearGroup.det (g w) := by
  first | exact @GlobalTheory.GeoActCompare.exists_levGrp_equiv_pi | exact GlobalTheory.GeoActCompare.exists_levGrp_equiv_pi | (intros; apply GlobalTheory.GeoActCompare.exists_levGrp_equiv_pi <;> assumption)
