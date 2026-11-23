import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsEtaRuleExistsUniqueMemSec
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsBorelOrthonormalFlagFrameStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormEtaProductFormLeAtUnitFrameStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem etaRule_isSec_pnorm_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → AllTest Xo c → ∀ (R i N : ℕ), Odd R → 1 < R → Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i → 1 ≤ N → ∀ (J : Type) [Fintype J] (cf : J → ℤ) (xs : J → Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c), Fintype.card J ≤ R ^ (2 * I2.PT.f E * r ^ 2) → (∀ j, |cf j| ≤ N) → Spans xs → IsEtaRule Xo c R cf xs f → ∀ (DF q m : ℕ) (R0 : ℝ), RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → (∀ k, (U.X k).IsSec (laU U 0 (r * (2 * R ^ 4 * i)) k) (rdU U f k)) ∧ ∀ (k : U.Comp), ∀ x ∈ (U.X k).dom, (U.X k).pnorm (laU U 0 (r * (2 * R ^ 4 * i)) k) (rdU U f k) x ≤ Real.exp (-(i : ℝ) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) x - p16 E r q m R N)) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hT R i N hR hR1 hG hN J _ cf xs f hJ hcf hsp hf DF q m R0 hrun hm
  have hsec : f ∈ sec Xo c 0 (r * (2 * R ^ 4 * i)) := by
    rw [← hG]
    exact (GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR J r cf xs).2 f hf
  have hev : Even (r * (2 * R ^ 4 * i)) := ⟨r * (R ^ 4 * i), by ring⟩
  have hS : ∀ k, (U.X k).IsSec (laU U 0 (r * (2 * R ^ 4 * i)) k) (rdU U f k) :=
    hU.2.2.2.2.1 0 _ ⟨fun _ => antitone_const, hev⟩ f hsec
  refine ⟨hS, fun k x hx => ?_⟩
  obtain ⟨b, -, hb, hun, -, hphi, hp⟩ := GlobalTheory.T.exists_borel_orthonormal_flag_frame E r (U.X k) x hx
  rw [hp _ _ (hS k), ← hphi]
  exact GlobalTheory.T.norm_etaProductForm_le_at_unit_frame E H Dw l Xo c σ r U hσ hU hT R i N hR hR1 hG hN J cf xs f hJ hcf hsp hf DF q m R0 hrun hm k
    ⟨_, hb⟩ hun

end GlobalTheory.EtaAn
