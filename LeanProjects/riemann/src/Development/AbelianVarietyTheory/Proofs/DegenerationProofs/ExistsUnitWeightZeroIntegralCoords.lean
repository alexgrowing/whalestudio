import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByWeightZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ModPrim

theorem exists_unit_and_residue_point : Out.Laws → Out.Laws2 → ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (c : Sp (OO p) ⟶ G.left) (w : J → OO p), c ≫ G.hom = spMap j → Crd H σ c w → (∃ i, cls i = 0 ∧ IsUnit (w i)) ∧ ∃ x : m.Φ.Pt, x.left ≫ m.r = rPt p ≫ c ∧ Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
  intro L₁ L₂ p _ V _ j G _ g N N' X _ q H J _ σ cls m hB c w hc hw
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have pb : IsPullback m.r m.Φ.G.hom G.hom (rPt p ≫ spMap j) := m.cart.1
  have hsq : (rPt p ≫ c) ≫ G.hom = 𝟙 _ ≫ rPt p ≫ spMap j := by
    rw [Category.assoc, hc, Category.id_comp]
  let x : m.Φ.Pt := Over.homMk (pb.lift (rPt p ≫ c) (𝟙 _) hsq) (pb.lift_snd _ _ hsq)
  have hx : x.left ≫ m.r = rPt p ≫ c := pb.lift_fst _ _ hsq
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists (R := kb p) (m.Φ.H_isLB 1) m.F x.left
  have h₁ := m.red x v hv
  rw [hx] at h₁
  have h₂ := CrdCalc.crd_map (IsLocalRing.residue (OO p)) hw
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique h₁ h₂
  have h₃ : Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
    have := CrdCalc.crd_smul u hv
    rwa [← funext hu] at this
  refine ⟨?_, x, hx, h₃⟩
  have hcov := (GlobalTheory.T.immBy_weight_zero' L₁ L₂ (kb p) m.Φ g N N' _ J _ m.F m.pol hB m.good m.dim).1
  have hmem : (x.left : Sp (kb p) ⟶ m.Φ.G.left) (IsLocalRing.closedPoint (kb p)) ∈
      ⨆ i ∈ {i | m.xe.symm (cls i) = 0}, Out.nonzeroLocus (m.F i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hmem
  obtain ⟨i, hi, hm⟩ := hmem
  refine ⟨i, m.xe.symm.map_eq_zero_iff.1 hi, ?_⟩
  have h₄ := (CrdCalc.crd_isUnit_iff i h₃).2 ((CrdCalc.top_le_iff _ _).2 hm)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h₄.ne_zero

end GlobalTheory.ZH.ModPrim
