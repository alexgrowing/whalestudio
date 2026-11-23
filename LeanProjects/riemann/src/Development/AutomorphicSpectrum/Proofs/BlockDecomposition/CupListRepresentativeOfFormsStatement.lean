import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_list_representative_of_forms : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}  {d : ℕ}    (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (m : ℕ) (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1) (c : Fin m → Fin d → Φ.A.obj E.D) (h : Fin m → ∀ T : C, Φ.A.obj T),
    (∀ k T, h k T ∈ Φ.J.S T) →
    (∀ (k : Fin m) (u : ComposableArrows C 1), (show Φ.A.obj (u.obj (Fin.last 1)) from ℓ k u) -
      (∑ i, E.form σ ![i] (c k i) u + (h k (u.obj (Fin.last 1)) - (Φ.A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h k (u.obj 0)))) ∈ (Fil 2).S _) →
    ∀ (w : Φ.A.obj E.D) (r : ℤ), r = m → ∀ x : CH.H (gr Fil r) m,
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => (show Φ.A.obj (u.obj (Fin.last m)) from cupListC Φ.A ℓ u) * (Φ.A.map (σ _)).hom w) x →
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Fin m → Fin d, E.form σ I (w * ∏ k, c k (I k)) u) x := by
  first | exact @GlobalTheory.CompanionTheory.CupRep.cup_rep | exact GlobalTheory.CompanionTheory.CupRep.cup_rep | (intros; apply GlobalTheory.CompanionTheory.CupRep.cup_rep <;> assumption)
