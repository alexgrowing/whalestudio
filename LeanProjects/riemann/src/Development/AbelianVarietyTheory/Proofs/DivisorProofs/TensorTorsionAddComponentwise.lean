import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

theorem GlobalTheory.Mum.TensTor.qkAdd_of_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (p' q' s' : QkPt D'.toPre F k) (ps qs ss : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → PtRel T ν ν' s' ss → (∀ i, QkAdd (ps i) (qs i) (ss i)) → QkAdd p' q' s' := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' k p' q' s' ps qs ss hp hq hs hadd
  have gt : GlobalTheory.Ex.BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  obtain ⟨-, -, gAdd, -, gQ⟩ := gt R D.toPre D.psi_even D.tau_bimult F N ν
  obtain ⟨-, -, gAdd', -, gQ'⟩ := gt R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  have hF := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  obtain ⟨-, -, he, hebij, -, -, -, -⟩ := hF
  obtain ⟨P', Ps, hP', hPs, hPy, hPg⟩ := hp
  obtain ⟨Q', Qs, hQ', hQs, hQy, hQg⟩ := hq
  obtain ⟨S', Ss, hS', hSs, hSy, hSg⟩ := hs
  have hz : ∀ i, N.QEq (Ps i * Qs i) (Ss i) := by
    intro i
    obtain ⟨x, hxy, hxg, hxe⟩ := hadd i
    obtain ⟨X, hX⟩ := ((gQ k).1 x).exists
    have hXeq : X = Ps i * Qs i := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · apply Multiplicative.toAdd.injective
        apply ν.eX.injective
        rw [hX.1, hxy, ← (hPs i).1, ← (hQs i).1, ← map_add]
        rfl
      · exact (gAdd _ _ _ _ _ _ (hPs i).2 (hQs i).2 hX.2).1 hxg
    rw [← hXeq]
    exact ((gQ k).2.2 x (ss i) X (Ss i) hX (hSs i)).1 hxe
  choose z hz1 hz2 using hz
  obtain ⟨z', hz'⟩ := hebij.2 z
  have he0 : ∀ i, chi T ν ν' 0 i = 0 := fun i => by
    have := he 0 0 i
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have hensmul : ∀ (n : ℕ) χ i, chi T ν ν' (n • χ) i = n • chi T ν ν' χ i := by
    intro n χ i
    induction n with
    | zero => rw [zero_smul, zero_smul, he0]
    | succ n ih => rw [succ_nsmul, he, ih, succ_nsmul]
  obtain ⟨x', hx'⟩ := (gQ' k).2.1 (P' * Q')
  refine ⟨x', ?_, ?_, ?_⟩
  · rw [← hx'.1, ← hP'.1, ← hQ'.1, ← map_add]
    rfl
  · exact (gAdd' _ _ _ _ _ _ hP'.2 hQ'.2 hx'.2).2 rfl
  · refine ((gQ' k).2.2 x' s' (P' * Q') S' hx' hS').2 ⟨z', ?_, ?_⟩
    · apply hebij.1
      funext i
      have e1 : (P' * Q').1.1.toAdd = P'.1.1.toAdd + Q'.1.1.toAdd := rfl
      have e2 : (Ps i * Qs i).1.1.toAdd = (Ps i).1.1.toAdd + (Qs i).1.1.toAdd := rfl
      rw [hSy i, hz1 i, he, hensmul, hz', e1, he, hPy i, hQy i, e2]
    · have m1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        P'.1.2 Q'.1.2 _ _ hPg hQg
      have m2 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν') z'
      have m3 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        _ _ _ _ m1 m2
      have e3 : ((fun j => (Ps j).1.2) * (fun j => (Qs j).1.2)) * (fun j => N.io (chi T ν ν' z' j)) =
          fun j => (Ss j).1.2 := by
        funext j
        rw [hz2 j, hz']
        rfl
      rw [e3] at m3
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        _ _ _ hSg m3
