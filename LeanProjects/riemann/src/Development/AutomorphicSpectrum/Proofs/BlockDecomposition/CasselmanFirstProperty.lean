import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetRepsUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetFormulaStatement

noncomputable section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem hecke_dominant_mul_abstract (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    PositivityTheory.SphericalProduct.A1 G := by
  intro D V _ _ π hπ t t' ht _ U U' hU hU' v f hf
  obtain ⟨r, hr, x, hx, hcos⟩ := GlobalTheory.T.dominant_coset_reps_unipotent G D t' ‹_›
  have hform := GlobalTheory.T.hecke_operator_coset_formula G D.J D.isOpen_J D.isCompact_J V π hπ (t' : G) U' hU' r x hr
    (fun i => (hx i).1) hcos v
  have hfx : ∀ (x : G), x ∈ D.J → ∀ w : V, f (π x w) = f w := fun x hxJ w =>
    LinearMap.congr_fun (hf x hxJ) w
  have hterm : ∀ i, f (π (t : G) (π (x i * (t' : G)) (v : V))) = f (π ((t : G) * t') (v : V)) := by
    intro i
    have hconj : (t : G) * x i * (t : G)⁻¹ ∈ D.J := (ht.1 (x i) (hx i)).1
    have hmul : (t : G) * (x i * (t' : G)) = ((t : G) * x i * (t : G)⁻¹) * ((t : G) * t') := by group
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]
    exact hfx _ hconj _
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hUU : ((((U * U') v : fixed π D.J)) : V) = ((U (U' v) : fixed π D.J) : V) := rfl
  rw [hUU, ← hU (U' v) f hf, hform, map_smul, map_smul, map_sum, map_sum, Finset.sum_congr rfl (fun i _ => hterm i)]
  simp [hr0]

end GlobalTheory.CompanionTheory.Casselman

end
