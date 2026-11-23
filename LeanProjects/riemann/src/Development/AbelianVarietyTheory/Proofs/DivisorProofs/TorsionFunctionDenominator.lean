import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTorsionPrechartCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOfLocalPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFunctionsGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem pow_smul_mem_ord_of_chart : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp → ∀ f : Tors G N K → K, (∀ s : Tors G N K, ∃ a : c.C, ∀ ψ : c.C →ₐ[R] K, ψ a = f (s * torsMap ψ c.j)) → ∃ k : ℕ, c.r ^ k • f ∈ ord G N K := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN q c hc f hf
  obtain ⟨Idx, hIdx, q', c', hcov⟩ := GlobalTheory.T.exists_finite_torsion_prechart_cover R K G hG N hN
  have hfin : ∀ i, Finite ((c' i).C →ₐ[R] K) := fun i => (GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN (q' i) (c' i)).1

  have hT : Finite (Tors G N K) := by
    have hsub : (Set.univ : Set (Tors G N K)) ⊆ ⋃ i, Set.range (fun ψ : (c' i).C →ₐ[R] K => torsMap ψ (c' i).j) := by
      intro z _
      obtain ⟨i, hi⟩ := hcov K z
      obtain ⟨ψ, -, hψ⟩ := ((c' i).bij K).surjOn hi
      exact Set.mem_iUnion.2 ⟨i, ψ, hψ⟩
    have : (⋃ i, Set.range (fun ψ : (c' i).C →ₐ[R] K => torsMap ψ (c' i).j)).Finite :=
      Set.finite_iUnion fun i => Set.finite_range _
    exact Set.finite_univ_iff.1 (this.subset hsub)

  have hloc : ∀ (s : Tors G N K) (i : Idx), ∃ (k : ℕ) (a : (c' i).C), ∀ ψ : (c' i).C →ₐ[R] K,
      ψ a = ψ (algebraMap R (c' i).C c.r) ^ k * f (s * torsMap ψ (c' i).j) := by
    intro s i
    haveI := hfin i
    exact GlobalTheory.T.exists_global_of_local_prime R K (c' i).C (algebraMap R (c' i).C c.r) (fun ψ => f (s * torsMap ψ (c' i).j))
      (fun P _ hP => GlobalTheory.T.torsion_prechart_translate R K G hG N hN q c hc f hf (q' i) (c' i) s P hP)
  choose kf af haf using hloc
  haveI := hT
  haveI : Fintype (Tors G N K × Idx) := Fintype.ofFinite _
  refine ⟨Finset.univ.sup (fun p : Tors G N K × Idx => kf p.1 p.2), fun s => ?_⟩
  set k := Finset.univ.sup (fun p : Tors G N K × Idx => kf p.1 p.2)
  have hk : ∀ i, kf s i ≤ k := fun i =>
    Finset.le_sup (f := fun p : Tors G N K × Idx => kf p.1 p.2) (Finset.mem_univ (s, i))
  obtain ⟨σ, hσ, hσg⟩ := GlobalTheory.T.torsion_functions_glue R K G hG N hN Idx q' c' hcov (fun x => algebraMap R K c.r ^ k * f (s * x))
    (fun i => ⟨algebraMap R (c' i).C c.r ^ (k - kf s i) * af s i, fun ψ => by
      rw [map_mul, map_pow, haf, AlgHom.commutes, ← _root_.mul_assoc, ← _root_.pow_add, Nat.sub_add_cancel (hk i)]⟩)
  refine ⟨σ, hσ, fun x => ?_⟩
  rw [hσg x, Pi.smul_apply, Algebra.smul_def, map_pow]

end GlobalTheory.GroupBplus.Aff
