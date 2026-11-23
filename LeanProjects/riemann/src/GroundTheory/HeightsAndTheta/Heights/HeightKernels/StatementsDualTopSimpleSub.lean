import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSubLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualTopSimpleSub.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F'.withStdMetric.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

namespace DualTopSimpleSubExample

def oneVec : Fin 1 → ℚ := fun _ => 1

theorem oneVec_mem : oneVec ∈ (HermLattice.standard ℚ 1).lattice := by
  apply Submodule.subset_span
  refine ⟨0, ?_⟩
  funext j
  fin_cases j
  rfl

theorem coord_of_mem {v : Fin 1 → ℚ} (hv : v ∈ (HermLattice.standard ℚ 1).lattice) : ∃ n : ℤ, v 0 = n := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 ℚ)).mp hv
  refine ⟨Rat.ringOfIntegersEquiv (c 0), ?_⟩
  rw [← hc, Rat.ringOfIntegersEquiv_apply_coe]
  simp [Algebra.smul_def]

theorem coord_of_mem_two {v : Fin 1 → ℚ} (hv : v ∈ HermLattice.twiceStandardExample.lattice) :
    ∃ m : ℤ, v 0 = 2 * m := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
  rw [Rat.ringOfIntegersEquiv_apply_coe]
  simp [twoVecExample, Algebra.smul_def, mul_comm]

theorem evenVec_mem (m : ℤ) :
    (fun _ : Fin 1 => 2 * (m : ℚ)) ∈ HermLattice.twiceStandardExample.lattice := by
  have h : (fun _ : Fin 1 => 2 * (m : ℚ)) = (m : 𝓞 ℚ) • twoVecExample := by
    funext j
    simp [twoVecExample, Algebra.smul_def, mul_comm]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem twice_lt : HermLattice.twiceStandardExample.lattice < (HermLattice.standard ℚ 1).lattice := by
  refine lt_of_le_of_ne twiceStandardExample_le fun h => ?_
  obtain ⟨m, hm⟩ := coord_of_mem_two (h ▸ oneVec_mem)
  have h1 : (1 : ℤ) = 2 * m := by
    simp only [oneVec] at hm
    exact_mod_cast hm
  omega

theorem twice_cover (N : Submodule (𝓞 ℚ) (Fin 1 → ℚ))
    (h₁ : HermLattice.twiceStandardExample.lattice ≤ N) (h₂ : N ≤ (HermLattice.standard ℚ 1).lattice) :
    N = HermLattice.twiceStandardExample.lattice ∨ N = (HermLattice.standard ℚ 1).lattice := by
  by_cases hN : N ≤ HermLattice.twiceStandardExample.lattice
  · exact Or.inl (le_antisymm hN h₁)
  right
  refine le_antisymm h₂ ?_
  obtain ⟨u, huN, hu2⟩ := SetLike.not_le_iff_exists.mp hN
  obtain ⟨n, hn⟩ := coord_of_mem (h₂ huN)
  have hu : u = fun _ => (n : ℚ) := by
    funext j
    fin_cases j
    exact hn
  have hodd : ¬ ∃ m : ℤ, n = 2 * m := by
    rintro ⟨m, rfl⟩
    apply hu2
    rw [hu]
    push_cast
    exact evenVec_mem m
  have hm : n = 2 * (n / 2) + 1 := by
    by_contra hne
    exact hodd ⟨n / 2, by omega⟩
  have hone : oneVec ∈ N := by
    have h1 : oneVec = u - fun _ => 2 * ((n / 2 : ℤ) : ℚ) := by
      rw [hu]
      funext j
      simp only [oneVec, Pi.sub_apply]
      have : (n : ℚ) = 2 * ((n / 2 : ℤ) : ℚ) + 1 := by exact_mod_cast hm
      linarith
    rw [h1]
    exact sub_mem huN (h₁ (evenVec_mem _))
  show Submodule.span (𝓞 ℚ) _ ≤ N
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have : (Pi.single j 1 : Fin 1 → ℚ) = oneVec := by
    funext k
    fin_cases j
    fin_cases k
    rfl
  show (Pi.single j 1 : Fin 1 → ℚ) ∈ N
  rw [this]
  exact hone

end DualTopSimpleSubExample

open DualTopSimpleSubExample in

example : ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T)
    (b' : Module.Basis T ℤ (dualLattice HermLattice.twiceStandardExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b')) ∧
      Function.Bijective (Matrix.mulVecLin
        (dualEmbMatrix (F := HermLattice.standard ℚ 1) dualBasisStandard)) ∧
      HermLattice.twiceStandardExample.lattice < (HermLattice.standard ℚ 1).lattice ∧
      (∀ N : Submodule (𝓞 ℚ) (Fin 1 → ℚ), HermLattice.twiceStandardExample.lattice ≤ N →
        N ≤ (HermLattice.standard ℚ 1).lattice →
        N = HermLattice.twiceStandardExample.lattice ∨ N = (HermLattice.standard ℚ 1).lattice) ∧
      1 ≤ 1 := by
  obtain ⟨T, hT, hdT, ⟨b'⟩⟩ := DualLatticeBasisExists.proof ℚ 1 HermLattice.twiceStandardExample
  exact ⟨T, hT, hdT, b', DualEmbBijective.proof ℚ 1 _ T b', dualEmbMatrix_standard_bijective, twice_lt,
    twice_cover, le_rfl⟩

end

end GroundTheory.Heights₂.Heights
