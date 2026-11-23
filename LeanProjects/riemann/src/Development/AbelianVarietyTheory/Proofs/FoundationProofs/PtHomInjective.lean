import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.PolarLatticePairs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.ThetaLatticePoints

def ptHom (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) :
    Matrix (Fin d) (Fin a) D.host.E →+ VC D a d :=
  AddMonoidHom.mk' (pt D (tor0 D cc δ) δ) fun y y' => by
    funext τ i j
    simp [pt, embV, tor0, mul_add]

theorem ptHom_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ)
    (z : Matrix (Fin d) (Fin a) D.host.E) : ptHom D cc δ a d z = pt D (tor0 D cc δ) δ z := rfl

theorem ptHom_injective (D : D7) (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) (a d : ℕ) :
    Function.Injective (ptHom D cc δ a d) := by
  intro y y' h
  refine Matrix.ext fun i j => ?_
  have h1 : δ * embT D (D.eTau.symm 1) (y i j) = δ * embT D (D.eTau.symm 1) (y' i j) :=
    congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
  exact (embT D _).injective (mul_left_cancel₀ hδ h1)

theorem ptHom_smul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) (c : 𝓞 D.host.K)
    (y : Matrix (Fin d) (Fin a) D.host.E) :
    ptHom D cc δ a d (((c : D.host.K) : D.host.E) • y) =
      (δ * D.host.φ₀ ((c : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) y := by
  funext τ i j
  simp only [ptHom_apply, pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    GlobalTheory.InducedType.restrict_K D τ, mul_assoc]

theorem single_mem (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) (i : Fin d) (j : Fin a)
    {t : D.host.E} (ht : t ∈ coefLat D cc) (r : 𝓞 D.host.E) :
    ptHom D cc δ a d (Matrix.single i j (r • t)) ∈ La0 D (tor0 D cc δ) a d := by
  induction ht using Submodule.span_induction generalizing r with
  | mem t ht =>
    obtain ⟨c, hc, m, hm, rfl⟩ := ht
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ ((c : D.host.K) : D.host.E),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, Matrix.single i j (r • m), ?_, ?_⟩
    · refine (GlobalTheory.OddGenus.mem_iff_entries D a d _).2 fun k l => ?_
      rw [Matrix.single_apply]
      split_ifs
      · exact (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem r hm
      · exact D.host.AA0.zero_mem
    · rw [← ptHom_smul, Matrix.smul_single, smul_eq_mul, mul_smul_comm]
  | zero => rw [smul_zero, Matrix.single_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add, Matrix.single_add, map_add]; exact add_mem (hx r) (hy r)
  | smul s x _ hx => rw [smul_smul]; exact hx _

theorem La0_eq_map (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) :
    La0 D (tor0 D cc δ) a d = (lat0 D cc a d).map (ptHom D cc δ a d) := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D cc δ w).1 hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ptHom_smul D cc δ a d c A⟩
    exact Submodule.subset_span ⟨c, hc, A i j, (GlobalTheory.OddGenus.mem_iff_entries D a d A).1 hA i j, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [Matrix.matrix_eq_sum_single z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_sum]
    refine sum_mem fun j _ => ?_
    simpa using single_mem D cc δ a d i j (hz i j) 1

theorem pt_mem_iff : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ), Crv D cc δ → ∀ z : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) a d ↔ z ∈ lat0 D cc a d := by
  intro D cc δ a d h z
  have hδ : δ ≠ 0 :=
    (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.1
  rw [La0_eq_map, ← ptHom_apply]
  exact AddSubgroup.mem_map_iff_mem (ptHom_injective D cc hδ a d)

end GlobalTheory.ThetaLatticePoints
