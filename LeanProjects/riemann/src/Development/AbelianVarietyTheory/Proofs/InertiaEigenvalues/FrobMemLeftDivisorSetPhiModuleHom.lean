import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.Hom

section Bounds

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_sum_le {s : Type} (t : Finset s) (f : s → K⟦X⟧) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ k n, ‖coeff n (f k)‖ ≤ C) (n : ℕ) : ‖coeff n (∑ k ∈ t, f k)‖ ≤ C := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hC
  | insert k t hk ih =>
    rw [Finset.sum_insert hk, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf k n) ih)

theorem bdd_matMul {μ ν ρ : Type} [Fintype ν] {Y : Matrix μ ν K⟦X⟧} {Z : Matrix ν ρ K⟦X⟧}
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) (hZ : ∃ c : ℝ, ∀ i j n, ‖coeff n (Z i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y * Z) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hY
  obtain ⟨b, hb⟩ := hZ
  refine ⟨max a 0 * max b 0, fun i j n => ?_⟩
  rw [Matrix.mul_apply]
  refine norm_coeff_sum_le _ (fun k => Y i k * Z k j)
    (mul_nonneg (le_max_right _ _) (le_max_right _ _)) (fun k m => ?_) n
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    (le_max_right a 0) (le_max_right b 0) (f := Y i k) (g := Z k j)
    (fun p => by rw [mul_one]; exact (ha i k p).trans (le_max_left _ _))
    (fun p => by rw [mul_one]; exact (hb k j p).trans (le_max_left _ _)) m

theorem bdd_frob (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (frob K l f)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, fun n => ?_⟩
  rw [coeff_frob]
  split_ifs
  · exact hc _
  · simpa using (norm_nonneg _).trans (hc 0)

theorem bdd_map_frob (l : ℕ) [Fact l.Prime] {μ ν : Type} {Y : Matrix μ ν K⟦X⟧}
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y.map (frob K l)) i j)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hY
  refine ⟨max c 0, fun i j n => ?_⟩
  rw [Matrix.map_apply, coeff_frob]
  split_ifs
  · exact (hc _ _ _).trans (le_max_left _ _)
  · simp

end Bounds

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem exists_pow_E_mul_mem (l e : ℕ) {s : Type} [Finite s] (f : s → K⟦X⟧)
    (hf : ∀ x, f x ∈ invE l e (A O K)) : ∃ N : ℕ, ∀ x, E K l e ^ N * f x ∈ A O K := by
  classical
  cases nonempty_fintype s
  choose n hn using fun x => mem_away.1 (hf x)
  refine ⟨Finset.univ.sup n, fun x => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ x))
  rw [hc, pow_add, mul_assoc]
  exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn x)

theorem bdd_of_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c := ⟨1, hf⟩

theorem map_frob_smul_one (l : ℕ) [Fact l.Prime] {μ : Type} [DecidableEq μ] (h : K⟦X⟧) :
    (h • (1 : Matrix μ μ K⟦X⟧)).map (frob K l) = frob K l h • (1 : Matrix μ μ K⟦X⟧) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

section Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem mxInv_mul_mat (F : Hom P Q) (τ : ZMod a) :
    Q.mxInv τ * F.mat τ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
  calc Q.mxInv τ * F.mat τ = Q.mxInv τ * (F.mat τ * P.mx τ) * P.mxInv τ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one]
    _ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
        rw [F.comm, ← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]

theorem frob_ldiv_eq (F : Hom P Q) (τ : ZMod a) {h : K⟦X⟧} {Y : Matrix ι κ K⟦X⟧}
    (hY : Y * F.mat (τ - 1) = h • (1 : Matrix ι ι K⟦X⟧)) :
    P.mx τ * Y.map (frob K l) * Q.mxInv τ * F.mat τ = frob K l h • (1 : Matrix ι ι K⟦X⟧) := by
  have hφ : Y.map (frob K l) * (F.mat (τ - 1)).map (frob K l) = frob K l h • (1 : Matrix ι ι K⟦X⟧) := by
    rw [← map_frob_smul_one l h, ← hY]
    exact (Matrix.map_mul (f := ((frob K l : K⟦X⟧ →ₐ[K] K⟦X⟧) : K⟦X⟧ →+* K⟦X⟧))).symm
  rw [Matrix.mul_assoc, mxInv_mul_mat, ← Matrix.mul_assoc,
    Matrix.mul_assoc (P.mx τ) (Y.map (frob K l)), hφ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, P.mx_mul_mxInv]

end Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem exists_pow_E_mul_frob_mem_ldivSet (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NeZero a] (κ : Type) [Fintype κ] [DecidableEq κ]
    (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : Hom P Q) :
    ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.ldivSet τ := by
  obtain ⟨N₁, hN₁⟩ := exists_pow_E_mul_mem (O := O) l e (fun p : ZMod a × ι × ι => P.mx p.1 p.2.1 p.2.2)
    fun p => P.mx_mem _ _ _
  obtain ⟨N₂, hN₂⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × κ × κ => Q.mxInv p.1 p.2.1 p.2.2) fun p => Q.mxInv_mem _ _ _
  refine ⟨N₁ + N₂, fun τ h ⟨hb, Y, hY, hYF⟩ => ⟨?_, ?_⟩⟩
  · exact bdd_mul (bdd_of_mem_A (pow_mem (E_mem l e (A O K)) _)) (bdd_frob l hb)
  · refine ⟨(E K l e ^ N₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ N₂ • Q.mxInv τ),
      bdd_matMul (bdd_matMul ⟨1, fun i j n => ?_⟩ (bdd_map_frob l hY)) ⟨1, fun i j n => ?_⟩, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]; exact hN₁ (τ, i, j) n
    · rw [Matrix.smul_apply, smul_eq_mul]; exact hN₂ (τ, i, j) n
    · simp only [Matrix.smul_mul, Matrix.mul_smul]
      rw [frob_ldiv_eq F τ hYF, smul_smul, smul_smul, pow_add]
      congr 1
      ring

end GlobalTheory.BK.Hom

theorem GlobalTheory.BK.Hom.frob_mem_ldivSet_target : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.ldivSet τ := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  exact GlobalTheory.BK.Hom.exists_pow_E_mul_frob_mem_ldivSet l e a ι κ P Q F
