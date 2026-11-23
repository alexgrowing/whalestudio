import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfBas

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

section Bas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem basRatV_add (x y : Fin n → E) :
    ratV (F := F) (Fv F v) (x + y) = ratV (F := F) (Fv F v) x + ratV (F := F) (Fv F v) y := by
  funext i
  simp [ratV, map_add]

theorem basRatV_zsmul (c : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (c • x) = c • ratV (F := F) (Fv F v) x := by
  funext i
  simp [ratV]

theorem basRatV_zero : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

theorem basRatV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

theorem basInt_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

theorem basLat_fg (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsLattice E L) :
    (latLoc (E := E) v (L : Set (Fin n → E))).FG := by
  classical
  obtain ⟨s, hs⟩ : (L.restrictScalars ℤ).FG := hLat.fg.restrictScalars
  refine ⟨s.image (ratV (F := F) (Fv F v)), ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxL : x ∈ L := by
      have : x ∈ L.restrictScalars ℤ := by
        rw [← hs]
        exact Submodule.subset_span hx
      exact this
    exact Submodule.subset_span ⟨x, hxL, rfl⟩
  · unfold latLoc
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span ℤ (s : Set (Fin n → E)) := by
      rw [hs]
      exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      rw [basRatV_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [basRatV_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [basRatV_zsmul]
      exact zsmul_mem hy c

theorem basSpan_top (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsLattice E L) :
    Submodule.span (Fv F v) (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) = ⊤ := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let bE := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Fv F v) bE
  let P := Pi.basis (fun _ : Fin n => B)
  rw [eq_top_iff, ← P.span_eq, Submodule.span_le]
  rintro _ ⟨⟨i, k⟩, rfl⟩
  obtain ⟨N, hN, hNL⟩ := basInt_smul_mem L hLat.span_eq_top (Pi.single i (bE k) : Fin n → E)
  have hN' : (N : Fv F v) ≠ 0 := by
    rw [← map_intCast (algebraMap F (Fv F v))]
    exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hN)
  have hmem : ratV (F := F) (Fv F v) (N • (Pi.single i (bE k) : Fin n → E)) ∈
      latLoc (E := E) v (L : Set (Fin n → E)) := Submodule.subset_span ⟨_, hNL, rfl⟩
  have e : P ⟨i, k⟩ = (N : Fv F v)⁻¹ • ratV (F := F) (Fv F v) (N • (Pi.single i (bE k) : Fin n → E)) := by
    rw [basRatV_zsmul, basRatV_single, ← Int.cast_smul_eq_zsmul (Fv F v), smul_smul, inv_mul_cancel₀ hN', one_smul]
    simp only [P, B, Pi.basis_apply, Algebra.TensorProduct.basis_apply]
    rfl
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Bas

end PI.OmLocU
