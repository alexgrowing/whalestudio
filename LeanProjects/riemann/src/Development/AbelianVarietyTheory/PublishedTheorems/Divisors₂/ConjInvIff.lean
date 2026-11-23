import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt

namespace GlobalTheory.Published.SiegelModel

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

omit [NumberField K] in

theorem conjInv_iff (h : HermFam K (Fin m → K)) : ConjInv h ↔ h.IsConjInv := Iff.rfl

theorem conjInv_std : ConjInv (stdHerm K m) := by
  intro σ x y
  simp [stdHerm]

theorem full_std : Full (stdLat K m) := by
  classical
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun K (Fin m)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span (Submodule.subset_span ⟨i, (Pi.basisFun_apply K (Fin m) i).symm⟩)

omit [NumberField K] in
theorem latBC_self (L : Submodule (𝓞 K) (Fin m → K)) : latBC K L = L := by
  simp [latBC]

omit [NumberField K] in
theorem isBC_self (h : HermFam K (Fin m → K)) : IsBC h h := by
  intro σ i j
  congr 1

theorem lineLat_fg {L : Submodule (𝓞 K) (Fin m → K)} (hL : L.FG) (x : Fin m → K) : (lineLat L x).FG :=
  Submodule.FG.of_le hL inf_le_left

theorem latBC_fg (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] {L : Submodule (𝓞 K) (Fin m → K)} (hL : L.FG) :
    (latBC K' L).FG := by
  obtain ⟨s, rfl⟩ := hL
  let f : (Fin m → K) → (Fin m → K') := fun v i => algebraMap K K' (v i)
  refine ⟨(s.finite_toSet.image f).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  refine le_antisymm (Submodule.span_mono (Set.image_mono Submodule.subset_span)) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, hv, rfl⟩
  change f v ∈ Submodule.span (𝓞 K') (f '' s)
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => have : f 0 = 0 := by ext i; simp [f]
            rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
      have : f (x + y) = f x + f y := by ext i; simp [f]
      rw [this]; exact add_mem hx hy
  | smul a x _ hx =>
      have : f (a • x) = (algebraMap (𝓞 K) (𝓞 K') a) • f x := by
        ext i
        simp only [f, Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl
      rw [this]; exact Submodule.smul_mem _ _ hx

theorem rank_one (h : HermFam K (Fin 1 → K)) (L : Submodule (𝓞 K) (Fin 1 → K)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (h' : HermFam K' (Fin 1 → K')) (x : Fin 1 → K'),
      IsBC h h' ∧ x ≠ 0 ∧ deg h L / (1 : ℕ) - Real.log (1 : ℕ) / 2 - ε ≤ deg h' (lineLat (latBC K' L) x) := by
  refine ⟨K, inferInstance, inferInstance, inferInstance, h, fun _ => 1, isBC_self h, fun e => one_ne_zero (congrFun e 0), ?_⟩
  have : lineLat L (fun _ : Fin 1 => (1 : K)) = L := by
    refine inf_eq_left.mpr fun v _ => ?_
    rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
    exact ⟨v 0, by ext i; simp [Subsingleton.elim i 0]⟩
  rw [latBC_self, this]
  simp [hε.le]

theorem std_line (H : AbsoluteSiegel) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (h' : HermFam K' (Fin m → K')) (x : Fin m → K'),
      IsBC (stdHerm K m) h' ∧ x ≠ 0 ∧ - Real.log m / 2 - ε ≤ deg h' (lineLat (latBC K' (stdLat K m)) x) := by
  obtain ⟨K', i1, i2, i3, h', x, a, b, c⟩ := H K m (stdHerm K m) (stdLat K m) hm conjInv_std full_std ε hε
  refine ⟨K', i1, i2, i3, h', x, a, b, ?_⟩
  rw [deg_stdLat] at c
  simpa [neg_div] using c

end GlobalTheory.Published.SiegelModel
