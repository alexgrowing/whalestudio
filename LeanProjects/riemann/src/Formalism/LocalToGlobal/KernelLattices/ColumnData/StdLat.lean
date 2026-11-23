import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData

noncomputable section

namespace Formalism.L2.Ker.Cd.Inhab

open Formalism.BasicNotions NumberField

variable (D : Car)

theorem mem_stdL {N : ℕ} (x : Fin N → D.host.E) :
    x ∈ Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N ↔ ∀ i, x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  simp [Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL, Submodule.mem_pi, Submodule.mem_one, RingHom.mem_range]

theorem single_mem_stdL {N : ℕ} (a : Fin N) : (Pi.single a 1 : Fin N → D.host.E) ∈ Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N := by
  rw [mem_stdL]
  intro i
  by_cases h : i = a
  · subst h
    simp only [Pi.single_eq_same]
    exact one_mem _
  · simp only [Pi.single_eq_of_ne h]
    exact zero_mem _

theorem star_mem_range (x : D.host.E) (h : x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    (letI := D.host.cmStar; star x) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  letI := D.host.cmStar
  obtain ⟨y, rfl⟩ := RingHom.mem_range.1 h
  have hi : IsIntegral ℤ (star (algebraMap (𝓞 D.host.E) D.host.E y)) :=
    (NumberField.RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom
  exact RingHom.mem_range.2 ⟨⟨_, hi⟩, rfl⟩

theorem stdL_isSD (N : ℕ) : (letI := D.host.cmStar; IsSDLat D.host.E N (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N)) := by
  letI := D.host.cmStar
  refine ⟨?_, ?_, ?_⟩
  · have hspan : Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N = Submodule.span (𝓞 D.host.E)
        (Set.range fun i : Fin N => (Pi.single i 1 : Fin N → D.host.E)) := by
      apply le_antisymm
      · intro y hy
        rw [mem_stdL] at hy
        have hy' : ∀ i, ∃ z, algebraMap (𝓞 D.host.E) D.host.E z = y i := fun i => RingHom.mem_range.1 (hy i)
        choose z hz using hy'
        have hyz : y = ∑ i, z i • (Pi.single i 1 : Fin N → D.host.E) := by
          funext j
          simp [Finset.sum_apply, Pi.single_apply, ← hz j, Algebra.algebraMap_eq_smul_one]
        rw [hyz]
        exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact single_mem_stdL D i
    rw [hspan]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [eq_top_iff]
    rintro v -
    rw [← (Pi.basisFun D.host.E (Fin N)).sum_repr v]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    rw [Pi.basisFun_apply]
    exact single_mem_stdL D i
  · intro y
    constructor
    · intro hy x hx
      rw [mem_stdL] at hx hy
      simp only [stdH]
      refine Subring.sum_mem _ (fun i _ => ?_)
      first
        | exact Subring.mul_mem _ (star_mem_range D _ (hx i)) (hy i)
        | exact Subring.mul_mem _ (hx i) (star_mem_range D _ (hy i))
        | exact Subring.mul_mem _ (hy i) (star_mem_range D _ (hx i))
        | exact Subring.mul_mem _ (star_mem_range D _ (hy i)) (hx i)
    · intro h
      rw [mem_stdL]
      intro i
      have := h _ (single_mem_stdL D i)
      simp only [stdH] at this
      rw [Fintype.sum_eq_single i (fun j hj => by simp [Pi.single_eq_of_ne hj])] at this
      simp only [Pi.single_eq_same, star_one, one_mul, mul_one] at this
      first
        | exact this
        | simpa using star_mem_range D _ this

theorem Adm_std (N N' : ℕ) (h : Even N) (h' : Even N') :
    Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D N N' (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N') := by
  exact ⟨h, h', stdL_isSD D N, stdL_isSD D N'⟩

end Formalism.L2.Ker.Cd.Inhab
