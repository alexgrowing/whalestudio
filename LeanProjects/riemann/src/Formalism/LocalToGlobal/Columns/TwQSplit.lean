import Formalism.LocalToGlobal.Columns.TiedGlSplit
import Formalism.LocalToGlobal.Columns.TwQDefs

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)

theorem qsp_exists_pi (P : Pl E) (hP : conjPrime₂ P ≠ P) : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal := by
  obtain ⟨s, hs, hns⟩ := exists_mem_notMem (Ne.symm hP)
  exact ⟨s, hs, fun h => hns ((mem_conjP P s).2 h)⟩

include hc in

theorem qsp_norm_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a * cO E a := by
  have h1 : star (algebraMap (𝓞 E) E (a * cO E a)) = algebraMap (𝓞 E) E (a * cO E a) := by
    rw [map_mul, algebraMap_cO, star_mul', star_star, mul_comm]
  obtain ⟨x, hx⟩ := (hc.fixed _).1 h1
  have hi : IsIntegral ℤ x := by
    have h2 : IsIntegral ℤ (algebraMap F E x) := by rw [hx]; exact RingOfIntegers.isIntegral_coe _
    exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h2
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) F b = x := ⟨⟨x, hi⟩, rfl⟩
  refine ⟨b, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) b) = algebraMap (𝓞 E) E (a * cO E a)
  rw [← hx, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem qsp_isOver (P : Pl E) : IsOver (underPl F P) P := rfl

include hc in

theorem qsp_exists (P : Pl E) (hP : conjPrime₂ P ≠ P) :
    ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal ∧ Nonempty (Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P) (ϖ : E)) := by
  obtain ⟨ϖ, hϖ, hcϖ⟩ := qsp_exists_pi P hP
  obtain ⟨t, ht⟩ := gls_trace_mem hc ϖ
  obtain ⟨N, hN⟩ := qsp_norm_mem hc ϖ
  have hsig : ∀ x : E, hc.sig x = star x := fun _ => rfl
  have hsig0 : hc.sig (ϖ : E) = ((cO E ϖ : 𝓞 E) : E) := by rw [hsig]; exact (algebraMap_cO ϖ).symm
  have hN' : algebraMap F E (N : F) = (ϖ : E) * hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hN
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have ht' : algebraMap F E (t : F) = (ϖ : E) + hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) ht
    rw [map_add, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have hNv : N ∈ (underPl F P).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
    rw [hN]; exact Ideal.mul_mem_right _ _ hϖ
  have htv : t ∉ (underPl F P).asIdeal := by
    intro h
    have h1 : algebraMap (𝓞 F) (𝓞 E) t ∈ P.asIdeal := h
    rw [ht] at h1
    exact hcϖ (by simpa using P.asIdeal.sub_mem h1 hϖ)
  obtain ⟨s⟩ := Formalism.MainNotions.Gaps.LG.sc_core hc.sig (fun x => by rw [hsig, hsig, star_star])
    (fun x hx => (hc.fixed x).1 hx) hc.deg2 (underPl F P) ϖ t N ht' hN' hNv htv
  have hN2 : ((cO E ϖ : 𝓞 E) : E) * hc.sig ((cO E ϖ : 𝓞 E) : E) = algebraMap F E (N : F) := by
    rw [hN', ← hsig0, mul_comm, hsig, hsig, star_star]
  obtain ⟨sa⟩ := Formalism.MainNotions.Gaps.LG.sc_orient s (cO E ϖ) N hNv hN2
  have e : hc.sig ((cO E ϖ : 𝓞 E) : E) = (ϖ : E) := by rw [← hsig0, hsig, hsig, star_star]
  exact ⟨ϖ, hϖ, hcϖ, ⟨e ▸ sa⟩⟩

end Split

end Formalism.L2.Col
