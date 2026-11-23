import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Published

theorem arProj_of_heightProjection (H : HeightProjection) : ArProj := by
  intro k _ X Y _ _ p q D hX hY π hπ hg hm
  have key (L : HermLB p) (a : ℝ) (ha : L.IsSelfInter a) :
      (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * a) := by
    obtain ⟨h, hh, rfl⟩ := ha
    have := H k X Y p q D D hX hY π hπ (by
      rw [hg, (genericPoint_spec X).def]
      exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).trans hX.dim_eq) hm L h hh
    exact (congrArg (fun x => (π.residueDegree (genericPoint Y) : ℝ) * h x) hg) ▸ this
  refine ⟨key, fun ι _ L Φ hΦ => ⟨fun n => ?_, fun P d hd hP => ?_⟩⟩
  · exact (ArInt.isometric_comb_pull L n π hπ).symm.isSelfInter hY (key _ _ (hΦ.1 n))
  · rw [LinearMap.smul_apply, hΦ.2 P d hd hP, smul_zero]

end GlobalTheory.Published
