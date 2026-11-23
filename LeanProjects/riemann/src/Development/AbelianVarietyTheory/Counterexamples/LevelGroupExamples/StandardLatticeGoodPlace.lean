import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ThetaIntegralityAtPlaces

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Survey.StandardLatticeGoodPlace

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.ThetaIntegralityAtPlaces

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mem_std {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ j, v j ∈ (algebraMap (𝓞 E) E).range := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one, RingHom.mem_range]

private theorem algebraMap_range_mem_iff_isIntegral (x : E) : x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem unimod_std (H : Host E) (n : ℕ) : GenLat.Unimod (⟨stdLat E n⟩ : GenLat E n) := by
  intro v
  show v ∈ stdLat E n ↔ ∀ w ∈ stdLat E n, _
  simp only [mem_std]
  constructor
  · intro hv w hw
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hw j)
    exact (algebraMap_range_mem_iff_isIntegral _).2 (((algebraMap_range_mem_iff_isIntegral _).1 (hv j)).map
      ((IsCMField.complexConj E).toRingEquiv : E →+* E).toIntAlgHom)
  · intro h j
    have hs : ∀ i, (Pi.single j (1 : E) : Fin n → E) i ∈ (algebraMap (𝓞 E) E).range := by
      intro i
      rw [Pi.single_apply]
      split_ifs
      exacts [Subring.one_mem _, Subring.zero_mem _]
    have h1 := h (Pi.single j 1) hs
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h1
    have h2 := ((algebraMap_range_mem_iff_isIntegral _).1 h1).map
      ((IsCMField.complexConj E).toRingEquiv : E →+* E).toIntAlgHom
    exact (algebraMap_range_mem_iff_isIntegral _).2 (by simpa using h2)

theorem trivAt_std (n k : ℕ) : GenLat.TrivAt (⟨stdLat E n⟩ : GenLat E n) k := by
  exact ⟨1, Nat.coprime_one_left _, Submodule.smul_le_right, Submodule.smul_le_right⟩

end GlobalTheory.Survey.StandardLatticeGoodPlace
