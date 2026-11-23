import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups

namespace GroundTheory.Global

open NumberField IsDedekindDomain

section GroupLemma

variable {G C : Type*} [Group G] [Group C]

theorem index_map_mul_relIndex_ker {f : G →* C} (hf : Function.Surjective f) (W : Subgroup G)
    [W.Normal] : (W.map f).index * W.relIndex f.ker = W.index := by
  rw [Subgroup.index_map, f.range_eq_top_of_surjective hf, Subgroup.index_top, mul_one,
    ← Subgroup.relIndex_sup_left, mul_comm, Subgroup.relIndex_mul_index le_sup_left]

end GroupLemma

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem index_comap_sUnitsToSIdeles (W : Subgroup (sIdeles S)) :
    (W.comap (sUnitsToSIdeles S)).index = W.relIndex (sIdelesToIdeleClassGroup S).ker := by
  rw [Subgroup.index_comap, range_sUnitsToSIdeles]

theorem index_map_mul_index_comap (h : (diagonal K).range ⊔ sIdeles S = ⊤)
    (W : Subgroup (sIdeles S)) :
    (W.map (sIdelesToIdeleClassGroup S)).index * (W.comap (sUnitsToSIdeles S)).index =
      W.index := by
  rw [index_comap_sUnitsToSIdeles]
  exact index_map_mul_relIndex_ker ((sIdelesToIdeleClassGroup_surjective_iff S).2 h) W

end IdeleGroup

end

end GroundTheory.Global
