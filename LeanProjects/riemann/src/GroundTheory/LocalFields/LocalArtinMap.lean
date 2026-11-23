import Mathlib
import GroundTheory.LocalFields.MaximalAbelianExtension
import GroundTheory.LocalFields.LocalReciprocityUniversal
import GroundTheory.LocalFields.Existence

noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel GroundTheory.LocalField.FormalGroup

theorem continuous_of_isOpen_ker {G D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group D] [TopologicalSpace D] [DiscreteTopology D] (f : G →* D)
    (hf : IsOpen (f.ker : Set G)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one, nhds_discrete D, Filter.tendsto_pure]
  exact Filter.mem_of_superset (hf.mem_nhds f.ker.one_mem) fun x hx => hx

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Def

variable (K Ω) in

def localArtinMap :
    Kˣ →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  (topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom.comp (localReciprocityLimit K Ω)

theorem localArtinMap_apply (x : Kˣ) :
    localArtinMap K Ω x = topologicalAbelianizationEquiv K Ω (localReciprocityLimit K Ω x) :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem restrictAb_topologicalAbelianizationEquiv_eq_abelianRestrict (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsAbelianGalois K L] (g : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :
    restrictAb L (le_maximalAbelianExtension L) (topologicalAbelianizationEquiv K Ω g) =
      abelianRestrict L g := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  rw [restrictAb_topologicalAbelianizationEquiv]
  rfl

theorem restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] (x : Kˣ) :
    restrictAb L (le_maximalAbelianExtension L) (localArtinMap K Ω x) =
      (localReciprocityAbelian L).symm (x : Kˣ ⧸ (normUnits K L).range) := by
  rw [localArtinMap_apply, restrictAb_topologicalAbelianizationEquiv_eq_abelianRestrict,
    abelianRestrict_localReciprocityLimit]

theorem ker_restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)).ker =
      (normUnits K L).range := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, restrictAb_localArtinMap, MulEquiv.map_eq_one_iff,
    QuotientGroup.eq_one_iff]

theorem surjective_restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    Function.Surjective ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)) := by
  intro σ
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (localReciprocityAbelian L σ)
  refine ⟨x, ?_⟩
  rw [MonoidHom.comp_apply, restrictAb_localArtinMap, hx, MulEquiv.symm_apply_apply]

end Def

section Unramified

instance isAbelianGalois_maximalUnramifiedExtension :
    IsAbelianGalois K (maximalUnramifiedExtension K Ω) :=
  { toIsMulCommutative := ⟨⟨fun σ τ => (maximalUnramifiedExtensionGaloisEquiv K Ω).injective (by
      rw [map_mul, map_mul, mul_comm])⟩⟩ }

theorem maximalUnramifiedExtension_le_maximalAbelianExtension :
    maximalUnramifiedExtension K Ω ≤ maximalAbelianExtension K Ω :=
  le_maximalAbelianExtension _

theorem restrictAb_localArtinMap_uniformizer {π : Kˣ} (hπ : ord (π : K) = 1) :
    restrictAb (maximalUnramifiedExtension K Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
      (localArtinMap K Ω π) = maximalUnramifiedExtensionFrobenius K Ω := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (localReciprocityLimit K Ω π)
  rw [localArtinMap_apply, ← hg, restrictAb_topologicalAbelianizationEquiv]
  exact restrictNormal_eq_frobenius_of_mk_eq_localReciprocityLimit hπ hg

theorem restrictAb_localArtinMap_of_le_maximalUnramifiedExtension (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L] (hL : L ≤ maximalUnramifiedExtension K Ω) (x : Kˣ) :
    restrictAb L (hL.trans maximalUnramifiedExtension_le_maximalAbelianExtension) (localArtinMap K Ω x) =
      unramifiedFrobenius K Ω L ^ ord (x : K) := by
  have := isAbelianGalois_of_le_maximalAbelianExtension L
    (hL.trans maximalUnramifiedExtension_le_maximalAbelianExtension)
  apply (bijective_abelianizationOf L).1
  rw [restrictAb_localArtinMap, of_localReciprocityAbelian_symm,
    localReciprocity_symm_mk_of_le_maximalUnramifiedExtension L hL, map_zpow]

theorem localArtinMap_uniformizer_apply {π : Kˣ} (hπ : ord (π : K) = 1) {y : Ω}
    (hy : y ∈ maximalUnramifiedExtension K Ω) :
    ((localArtinMap K Ω π ⟨y, maximalUnramifiedExtension_le_maximalAbelianExtension hy⟩ :
      maximalAbelianExtension K Ω) : Ω) =
      (maximalUnramifiedExtensionFrobenius K Ω ⟨y, hy⟩ : Ω) := by
  rw [← restrictAb_localArtinMap_uniformizer hπ, restrictAb_apply]

end Unramified

section Topology

theorem continuous_localArtinMap : Continuous (localArtinMap K Ω) := by
  rw [continuous_iff_restrictAb]
  intro L _ _
  refine continuous_of_isOpen_ker ((restrictAb L (le_maximalAbelianExtension L)).comp
    (localArtinMap K Ω)) ?_
  rw [ker_restrictAb_localArtinMap]
  exact (isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L).1

end Topology

section Injective

theorem eq_one_of_forall_mem_unitFiltration {u : 𝒪[K]ˣ}
    (h : ∀ n, 1 ≤ n → u ∈ unitFiltration K n) : u = 1 := by
  have hmem : (u : 𝒪[K]) - 1 ∈ ⨅ n : ℕ, 𝓂[K] ^ n := by
    refine Ideal.mem_iInf.2 fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact h n hn
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top', Ideal.mem_bot, sub_eq_zero] at hmem
  exact Units.ext hmem

theorem injective_localArtinMap : Function.Injective (localArtinMap K Ω) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hker : x ∈ (localReciprocityLimit K Ω).ker := by
    rw [MonoidHom.mem_ker]
    exact (topologicalAbelianizationEquiv K Ω).injective (by rw [map_one]; exact hx)
  rw [ker_localReciprocityLimit, Subgroup.mem_iInf] at hker
  have hnorm : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L], x ∈ (normUnits K L).range :=
    fun L _ => hker ⟨L, inferInstance⟩
  have hopen : ∀ (H : Subgroup Kˣ) [H.FiniteIndex], IsOpen (H : Set Kˣ) → x ∈ H := by
    intro H _ hH
    obtain ⟨L, hL, -, -, hLH⟩ := exists_range_normUnits_eq (Ω := Ω) H hH
    rw [← hLH]
    exact hnorm L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set e := unitsEquivIntProd hπ
  have hk : (e x).1 = 1 := by
    set k := Multiplicative.toAdd (e x).1 with hk
    let f : Kˣ →* Multiplicative (ZMod (k.natAbs + 1)) :=
      (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod (k.natAbs + 1)))).comp
        ((MonoidHom.fst _ _).comp e.toMonoidHom)
    have hfo : IsOpen (f.ker : Set Kˣ) := by
      refine Subgroup.isOpen_mono (H₁ := unitFiltrationUnits K 0) ?_ (isOpen_unitFiltrationUnits 0)
      rintro _ ⟨u, -, rfl⟩
      simp [f, e, unitsEquivIntProd_unitsIncl]
    have hfx := hopen f.ker hfo
    rw [MonoidHom.mem_ker] at hfx
    have h0 : ((k : ℤ) : ZMod (k.natAbs + 1)) = 0 := by
      simpa [f, k] using hfx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have : k = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h0 (by simp only [Int.natAbs_natCast]; omega)
    rw [← ofAdd_toAdd (e x).1, ← hk, this, ofAdd_zero]
  set u := (e x).2
  have hxu : x = unitsIncl K u := by
    apply e.injective
    rw [unitsEquivIntProd_unitsIncl, ← hk]
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hf := isLubinTateSeries_ltPoly π
  have hu : u = 1 := by
    refine eq_one_of_forall_mem_unitFiltration fun n hn => ?_
    refine mem_unitFiltration_of_mem_range_normUnits (Ω := Ω) hπ hf hn u 0 ?_
    rw [unitUniformizerPow_eq, zpow_zero, one_mul, ← hxu]
    exact hnorm _
  rw [hxu, hu, map_one]

end Injective

end GroundTheory.LocalField
