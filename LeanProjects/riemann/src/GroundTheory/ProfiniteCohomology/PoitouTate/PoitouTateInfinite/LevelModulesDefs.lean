import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.Descent
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.Levels
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecomp
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

theorem isOpen_ker_ρ {k G : Type*} [CommRing k] [Group G] [TopologicalSpace G] (A : Rep k G) [IsDiscreteRep A]
    [Finite A] : IsOpen ((A.ρ.ker : Subgroup G) : Set G) := by
  have e : ((A.ρ.ker : Subgroup G) : Set G) = ⋂ a : A, (stabilizer A.ρ a : Set G) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter]
    constructor
    · intro h a
      change A.ρ g a = a
      rw [h, Module.End.one_apply]
    · intro h
      exact LinearMap.ext fun a => h a
  rw [e]
  exact isOpen_iInter_of_finite fun a => isOpen_stabilizer A a

theorem finite_setOf_natCast_mem {N : ℕ} (hN : N ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K.1) | ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((N : ℕ) : 𝓞 K.1)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  change v.asIdeal ∣ Ideal.span {((N : ℕ) : 𝓞 K.1)}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem isLevelModule_mono {T T' : Set (HeightOneSpectrum (𝓞 K.1))} {h : T ⊆ S}
    {M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)}
    (hM : ∀ g, gsResCont (Ω := ℚ̄) h g = 1 → M.ρ g = 1) (hTT' : T ⊆ T') (h' : T' ⊆ S) :
    ∀ g, gsResCont (Ω := ℚ̄) h' g = 1 → M.ρ g = 1 := fun g hg => hM g (by
  rw [gsResCont_apply] at hg ⊢
  rw [← gsRes_gsRes h' hTT', hg, map_one])

theorem exists_finset_isLevelModule (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    {N : ℕ} (hN : N ≠ 0) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    ∃ T₀ : Finset (HeightOneSpectrum (𝓞 K.1)), ∃ h : (T₀ : Set (HeightOneSpectrum (𝓞 K.1))) ⊆ S,
      (∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ T₀) ∧
        ∀ g, gsResCont (Ω := ℚ̄) h g = 1 → M.ρ g = 1 := by
  obtain ⟨T, hT, hNT, hTS, hker⟩ := exists_finite_ker_gsRes_le (M.ρ.ker : Subgroup _) (isOpen_ker_ρ M)
    (finite_setOf_natCast_mem hN) fun v hv => hS v hv
  refine ⟨hT.toFinset, by rw [Set.Finite.coe_toFinset]; exact hTS, fun v hv => hT.mem_toFinset.2 (hNT hv),
    fun g hg => ?_⟩
  rw [gsResCont_apply] at hg
  have hg' : gsRes (Ω := ℚ̄) hTS g = 1 := by
    rw [← gsRes_gsRes (T := (hT.toFinset : Set _)) (by rw [Set.Finite.coe_toFinset]; exact hTS)
      (by rw [Set.Finite.coe_toFinset]), hg, map_one]
  exact MonoidHom.mem_ker.1 (hker (MonoidHom.mem_ker.2 hg'))

variable {T : Set (HeightOneSpectrum (𝓞 K.1))} (h : T ⊆ S)

theorem gsResCont_surjective : Function.Surjective (gsResCont (Ω := ℚ̄) h) := fun τ => by
  obtain ⟨σ, hσ⟩ := gsRes_surjective (Ω := ℚ̄) h τ
  exact ⟨σ, by rw [gsResCont_apply]; exact hσ⟩

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
  (hM : ∀ g, gsResCont (Ω := ℚ̄) h g = 1 → M.ρ g = 1)

abbrev levelModule : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ T) :=
  descendRep (gsResCont (Ω := ℚ̄) h) (gsResCont_surjective h) M hM

abbrev levelModuleIso : Rep.res (gsResCont (Ω := ℚ̄) h).toMonoidHom (levelModule h M hM) ≅ M :=
  resDescendRepIso (gsResCont (Ω := ℚ̄) h) (gsResCont_surjective h) M hM

theorem isQuotientMap_gsResCont : Topology.IsQuotientMap (gsResCont (Ω := ℚ̄) h) :=
  (gsResCont (Ω := ℚ̄) h).continuous.isClosedMap.isQuotientMap (gsResCont (Ω := ℚ̄) h).continuous
    (gsResCont_surjective h)

instance isDiscreteRep_levelModule [IsDiscreteRep M] : IsDiscreteRep (levelModule h M hM) :=
  isDiscreteRep_descendRep _ (gsResCont_surjective h) M hM (isQuotientMap_gsResCont h)

abbrev levelModuleInfl [IsDiscreteRep M] (r : ℕ) : cohomology (levelModule h M hM) r ⟶ cohomology M r :=
  cohomologyMapAlong (gsResCont (Ω := ℚ̄) h).toMonoidHom (gsResCont (Ω := ℚ̄) h).continuous
    (levelModuleIso h M hM).hom r

end

end GroundTheory.ProfCoh
