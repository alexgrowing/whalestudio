import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.Restrict
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerFrob
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSUnram
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Ramified
import GroundTheory.ArithmeticGeometry.SelmerPairing.Unramified
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Finite

variable {S : Set (HeightOneSpectrum (𝓞 K.1))}

def finitePlaceUnder (E : IntermediateField K.1 ℚ̄) [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 K.1) where
  asIdeal := w.asIdeal.under (𝓞 K.1)
  isPrime := Ideal.IsPrime.under (𝓞 K.1) w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

theorem finitePlaceUnder_eq (E : IntermediateField K.1 ℚ̄) [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    {v : HeightOneSpectrum (𝓞 K.1)} (h : w.asIdeal.LiesOver v.asIdeal) : finitePlaceUnder E w = v :=
  HeightOneSpectrum.ext (Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal)).symm

theorem finite_setOf_ramified_below (E : IntermediateField K.1 ℚ̄) [FiniteDimensional K.1 E] :
    {v : HeightOneSpectrum (𝓞 K.1) | ∃ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal ∧
      w.asIdeal.ramificationIdx (𝓞 K.1) ≠ 1}.Finite := by
  have := NumberField.of_module_finite K.1 E
  refine ((finite_setOf_ramified K.1 E).image (finitePlaceUnder E)).subset ?_
  rintro v ⟨w, hw, he⟩
  exact ⟨w, he, finitePlaceUnder_eq E hw⟩

theorem exists_finite_ker_gsRes_le (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hU : IsOpen (U : Set (galUnramifiedOutside K.1 ℚ̄ S)))
    {T₁ : Set (HeightOneSpectrum (𝓞 K.1))} (hT₁ : T₁.Finite) (hT₁S : T₁ ⊆ S) :
    ∃ T : Set (HeightOneSpectrum (𝓞 K.1)), T.Finite ∧ T₁ ⊆ T ∧
      ∃ hTS : T ⊆ S, (gsRes (Ω := ℚ̄) hTS).ker ≤ U := by
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K.1 (maxUnramifiedOutside K.1 ℚ̄ S)
    (U : Set (galUnramifiedOutside K.1 ℚ̄ S))).1 (hU.mem_nhds U.one_mem)
  let E' : IntermediateField K.1 ℚ̄ := E.map (maxUnramifiedOutside K.1 ℚ̄ S).val
  have hE' : FiniteDimensional K.1 E' :=
    LinearEquiv.finiteDimensional (E.equivMap (maxUnramifiedOutside K.1 ℚ̄ S).val).toLinearEquiv
  set R := {v : HeightOneSpectrum (𝓞 K.1) | ∃ w : HeightOneSpectrum (𝓞 E'),
    w.asIdeal.LiesOver v.asIdeal ∧ w.asIdeal.ramificationIdx (𝓞 K.1) ≠ 1}
  have hR : R.Finite := finite_setOf_ramified_below E'
  have hE'S : E' ≤ maxUnramifiedOutside K.1 ℚ̄ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hE'Sun : IsUnramifiedOutside S E' := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hE'S
  refine ⟨T₁ ∪ (R ∩ S), hT₁.union (hR.inter_of_left S), Set.subset_union_left,
    Set.union_subset hT₁S Set.inter_subset_right, ?_⟩
  have hE'T : IsUnramifiedOutside (T₁ ∪ (R ∩ S)) E' := by
    refine isUnramifiedOutside_of_ramificationIdx_eq_one _ fun v hv w => ?_
    by_cases hvS : v ∈ S
    · by_contra he
      exact hv (Or.inr ⟨⟨w.1, w.2, he⟩, hvS⟩)
    · exact ramificationIdx_eq_one_of_isUnramifiedOutside S hE'Sun hvS w
  have hE'le : E' ≤ maxUnramifiedOutside K.1 ℚ̄ (T₁ ∪ (R ∩ S)) := le_maxUnramifiedOutside _ hE'T
  intro σ hσ
  apply hEU
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hy : (x : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ (T₁ ∪ (R ∩ S)) := hE'le ⟨x, hx, rfl⟩
  have h := (mem_ker_gsRes _ σ).1 hσ ⟨x, hy⟩
  have hx' : (⟨((⟨(x : ℚ̄), hy⟩ : maxUnramifiedOutside K.1 ℚ̄ (T₁ ∪ (R ∩ S))) : ℚ̄),
      maxUnramifiedOutside_mono (Set.union_subset hT₁S Set.inter_subset_right) hy⟩ :
      maxUnramifiedOutside K.1 ℚ̄ S) = x :=
    Subtype.ext rfl
  rw [hx'] at h
  exact h

end Finite

section Unramified

open GroundTheory.LocalField

variable (T : Set (HeightOneSpectrum (𝓞 K.1))) {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

theorem inertiaGroup_le_ker_decompHomS (hv : v ∉ T) :
    inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) ≤
      (decompHomS (v.adicCompletion K.1) T ι).ker := by
  intro g hg
  refine MonoidHom.mem_ker.2 (decompHomS_eq_one_of_unramifiedDegree_eq_one T ι hv g ?_)
  rw [← MonoidHom.mem_ker, ker_unramifiedDegree]
  exact hg

def decompHomSUnram (hv : v ∉ T) :
    Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ⧸
        inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) →ₜ*
      galUnramifiedOutside K.1 ℚ̄ T :=
  ⟨QuotientGroup.lift _ (decompHomS (v.adicCompletion K.1) T ι) (inertiaGroup_le_ker_decompHomS T ι hv),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
      (continuous_decompHomS (Kv := v.adicCompletion K.1) T ι)⟩

theorem decompHomSUnram_mk (hv : v ∉ T) (g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    decompHomSUnram T ι hv (g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ⧸
      inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) =
      decompHomS (v.adicCompletion K.1) T ι g :=
  rfl

variable (v) in

theorem exists_isZHatGenerator_inertia_adicCompletion :
    ∃ σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ⧸
        inertiaGroup (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)),
      IsZHatGenerator σ :=
  GroundTheory.Arith.Selmer.exists_isZHatGenerator_inertia _ _

end Unramified

end

end GroundTheory.ProfCoh
