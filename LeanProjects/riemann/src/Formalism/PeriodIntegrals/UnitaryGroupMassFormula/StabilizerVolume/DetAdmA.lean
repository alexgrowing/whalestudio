import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuInvSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoPolish

noncomputable section

namespace PI.VolStabS.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabS.PositiveNearLattice MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct

section Borel

variable {F : Type} [Field F] [NumberField F]

instance borel_Ainf : BorelSpace (Ainf F) := ⟨rfl⟩
instance borel_Af : BorelSpace (Af F) := ⟨rfl⟩
instance borel_AF : BorelSpace (AF F) := ⟨rfl⟩
instance borel_Fv (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (Fv F v) := ⟨rfl⟩
instance borel_tens {E : Type} [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : BorelSpace (R ⊗[F] E) := ⟨rfl⟩

end Borel

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isCompact_intV : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
  ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v

theorem isClopen_intV : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) := by
  exact Valued.isClopen_valuationSubring _

instance lc_Fv : LocallyCompactSpace (Fv F v) :=
  (isCompact_intV v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isClopen_intV v).isOpen.mem_nhds (zero_mem (v.adicCompletionIntegers F)))

theorem isClopen_translate (t : Fv F v) :
    IsClopen ((Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) := by
  exact (isClopen_intV v).preimage (Homeomorph.subRight t).continuous

theorem isCompact_translate (t : Fv F v) :
    IsCompact ((Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) := by
  exact (Homeomorph.subRight t).isCompact_preimage.mpr (isCompact_intV v)

theorem mem_translate (t : Fv F v) :
    t ∈ (Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  simp

theorem exists_cc {W : Set (Fv F v)} (hW : IsOpen W) {t : Fv F v} (ht : t ∈ W) :
    ∃ C, IsClopen C ∧ IsCompact C ∧ t ∈ C ∧ C ⊆ W := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 (hW.mem_nhds ht)
  have hB : IsClopen ((Homeomorph.subRight t) ⁻¹' {x : Fv F v | Valued.v.restrict x < (γ : _)}) :=
    (Valued.isClopen_ball _ _).preimage (Homeomorph.subRight t).continuous
  refine ⟨(Homeomorph.subRight t) ⁻¹' {x : Fv F v | Valued.v.restrict x < (γ : _)} ∩
      (Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)),
    hB.inter (isClopen_translate v t), (isCompact_translate v t).inter_left hB.isClosed,
    ⟨?_, mem_translate v t⟩, fun y hy => hγ hy.1⟩
  show Valued.v.restrict (t - t) < (γ : _)
  rw [sub_self, map_zero]
  exact zero_lt_iff.2 (Units.ne_zero γ)

theorem open_eq_sUnion {W : Set (Fv F v)} (hW : IsOpen W) :
    ∃ T : Set (Set (Fv F v)), T.Countable ∧ (∀ C ∈ T, IsClopen C ∧ IsCompact C) ∧ W = ⋃₀ T := by
  obtain ⟨T, hT, he⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : {C : Set (Fv F v) // IsClopen C ∧ IsCompact C ∧ C ⊆ W} => (i.1 : Set (Fv F v)))
    fun i => i.2.1.isOpen
  refine ⟨Subtype.val '' T, hT.image _, ?_, ?_⟩
  · rintro _ ⟨i, -, rfl⟩
    exact ⟨i.2.1, i.2.2.1⟩
  · rw [sUnion_image, he]
    ext t
    constructor
    · intro ht
      obtain ⟨C, h1, h2, h3, h4⟩ := exists_cc v hW ht
      exact mem_iUnion.2 ⟨⟨C, h1, h2, h4⟩, h3⟩
    · intro ht
      obtain ⟨i, hi⟩ := mem_iUnion.1 ht
      exact i.2.2.2 hi

end Local

section Box1

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_finite_adele_box {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hc : ∀ v, IsCompact (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsCompact {x : Af F | ∀ v, x v ∈ D v} := by
  classical
  set S' : Set (HeightOneSpectrum (𝓞 F)) := {v | D v = (v.adicCompletionIntegers F : Set (Fv F v))} with hS'
  have hS : Filter.cofinite ≤ Filter.principal S' := Filter.le_principal_iff.2 hf
  have hBY : IsCompact {y : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => Fv F v)
      (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (Filter.principal S') | ∀ v, y v ∈ D v} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have e : (DFunLike.coe '' {y : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => Fv F v)
        (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (Filter.principal S') | ∀ v, y v ∈ D v}) =
        Set.pi Set.univ D := by
      ext f
      constructor
      · rintro ⟨y, hy, rfl⟩ v _
        exact hy v
      · intro hf'
        refine ⟨⟨f, Filter.eventually_principal.2 (fun v hv => ?_)⟩, fun v => hf' v (Set.mem_univ _), rfl⟩
        have h1 := hf' v (Set.mem_univ _)
        rw [show D v = _ from hv] at h1
        exact h1
    rw [e]
    exact isCompact_univ_pi hc
  have himg : {x : Af F | ∀ v, x v ∈ D v} = RestrictedProduct.inclusion _ _ hS ''
      {y : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => Fv F v)
        (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (Filter.principal S') | ∀ v, y v ∈ D v} := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x.1, Filter.eventually_principal.2 (fun v hv => ?_)⟩, fun v => hx v, rfl⟩
      have h1 := hx v
      rw [show D v = _ from hv] at h1
      exact h1
    · rintro ⟨y, hy, rfl⟩ v
      exact hy v
  rw [himg]
  exact hBY.image (RestrictedProduct.continuous_inclusion hS)

theorem isOpen_finite_adele_box {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (ho : ∀ v, IsOpen (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsOpen {x : Af F | ∀ v, x v ∈ D v} := by
  classical
  have hSfin : {v : HeightOneSpectrum (𝓞 F) | ¬ (D v = (v.adicCompletionIntegers F : Set (Fv F v)))}.Finite :=
    Filter.eventually_cofinite.1 hf
  have e : {x : Af F | ∀ v, x v ∈ D v} = (⋂ v ∈ hSfin.toFinset, {x : Af F | x v ∈ D v}) ∩
      {x : Af F | ∀ v, v ∉ hSfin.toFinset → x v ∈ (v.adicCompletionIntegers F : Set (Fv F v))} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.Finite.mem_toFinset]
    constructor
    · intro h
      refine ⟨fun v _ => h v, fun v hv => ?_⟩
      have hv' : D v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
        by_contra hc
        exact hv hc
      rw [← hv']
      exact h v
    · rintro ⟨h1, h2⟩ v
      by_cases hv : D v = (v.adicCompletionIntegers F : Set (Fv F v))
      · rw [hv]
        exact h2 v (fun hc => hc hv)
      · exact h1 v hv
  rw [e]
  refine IsOpen.inter (isOpen_biInter_finset (fun v _ => (ho v).preimage (RestrictedProduct.continuous_eval v))) ?_
  exact RestrictedProduct.isOpen_forall_imp_mem (fun v => (isClopen_intV v).isOpen)

end Box1

end PI.VolStabS.DeterminantAdmissible
