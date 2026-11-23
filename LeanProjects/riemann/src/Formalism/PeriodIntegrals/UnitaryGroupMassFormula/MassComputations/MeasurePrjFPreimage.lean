import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.BcTensMapInclR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Set
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal Pointwise Matrix

namespace MassDataMassesW

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r)

def prjF : Hsub (AF F) σ J P →* Hsub (Af F) σ J P :=
  ((haMap σ J (sndA F)).comp (Hsub (AF F) σ J P).subtype).codRestrict (Hsub (Af F) σ J P)
    (fun g => haMap_stabT σ J (sndA F) (tupH P) g g.2)

theorem prjF_val (g : Hsub (AF F) σ J P) :
    ((prjF σ J P g : Hsub (Af F) σ J P) : HA (Af F) σ J) = (splitA σ J (g : HA (AF F) σ J)).2 := rfl

theorem nonempty_hos (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨p, hp0, hp⟩ :=
    Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  exact ⟨⟨p, hp, hp0⟩⟩

theorem nontrivial_Af (F : Type) [Field F] [NumberField F] : Nontrivial (Af F) := by
  first
  | exact inferInstance
  | (obtain ⟨v⟩ := nonempty_hos F
     refine ⟨⟨0, 1, fun h => ?_⟩⟩
     have h2 : Subtype.val (0 : Af F) v = Subtype.val (1 : Af F) v := by rw [h]
     have h0 : Subtype.val (0 : Af F) v = 0 := by first | rfl | simp
     have h1 : Subtype.val (1 : Af F) v = 1 := by first | rfl | simp
     exact zero_ne_one (h0.symm.trans (h2.trans h1)))

theorem inj_Af (F : Type) [Field F] [NumberField F] : Function.Injective (algebraMap F (Af F)) := by
  haveI := nontrivial_Af F
  exact (algebraMap F (Af F)).injective

theorem inclR_injective (R : Type) [CommRing R] [Algebra F R] (h : Function.Injective (algebraMap F R)) :
    Function.Injective (inclR (F := F) (E := E) R) := by
  intro x y hxy
  have key : ∀ e : E, inclR (F := F) (E := E) R e =
      ((Algebra.linearMap F R).rTensor E) ((TensorProduct.lid F E).symm e) := by
    intro e
    simp [inclR, Algebra.TensorProduct.includeRight_apply]
  have hinj : Function.Injective ((Algebra.linearMap F R).rTensor E) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := E) _ (by exact h)
  rw [key, key] at hxy
  exact (TensorProduct.lid F E).symm.injective (hinj hxy)

private theorem actTup_bc (R : Type) [CommRing R] [Algebra F R] (u : GL (Fin n) E) {a : ℕ}
    (X : Fin a → Fin n → E) :
    actTup R (Formalism.UG.bc (inclR (F := F) (E := E) R) u) (ratTup (F := F) R X) =
      ratTup (F := F) R (fun b => (u : Matrix (Fin n) (Fin n) E).mulVec (X b)) := by
  funext b i
  first
  | simp [actTup, ratTup, Formalism.UG.bc, Matrix.mulVec, dotProduct, map_sum]
  | simp [actTup, ratTup, Formalism.UG.bc, Matrix.mulVec, Matrix.dotProduct, map_sum]

theorem prjF_map_ratOf :
    (ratOf (K := Hsub (AF F) σ J P)).map (prjF σ J P) =
      (HFinIn (Af F) σ J : Subgroup (HA (Af F) σ J)).subgroupOf (Hsub (Af F) σ J P) := by
  ext δ
  constructor
  · intro hδ
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hδ
    have hmem : HA.mat (AF F) σ J (γ : HA (AF F) σ J) ∈ HFin (AF F) σ J := hγ
    obtain ⟨u, hu, hγu⟩ := Subgroup.mem_map.mp hmem
    show HA.mat (Af F) σ J (prjF σ J P γ : HA (Af F) σ J) ∈ HFin (Af F) σ J
    refine Subgroup.mem_map.mpr ⟨u, hu, ?_⟩
    show Formalism.UG.bc (inclR (F := F) (E := E) (Af F)) u =
      Formalism.UG.bc (tensMap (E := E) (sndA F)) (HA.mat (AF F) σ J (γ : HA (AF F) σ J))
    rw [← hγu]
    ext i j
    simp [Formalism.UG.bc, tensMap_inclR]
  · intro hδ
    have hmem : HA.mat (Af F) σ J (δ : HA (Af F) σ J) ∈ HFin (Af F) σ J := hδ
    obtain ⟨u, hu, hδu⟩ := Subgroup.mem_map.mp hmem
    have hcomm : (inclR (F := F) (E := E) (AF F)).comp (σ : E →+* E) =
        (sigR (AF F) σ).comp (inclR (F := F) (E := E) (AF F)) := by
      ext e
      simp [inclR, sigR]
    have hHR : Formalism.UG.bc (inclR (F := F) (E := E) (AF F)) u ∈ HR (AF F) σ J :=
      Formalism.UG.P.bc_mem _ _ _ hcomm J u hu
    let g : HA (AF F) σ J := ⟨_, hHR⟩
    have hX : (fun b => (u : Matrix (Fin n) (Fin n) E).mulVec (tupH P b)) = tupH P := by
      have hst : actTup (Af F) (HA.mat (Af F) σ J (δ : HA (Af F) σ J))
          (ratTup (F := F) (Af F) (tupH P)) = ratTup (F := F) (Af F) (tupH P) := δ.2
      rw [← hδu, actTup_bc] at hst
      funext b i
      have := congrFun (congrFun hst b) i
      first
      | exact inclR_injective (E := E) (Af F) (inj_Af F) this
      | exact inclR_injective (E := E) (Af F) (inj_Af F) (by simpa [ratTup] using this)
    have hg : g ∈ Hsub (AF F) σ J P := by
      show actTup (AF F) (Formalism.UG.bc (inclR (F := F) (E := E) (AF F)) u)
        (ratTup (F := F) (AF F) (tupH P)) = ratTup (F := F) (AF F) (tupH P)
      rw [actTup_bc, hX]
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩, ?_, ?_⟩
    · show HA.mat (AF F) σ J g ∈ HFin (AF F) σ J
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    · apply Subtype.ext
      apply Subtype.ext
      show Formalism.UG.bc (tensMap (E := E) (sndA F)) (Formalism.UG.bc (inclR (F := F) (E := E) (AF F)) u) =
        HA.mat (Af F) σ J (δ : HA (Af F) σ J)
      rw [← hδu]
      ext i j
      simp [Formalism.UG.bc, tensMap_inclR]

theorem prjF_inj (γ : Hsub (AF F) σ J P) (hγ : γ ∈ ratOf (K := Hsub (AF F) σ J P))
    (h1 : prjF σ J P γ = 1) : γ = 1 := by
  have hmem : HA.mat (AF F) σ J (γ : HA (AF F) σ J) ∈ HFin (AF F) σ J := hγ
  obtain ⟨u, -, hγu⟩ := Subgroup.mem_map.mp hmem
  have hh : Formalism.UG.bc (tensMap (E := E) (sndA F)) (HA.mat (AF F) σ J (γ : HA (AF F) σ J)) = 1 := by
    have := congrArg (fun x : Hsub (Af F) σ J P => HA.mat (Af F) σ J (x : HA (Af F) σ J)) h1
    exact this
  have hcomp : Formalism.UG.bc (inclR (F := F) (E := E) (Af F)) u =
      Formalism.UG.bc (tensMap (E := E) (sndA F)) (Formalism.UG.bc (inclR (F := F) (E := E) (AF F)) u) := by
    ext i j
    simp [Formalism.UG.bc, tensMap_inclR]
  have hb : Formalism.UG.bc (inclR (F := F) (E := E) (Af F)) u = 1 := by
    rw [hcomp, hγu]
    exact hh
  have hu1 : u = 1 := by
    ext i j
    apply inclR_injective (E := E) (Af F) (inj_Af F)
    have := congrArg (fun g : GL (Fin n) (Af F ⊗[F] E) => (Units.val g) i j) hb
    simpa [Formalism.UG.bc, Matrix.one_apply, apply_ite] using this
  apply Subtype.ext
  apply Subtype.ext
  show HA.mat (AF F) σ J (γ : HA (AF F) σ J) = 1
  rw [← hγu, hu1, map_one]

variable [FiniteDimensional F E]

theorem continuous_prjF : Continuous (prjF σ J P) := by
  have hs : Continuous (sndA F) := by
    first
    | exact continuous_snd
    | (simp only [sndA]; exact continuous_snd)
    | fun_prop
  have hm := continuous_haMap (σ := σ) (J := J) (sndA F) hs
  exact continuous_induced_rng.2 (hm.comp continuous_subtype_val)

theorem continuous_splitA_u : Continuous (splitA σ J) := by
  have hs : Continuous (sndA F) := by
    first
    | exact continuous_snd
    | (simp only [sndA]; exact continuous_snd)
    | fun_prop
  have hf : Continuous (fstA F) := by
    first
    | exact continuous_fst
    | (simp only [fstA]; exact continuous_fst)
    | fun_prop
  have h1 := continuous_haMap (σ := σ) (J := J) (fstA F) hf
  have h2 := continuous_haMap (σ := σ) (J := J) (sndA F) hs
  first
  | exact h1.prodMk h2
  | exact h1.prod_mk h2

theorem isClosed_stabT' (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R] {a : ℕ} (X0 : Fin a → Fin n → E) :
    IsClosed ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) := by
  have hmat : Continuous (fun g : HA R σ J => (HA.mat R σ J g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous (fun g : HA R σ J => actTup R (HA.mat R σ J g) (ratTup (F := F) R X0)) := by
    unfold actTup
    refine continuous_pi fun b => ?_
    refine continuous_pi fun i => ?_
    first
    | simp only [Matrix.mulVec, dotProduct]
    | simp only [Matrix.mulVec, Matrix.dotProduct]
    refine continuous_finset_sum _ fun j _ => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp hmat)).mul continuous_const
  have hset : ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) =
      {g | actTup R (HA.mat R σ J g) (ratTup (F := F) R X0) = ratTup (F := F) R X0} := by
    ext g
    exact Iff.rfl
  rw [hset]
  exact isClosed_eq hc continuous_const

theorem measure_prjF_preimage (M : MeasW σ J P) (hM : M.IsTextNorm) (S : Set (Hsub (Af F) σ J P))
    (hS : MeasurableSet S) : M.μH (prjF σ J P ⁻¹' S) = M.μHinf univ * M.μHf S := by
  have hcl : IsClosed ((Hsub (Af F) σ J P : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) :=
    isClosed_stabT' σ J (Af F) (tupH P)
  have hHf : MeasurableSet ((Hsub (Af F) σ J P : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) :=
    hcl.measurableSet
  haveI : SecondCountableTopology (HA (Af F) σ J) := PI.VolStabSW.TopoAF.secondCountable_HA_of (Af F) σ J
  haveI : LocallyCompactSpace (Hsub (Af F) σ J P) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := hM.2.2.1
  haveI : SecondCountableTopology (Hsub (Af F) σ J P) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (Hsub (Af F) σ J P) := inferInstance
  haveI : SigmaFinite M.μHf := inferInstance
  have hmeas : Measurable (splitA σ J) := (continuous_splitA_u σ J).measurable
  let T : Set (HA (Ainf F) σ J × HA (Af F) σ J) := univ ×ˢ (Subtype.val '' S)
  have hT : MeasurableSet T := MeasurableSet.univ.prod (hHf.subtype_image hS)
  have hpre : prjF σ J P ⁻¹' S = Subtype.val ⁻¹' (splitA σ J ⁻¹' T) := by
    ext g
    constructor
    · intro h
      exact ⟨trivial, prjF σ J P g, h, rfl⟩
    · rintro ⟨-, s, hs, hse⟩
      have : s = prjF σ J P g := Subtype.ext hse
      show prjF σ J P g ∈ S
      rwa [← this]
  rw [hpre, ← Measure.map_apply measurable_subtype_coe (hmeas hT), ← Measure.map_apply hmeas hT,
    hM.2.2.2.2.2.2.2.2.1, Measure.prod_prod]
  have hIm : MeasurableSet (Subtype.val '' S : Set (HA (Af F) σ J)) := hHf.subtype_image hS
  have e1 : (amb M.μHinf) univ = M.μHinf univ := by
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]
  have e2 : (amb M.μHf) (Subtype.val '' S) = M.μHf S := by
    rw [Measure.map_apply measurable_subtype_coe hIm, Subtype.val_injective.preimage_image]
  rw [e1, e2]

theorem massUnfold_gen [NumberField E] (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (M : MeasW σ J P)
    (hM : M.IsTextNorm) (U : Subgroup (Hsub (Af F) σ J P)) (hU : MeasurableSet (U : Set (Hsub (Af F) σ J P)))
    (hfin : Formalism.L2.SG.TypedSets.MassFinite (G := ↥(Hsub (Af F) σ J P)) ((HFinIn (Af F) σ J : Subgroup (HA (Af F) σ J)).subgroupOf (Hsub (Af F) σ J P)) U)
    (𝓕 : Set (Hsub (AF F) σ J P)) (h𝓕 : IsFundamentalDomain (ratOf (K := Hsub (AF F) σ J P)) 𝓕 M.μH) :
    M.μH 𝓕 = M.μHinf univ * M.μHf U *
      ENNReal.ofReal (Formalism.L2.SG.TypedSets.massCl (G := ↥(Hsub (Af F) σ J P)) ((HFinIn (Af F) σ J : Subgroup (HA (Af F) σ J)).subgroupOf (Hsub (Af F) σ J P)) U) := by
  haveI : Countable (HFinIn (AF F) σ J) :=
    ((PI.VolSemiDirect.W.discHA_of PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds) F E σ hCM n J hJ).1
  haveI : Countable (ratOf (K := Hsub (AF F) σ J P)) := by
    let f : ratOf (K := Hsub (AF F) σ J P) → HFinIn (AF F) σ J := fun x =>
      ⟨((x : Hsub (AF F) σ J P) : HA (AF F) σ J), Subgroup.mem_comap.1 x.2⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      have e := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext e)
    exact hinj.countable
  haveI := hM.1
  haveI := hM.2.2.1
  exact Abs.unfold_mass h𝓕 (prjF σ J P) (continuous_prjF σ J P).measurable _ U (prjF_map_ratOf σ J P)
    (prjF_inj σ J P) hU hfin _ (fun x => by
      rw [measure_prjF_preimage σ J P M hM _ (Abs.meas_smul_set hU x), measure_smul])

end Gen

end MassDataMassesW
