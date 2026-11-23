import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary

noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

section Gen

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

def Ug (D : PG.Dat A n r) : AddSubgroup (n → A) := (LinearMap.ker D.pW).toAddSubgroup

theorem map_eq_of_sum (D : PG.Dat A n r) (H : D.Hyp) (W : AddSubgroup (n → A))
    (hW : ∀ w, w ∈ W ↔ D.IsW w) (g : (n → A) →ₗ[A] (n → A))
    (hgU : ∀ v, g (D.pU v) = D.pU v)
    (hV : ∀ μ : Measure (n → A), μ.IsAddHaarMeasure → μ.map g = μ)
    (f : W → W) (hf : ∀ w, (f w : n → A) = g w) (μ : Measure W) (hμ : μ.IsAddHaarMeasure) :
    μ.map f = μ := by
  classical
  have hcU : Continuous D.pU := LinearMap.continuous_on_pi _
  have hcW : Continuous D.pW := LinearMap.continuous_on_pi _
  have hcg : Continuous g := LinearMap.continuous_on_pi _
  have hWmem : ∀ w ∈ W, D.pU w = 0 := fun w hw => PG.Dat.pU_of_isW ((hW w).1 hw)
  have hUmem : ∀ u ∈ Ug D, D.pU u = u := fun u hu => by
    have h0 : D.pW u = 0 := hu
    rw [PG.Dat.pW_apply, sub_eq_zero] at h0
    exact h0.symm
  have hWc : IsClosed (W : Set (n → A)) := by
    have : (W : Set (n → A)) = D.pU ⁻¹' {0} := by
      ext w
      simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_singleton_iff]
      refine ⟨fun h => hWmem w h, fun h => (hW w).2 ?_⟩
      have := PG.Dat.isW_pW H w
      rwa [PG.Dat.pW_apply, h, sub_zero] at this
    rw [this]
    exact isClosed_singleton.preimage hcU
  have hUc : IsClosed ((Ug D : AddSubgroup (n → A)) : Set (n → A)) := by
    have : ((Ug D : AddSubgroup (n → A)) : Set (n → A)) = D.pW ⁻¹' {0} := by
      ext v
      simp [Ug]
    rw [this]
    exact isClosed_singleton.preimage hcW
  have : LocallyCompactSpace W := hWc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (Ug D) := hUc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have := hμ
  have : SecondCountableTopology (n → A) := inferInstance
  have : BorelSpace (n → A) := Pi.borelSpace
  have : BorelSpace W := Subtype.borelSpace (· ∈ W)
  have : BorelSpace (Ug D) := Subtype.borelSpace (· ∈ Ug D)
  have : SecondCountableTopology W := TopologicalSpace.secondCountableTopology_induced W (n → A) Subtype.val
  have : SecondCountableTopology (Ug D) :=
    TopologicalSpace.secondCountableTopology_induced (Ug D) (n → A) Subtype.val
  have : BorelSpace (Ug D × W) := Prod.borelSpace
  let Ψ : (Ug D × W) ≃ₜ+ (n → A) :=
    { toFun := fun p => (p.1 : n → A) + (p.2 : n → A)
      invFun := fun v => (⟨D.pU v, by
          show D.pW (D.pU v) = 0
          exact PG.Dat.pW_pU H v⟩, ⟨D.pW v, (hW _).2 (PG.Dat.isW_pW H v)⟩)
      left_inv := by
        rintro ⟨⟨u, hu⟩, ⟨w, hw⟩⟩
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show D.pU (u + w) = u
          rw [map_add, hUmem u hu, hWmem w hw, add_zero]
        · show D.pW (u + w) = w
          rw [PG.Dat.pW_apply, map_add, hUmem u hu, hWmem w hw, add_zero, add_sub_cancel_left]
      right_inv := fun v => by
        show D.pU v + D.pW v = v
        rw [PG.Dat.pW_apply, add_sub_cancel]
      map_add' := by
        rintro ⟨u, w⟩ ⟨u', w'⟩
        show ((u + u' : Ug D) : n → A) + ((w + w' : W) : n → A) = _ + _
        simp only [AddSubgroup.coe_add]
        abel
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun :=
        (hcU.subtype_mk fun v => (show D.pW (D.pU v) = 0 from PG.Dat.pW_pU H v)).prodMk
          (hcW.subtype_mk fun v => (hW _).2 (PG.Dat.isW_pW H v)) }
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  have hΨsm : Measurable Ψ.symm := Ψ.symm.continuous.measurable
  have hgm : Measurable g := hcg.measurable
  have hfc : Continuous f := by
    refine continuous_induced_rng.2 ?_
    have : (Subtype.val ∘ f : W → n → A) = g ∘ Subtype.val := funext hf
    rw [this]
    exact hcg.comp continuous_subtype_val
  have hfm : Measurable f := hfc.measurable
  let μU : Measure (Ug D) := Measure.addHaar
  have : μU.IsAddHaarMeasure := inferInstance
  have : SigmaFinite μU := inferInstance
  have : SigmaFinite μ := inferInstance
  let ρ : Measure (Ug D × W) := μU.prod μ
  have hcomm : (g ∘ Ψ) = Ψ ∘ Prod.map id f := by
    funext p
    obtain ⟨⟨u, hu⟩, w⟩ := p
    show g (u + (w : n → A)) = u + (f w : n → A)
    have := hgU u
    rw [hUmem u hu] at this
    rw [map_add, this, hf]
  have h1 : (ρ.map (Prod.map id f)).map Ψ = ρ.map Ψ := by
    rw [Measure.map_map hΨm (measurable_id.prodMap hfm), ← hcomm, ← Measure.map_map hgm hΨm]
    exact hV _ inferInstance
  have h2 : ρ.map (Prod.map id f) = ρ := by
    have h3 := congrArg (Measure.map Ψ.symm) h1
    have hid : (Ψ.symm ∘ Ψ) = id := funext Ψ.symm_apply_apply
    rwa [Measure.map_map hΨsm hΨm, Measure.map_map hΨsm hΨm, hid, Measure.map_id,
      Measure.map_id] at h3
  have h4 : μU.prod (μ.map f) = μU.prod μ := by
    have h6 := Measure.map_prod_map μU μ measurable_id hfm
    rw [Measure.map_id] at h6
    rw [h6]
    exact h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : Ug D)
  have hpos : μU K ≠ 0 := (Measure.measure_pos_of_mem_nhds μU hK0).ne'
  have hfin : μU K ≠ ⊤ := hK.measure_lt_top.ne
  ext s _
  have h5 : μU K * (μ.map f) s = μU K * μ s := by
    rw [← Measure.prod_prod, ← Measure.prod_prod, h4]
  exact (ENNReal.mul_right_inj hpos hfin).1 h5

end Gen

theorem wMod_of (hV : Cj.VMod) : WMod := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T _ hP h hh μ hμ
  obtain ⟨t1, t2, t3, t4⟩ := Lc.tensor_adele_topology_holds F E
  have := t1
  have := t2
  have := t3
  have := t4
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  let D := datR (AF F) σ J P T
  have H : D.Hyp := datR_hyp (sigma_invol hCM) hJ hP
  have hS := heisenberg_le_stabilizer (AF F) σ J P hh
  have he : ∀ a, lin (AF F) σ J h (D.e a) = D.e a := fun a => stabilizer_fixes_frame_vector (AF F) σ J P hS a
  have hf : ∀ a, lin (AF F) σ J h (D.f a) = D.f a := fun a => by
    have h0 := hh
    rw [Hsub, mem_stabT] at h0
    have h1 := h0 (Fin.natAdd (r + 1) a)
    rwa [tupH_f] at h1
  have hz : lin (AF F) σ J h D.z = D.z := stabilizer_fixes_normal_vector hS
  refine map_eq_of_sum D H (Wsub (AF F) σ J P) (fun w => Iff.rfl) (lin (AF F) σ J h) ?_
    (fun ν hν => hV F E σ hCM M J hJ h ν hν) (actW hh) (fun w => rfl) μ hμ
  intro v
  rw [PG.Dat.pU_apply, PG.Dat.pX_apply, PG.Dat.pXv_apply, PG.Dat.pz_apply]
  simp only [map_add, map_sum, map_smul, he, hf, hz]

end PI.VolSemiDirect.W.Md
