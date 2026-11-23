import Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisFC

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

instance isModTopAE : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

instance topRingAE : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

abbrev bA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    Module.Basis (Fin (Module.finrank F E)) (AF F) (AF F ⊗[F] E) :=
  Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)

def cE (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    (AF F ⊗[F] E) ≃L[AF F] (Fin (Module.finrank F E) → AF F) :=
  { (bA F E).equivFun with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (bA F E).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (bA F E).equivFun.symm.toLinearMap }

theorem cE_tmul (e : E) (k : Fin (Module.finrank F E)) :
    cE F E ((1 : AF F) ⊗ₜ[F] e) k = algebraMap F (AF F) ((Module.finBasis F E).repr e k) := by
  change (bA F E).equivFun ((1 : AF F) ⊗ₜ[F] e) k = _
  rw [Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

instance lcAE : LocallyCompactSpace (AF F ⊗[F] E) :=
  (cE F E).toHomeomorph.isClosedEmbedding.locallyCompactSpace

instance t2AE : T2Space (AF F ⊗[F] E) :=
  T2Space.of_injective_continuous (cE F E).injective (cE F E).continuous

end Tens

section D7

variable {D : D7}

abbrev nE (D : D7) : ℕ := Module.finrank D.host.F D.host.E

def Phi (V W : HSp D) (x : WA V W) : Fin V.rank → Fin W.rank → Fin (nE D) → AF D.host.F :=
  fun i j => cE D.host.F D.host.E (x i j)

theorem Phi_add (V W : HSp D) (x y : WA V W) (i j k) : Phi V W (x + y) i j k = Phi V W x i j k + Phi V W y i j k := by
  simp only [Phi, Matrix.add_apply, map_add, Pi.add_apply]

theorem Phi_rat (V W : HSp D) (e : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (i j k) :
    Phi V W (e.map (incA D)) i j k = algebraMap D.host.F (AF D.host.F) ((Module.finBasis D.host.F D.host.E).repr (e i j) k) := by
  exact cE_tmul (e i j) k

theorem cont_Phi (V W : HSp D) (i j k) : Continuous fun x : WA V W => Phi V W x i j k := by
  unfold Phi
  exact (continuous_apply k).comp ((cE D.host.F D.host.E).continuous.comp
    ((continuous_apply j).comp (continuous_apply i)))

def FD (V W : HSp D) : Set (WA V W) := {x | ∀ i j k, Phi V W x i j k ∈ F0 D.host.F}

theorem exU (V W : HSp D) (x : WA V W) : ∃! g : ratL V W, g +ᵥ x ∈ FD V W := by
  classical
  choose q hq using fun i j k => PHeisFC.ad_exU (F := D.host.F) (Phi V W x i j k)
  let b := Module.finBasis D.host.F D.host.E
  let e : Matrix (Fin V.rank) (Fin W.rank) D.host.E := fun i j => b.equivFun.symm (q i j)
  have hrep : ∀ i j k, b.repr (e i j) k = q i j k := by
    intro i j k
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]

  have hshift : ∀ (e' : Matrix (Fin V.rank) (Fin W.rank) D.host.E) i j k,
      Phi V W (e'.map (incA D) + x) i j k =
        algebraMap D.host.F (AF D.host.F) (b.repr (e' i j) k) + Phi V W x i j k := by
    intro e' i j k
    rw [Phi_add, Phi_rat]
  refine ⟨⟨e.map (incA D), ⟨e, rfl⟩⟩, ?_, ?_⟩
  · intro i j k
    show Phi V W (e.map (incA D) + x) i j k ∈ F0 D.host.F
    rw [hshift, hrep]
    exact (hq i j k).1
  · rintro ⟨g, e', rfl⟩ hg
    apply Subtype.ext
    show e'.map (incA D) = e.map (incA D)
    have he : e' = e := by
      ext i j
      refine b.ext_elem fun k => ?_
      rw [hrep]
      have h1 := hg i j k
      change Phi V W (e'.map (incA D) + x) i j k ∈ F0 D.host.F at h1
      rw [hshift] at h1
      exact (hq i j k).2 _ h1
    rw [he]

instance borelWA (V W : HSp D) : BorelSpace (WA V W) := ⟨rfl⟩

open scoped Classical in
theorem meas_FD (V W : HSp D) : MeasurableSet (FD V W) := by
  classical
  have heM : Continuous (eM D.host.F) := by
    rw [show (⇑(eM D.host.F)) = _ from funext (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply D.host.F)]
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp
        (continuous_apply _)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp
        (continuous_apply _)
  have hset : FD V W = ⋂ i, ⋂ j, ⋂ k,
      ((fun x => eM D.host.F (Phi V W x i j k).1) ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis D.host.F) ∩
        (fun x => (Phi V W x i j k).2) ⁻¹' Ohat D.host.F) := by
    ext x
    simp [FD, F0, Pinf, Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff]
  rw [hset]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => ?_
  refine MeasurableSet.inter ?_ ?_
  · exact (heM.comp (continuous_fst.comp (cont_Phi V W i j k))).measurable (measurableSet_Pinf D.host.F)
  · exact ((isOpen_Ohat D.host.F).preimage (continuous_snd.comp (cont_Phi V W i j k))).measurableSet

theorem FD_sub_compact (V W : HSp D) : ∃ K : Set (WA V W), IsCompact K ∧ FD V W ⊆ K := by
  obtain ⟨K0, hK0, hF0⟩ := fundamental_set_subset_compact (F := D.host.F)
  let g : (Fin V.rank → Fin W.rank → Fin (nE D) → AF D.host.F) → WA V W :=
    fun φ i j => (cE D.host.F D.host.E).symm (φ i j)
  have hg : Continuous g :=
    continuous_pi fun i => continuous_pi fun j =>
      (cE D.host.F D.host.E).symm.continuous.comp ((continuous_apply j).comp (continuous_apply i))
  refine ⟨g '' Set.univ.pi (fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => K0), ?_, ?_⟩
  · exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK0).image hg
  · intro x hx
    refine ⟨fun i j => cE D.host.F D.host.E (x i j), ?_, ?_⟩
    · intro i _ j _ k _
      exact hF0 (hx i j k)
    · funext i j
      exact (cE D.host.F D.host.E).symm_apply_apply (x i j)

instance tagWA (V W : HSp D) : IsTopologicalAddGroup (WA V W) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin V.rank → Fin W.rank → AE D))

instance lcWA (V W : HSp D) : LocallyCompactSpace (WA V W) :=
  inferInstanceAs (LocallyCompactSpace (Fin V.rank → Fin W.rank → AE D))

instance t2WA (V W : HSp D) : T2Space (WA V W) :=
  inferInstanceAs (T2Space (Fin V.rank → Fin W.rank → AE D))

instance measAddWA (V W : HSp D) : MeasurableAdd (WA V W) :=
  ⟨fun _ => (continuous_const.add continuous_id).measurable, fun _ => (continuous_id.add continuous_const).measurable⟩

theorem countable_ratL (V W : HSp D) : Countable (ratL V W) := by
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin V.rank) (Fin W.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin W.rank → D.host.E))
  have h : (ratL V W : Set (WA V W)).Countable := by
    unfold ratL
    rw [AddMonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem finCovol {D : D7} (V W : HSp D) : Formalism.IndefR.Heis.FinCovol V W := by
  haveI := countable_ratL V W
  obtain ⟨K, hK, hFK⟩ := FD_sub_compact V W
  have hfd : ∀ μ : Measure (WA V W), IsAddFundamentalDomain (ratL V W) (FD V W) μ :=
    fun μ => IsAddFundamentalDomain.mk' (meas_FD V W).nullMeasurableSet (exU V W)
  refine ⟨⟨Measure.addHaar, FD V W, inferInstance, hfd _⟩, fun μ 𝓕 hμ h𝓕 => ?_⟩
  rw [h𝓕.measure_eq (hfd μ)]
  exact (measure_mono hFK).trans_lt hK.measure_lt_top

end D7

end Formalism.IndefR.PHeisFC

end
