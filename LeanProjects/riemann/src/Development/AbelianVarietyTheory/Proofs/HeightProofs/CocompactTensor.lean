import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicMatrixLattice

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem exists_coords : ∃ (n : ℕ) (e : R ⊗[F] E ≃ₜ (Fin n → R)) (b : E ≃ₗ[F] (Fin n → F)),
    (∀ x y, e (x + y) = e x + e y) ∧ ∀ x i, e (inclR R x) i = algebraMap F R (b x i) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  refine ⟨Module.finrank F E, { e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap },
    (Module.finBasis F E).equivFun, fun x y => e.map_add x y, fun x i => ?_⟩
  change (Algebra.TensorProduct.basis R (Module.finBasis F E)).repr ((1 : R) ⊗ₜ[F] x) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem discrete_tensor (h : ∃ U ∈ nhds (0 : R), ∀ x : F, algebraMap F R x ∈ U → x = 0) :
    ∃ U ∈ nhds (0 : R ⊗[F] E), ∀ x : E, inclR R x ∈ U → x = 0 := by
  obtain ⟨U, hU, hx⟩ := h
  obtain ⟨n, e, b, hadd, hb⟩ := exists_coords (F := F) (E := E) R
  have h0 : e 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => U), ?_, fun x hxU => ?_⟩
  · refine e.continuous.continuousAt.preimage_mem_nhds ?_
    rw [h0]
    exact set_pi_mem_nhds Set.finite_univ fun _ _ => hU
  · refine b.injective ?_
    rw [map_zero]
    funext i
    refine hx _ ?_
    rw [← hb]
    exact hxU i (Set.mem_univ i)

theorem cocompact_tensor
    (h : ∃ K : Set R, IsCompact K ∧ ∀ a : R, ∃ x : F, a - algebraMap F R x ∈ K) :
    ∃ K : Set (R ⊗[F] E), IsCompact K ∧ ∀ a : R ⊗[F] E, ∃ x : E, inclR R x + a ∈ K := by
  obtain ⟨K, hK, hx⟩ := h
  obtain ⟨n, e, b, hadd, hb⟩ := exists_coords (F := F) (E := E) R
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => K), e.isCompact_preimage.2 (isCompact_univ_pi fun _ => hK),
    fun a => ?_⟩
  choose c hc using hx
  refine ⟨b.symm fun i => - c (e a i), fun i _ => ?_⟩
  rw [hadd, Pi.add_apply, hb, b.apply_symm_apply, map_neg, neg_add_eq_sub]
  exact hc _

end Tensor

theorem lattice : ∀ (D : D7) (V W : HSp D), IsTopologicalAddGroup (WA V W) ∧ LocallyCompactSpace (WA V W) ∧ SecondCountableTopology (WA V W) ∧ T2Space (WA V W) ∧ DiscreteTopology (ratL V W) ∧ ∃ K : Set (WA V W), IsCompact K ∧ ∀ x : WA V W, ∃ γ ∈ ratL V W, γ + x ∈ K := by
  intro D V W
  have : LocallyCompactSpace (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E)
    (AF D.host.F)
  have : LocallyCompactSpace (AE D) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AE D) := e.secondCountableTopology
  have : T2Space (AE D) := e.isEmbedding.t2Space
  have hg : IsTopologicalAddGroup (WA V W) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin V.rank → Fin W.rank → AE D))
  refine ⟨hg, inferInstanceAs (LocallyCompactSpace (Fin V.rank → Fin W.rank → AE D)),
    inferInstanceAs (SecondCountableTopology (Fin V.rank → Fin W.rank → AE D)),
    inferInstanceAs (T2Space (Fin V.rank → Fin W.rank → AE D)), ?_, ?_⟩
  · obtain ⟨U, hU, hx⟩ := discrete_tensor (F := D.host.F) (E := D.host.E) (AF D.host.F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero D.host.F)
    have hN : (Set.univ.pi fun _ : Fin V.rank => Set.univ.pi fun _ : Fin W.rank => U) ∈
        nhds (0 : WA V W) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratL V W => (x : WA V W)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, hx⟩ := cocompact_tensor (F := D.host.F) (E := D.host.E) (AF D.host.F)
      (GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F)
    choose c hc using hx
    refine ⟨Set.univ.pi fun _ : Fin V.rank => Set.univ.pi fun _ : Fin W.rank => K,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

end GlobalTheory.AdelicMatrixLattice
