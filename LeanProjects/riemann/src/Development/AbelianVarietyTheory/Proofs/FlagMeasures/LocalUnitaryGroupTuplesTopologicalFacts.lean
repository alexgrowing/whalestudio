import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalUnitaryTop

theorem linearIndependent_iff_smul_basis {K S V ι α : Type} [Field K] [CommRing S] [Algebra K S]
    [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower K S V] [Fintype ι] [Fintype α]
    (b : Module.Basis ι K S) (X : α → V) :
    LinearIndependent S X ↔ LinearIndependent K fun p : ι × α => b p.1 • X p.2 := by
  refine ⟨fun h => linearIndependent_smul b.linearIndependent h, fun h => ?_⟩
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h0 := h (fun p => b.repr (g p.2) p.1) (by
    rw [← hg, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← b.sum_repr (g j), Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => (smul_assoc _ _ _).symm)
  exact b.ext_elem fun k => by simpa using h0 (k, i)

theorem isOpen_linearIndependent {K S ι α β : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [CommRing S] [Algebra K S] [TopologicalSpace S] [IsModuleTopology K S] [IsTopologicalRing S]
    [Fintype ι] [Fintype α] [Fintype β] (b : Module.Basis ι K S) :
    IsOpen {X : α → β → S | LinearIndependent S X} := by
  let e : (β → S) ≃ₗ[K] (β → ι → K) := LinearEquiv.piCongrRight fun _ => b.equivFun
  have hb : Continuous b.equivFun :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have hc : Continuous fun (X : α → β → S) (p : ι × α) => e (b p.1 • X p.2) := by
    refine continuous_pi fun p => continuous_pi fun j => ?_
    have : Continuous fun X : α → β → S => b p.1 * X p.2 j := by fun_prop
    exact hb.comp this
  have ho := (isOpen_setOfPred_linearIndependent (𝕜 := K) (E := β → ι → K) (ι := ι × α)).preimage hc
  convert ho using 1
  ext X
  rw [Set.mem_ofPred_eq, linearIndependent_iff_smul_basis b]
  exact (e.toLinearMap.linearIndependent_iff e.ker).symm

theorem top_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsTopologicalRing (Fv F v ⊗[F] E) ∧ LocallyCompactSpace (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧ IsTopologicalGroup (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ SecondCountableTopology (HA (Fv F v) σ J) ∧ ∀ a : ℕ, IsOpen {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Continuous (fun p : HA (Fv F v) σ J × (Fin a → Fin n → Fv F v ⊗[F] E) => p.1 • p.2) := by
  intro F E _ _ _ _ _ σ _ n J _ v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hr : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Fv F v) σ n J
  refine ⟨hr, e.isClosedEmbedding.locallyCompactSpace, e.isEmbedding.t2Space,
    e.secondCountableTopology, inferInstanceAs (IsTopologicalGroup (HR (Fv F v) σ J)), h1, h3, h2,
    fun a => ⟨?_, ?_⟩⟩
  · letI : NontriviallyNormedField (Fv F v) :=
      Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
    exact isOpen_linearIndependent (K := Fv F v)
      (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E))
  · have hm : Continuous fun g : HA (Fv F v) σ J => HA.mat (Fv F v) σ J g :=
      continuous_subtype_val
    have hv : Continuous fun g : HA (Fv F v) σ J =>
        ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := Units.continuous_val.comp hm
    refine continuous_pi fun b => ?_
    exact (hv.comp continuous_fst).matrix_mulVec ((continuous_apply b).comp continuous_snd)

end GlobalTheory.LocalUnitaryTop
