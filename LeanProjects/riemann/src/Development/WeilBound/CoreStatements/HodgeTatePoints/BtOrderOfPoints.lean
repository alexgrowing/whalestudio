import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import ReciprocityTheory.DualLattices.TensorSpan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.HtPt.Mk

theorem bt_pgsh : ∀ (R C : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field C] [Algebra R C], Function.Injective (algebraMap R C) → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (A : Subalgebra R (Multiplicative N → R)), IsHopfOrder A → ∃ AA : ReciprocityTheory.PGsh.L2.HopfOrder R (C := C) N, ∀ f : N → C, f ∈ AA.carrier ↔ ∃ g ∈ A, ∀ x, f x = algebraMap R C (g (Multiplicative.ofAdd x)) := by
  intro R C _ _ _ _ _ hinj N _ _ _ A hA
  classical
  let φ : (Multiplicative N → R) →ₗ[R] (N → C) :=
    { toFun := fun g x => algebraMap R C (g (Multiplicative.ofAdd x))
      map_add' := by
        intro g h
        funext x
        simp
      map_smul' := by
        intro r g
        funext x
        simp [Algebra.smul_def] }
  have hφ : ∀ g x, φ g x = algebraMap R C (g (Multiplicative.ofAdd x)) := fun _ _ => rfl
  haveI := hA.finite
  haveI := hA.projective
  haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing
  obtain ⟨d, hd0, hd⟩ := hA.full
  have hcardT : Module.finrank R (Multiplicative N → R) = Fintype.card N := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr Multiplicative.toAdd
  have hrank : Module.finrank R A = Fintype.card N := by
    apply le_antisymm
    · rw [← hcardT]
      exact LinearMap.finrank_le_finrank_of_injective (f := A.val.toLinearMap) Subtype.val_injective
    · let sc : (Multiplicative N → R) →ₗ[R] A :=
        { toFun := fun f => ⟨d • f, hd f⟩
          map_add' := fun f g => Subtype.ext (smul_add d f g)
          map_smul' := fun r f => Subtype.ext (smul_comm d r f) }
      have hsc : Function.Injective sc := by
        intro f g hfg
        have h2 : d • f = d • g := congrArg Subtype.val hfg
        exact smul_right_injective _ hd0 h2
      rw [← hcardT]
      exact LinearMap.finrank_le_finrank_of_injective hsc
  let b : Module.Basis N R A := (Module.finBasisOfFinrankEq R A hrank).reindex (Fintype.equivFin N).symm
  refine ⟨{ carrier := (Subalgebra.toSubmodule A).map φ
            lat := ?_
            le_int := ?_
            one_mem := ?_
            mul_mem := ?_
            comul := ?_
            antipode := ?_ }, ?_⟩
  · refine ⟨fun x j => φ (b j) x, ?_, ?_⟩
    · let M : Matrix N N R := fun x j => (b j : Multiplicative N → R) (Multiplicative.ofAdd x)
      have hdet : Matrix.det (fun x j => φ (b j) x : Matrix N N C) = algebraMap R C M.det := by
        rw [RingHom.map_det]
        rfl
      rw [hdet]
      apply isUnit_iff_ne_zero.mpr
      rw [map_ne_zero_iff _ hinj]
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0
      have hsum : ∑ j, v j • b j = 0 := by
        apply Subtype.ext
        funext t
        have h3 := congrFun hv (Multiplicative.toAdd t)
        simpa [Matrix.mulVec, dotProduct, M, mul_comm] using h3
      exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent v hsum)
    · apply le_antisymm
      · rintro f ⟨g, hg, rfl⟩
        have hg' : (⟨g, hg⟩ : A) = ∑ j, b.repr ⟨g, hg⟩ j • b j := (b.sum_repr _).symm
        have hgs : g = ∑ j, b.repr ⟨g, hg⟩ j • (b j : Multiplicative N → R) := by
          have h4 : ((⟨g, hg⟩ : A) : Multiplicative N → R)
              = ((∑ j, b.repr ⟨g, hg⟩ j • b j : A) : Multiplicative N → R) := congrArg Subtype.val hg'
          rw [AddSubmonoidClass.coe_finset_sum] at h4
          exact h4
        rw [hgs, map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact ⟨b j, (b j).2, rfl⟩
  · rintro f ⟨g, hg, rfl⟩ x
    exact ⟨g (Multiplicative.ofAdd x), rfl⟩
  · refine ⟨1, A.one_mem, ?_⟩
    funext x
    simp [hφ]
  · rintro f g ⟨f', hf', rfl⟩ ⟨g', hg', rfl⟩
    refine ⟨f' * g', A.mul_mem hf' hg', ?_⟩
    funext x
    simp [hφ]
  · rintro f ⟨g, hg, rfl⟩
    let ψ : (Multiplicative N × Multiplicative N → R) →ₗ[R] (N × N → C) :=
      { toFun := fun F p => algebraMap R C (F (Multiplicative.ofAdd p.1, Multiplicative.ofAdd p.2))
        map_add' := by
          intro F G
          funext p
          simp
        map_smul' := by
          intro r F
          funext p
          simp [Algebra.smul_def] }
    have hle : GlobalTheory.CompanionTheory.Ar.BT.prodSpan A ≤
        (ReciprocityTheory.PGsh.L2.tensorSpan R ((Subalgebra.toSubmodule A).map φ)).comap ψ := by
      rw [GlobalTheory.CompanionTheory.Ar.BT.prodSpan, Submodule.span_le]
      rintro _ ⟨a, ha, a', ha', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      apply Submodule.subset_span
      refine ⟨φ a, ⟨a, ha, rfl⟩, φ a', ⟨a', ha', rfl⟩, ?_⟩
      funext p
      simp [hφ, ψ]
    have h5 := hle (hA.comul g hg)
    rw [Submodule.mem_comap] at h5
    convert h5 using 1
    funext p
    simp [hφ, ψ, ReciprocityTheory.PGsh.L2.addPull, LinearMap.funLeft_apply]
  · rintro f ⟨g, hg, rfl⟩
    refine ⟨fun t => g t⁻¹, hA.inv g hg, ?_⟩
    funext x
    simp [hφ]
  · intro f
    show f ∈ (Subalgebra.toSubmodule A).map φ ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, fun x => rfl⟩
    · rintro ⟨g, hg, hfg⟩
      exact ⟨g, hg, funext fun x => (hfg x).symm⟩

end PositivityTheory.HtPt.Mk
