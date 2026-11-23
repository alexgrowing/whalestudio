import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
import GroundTheory.ProfiniteCohomology.Procyclic
import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
import GroundTheory.ProfiniteCohomology.CupProducts.Pairing
import GroundTheory.LocalFields.WildInertia
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Arith.Selmer

open CategoryTheory CategoryTheory.Limits MonoidalCategory GroundTheory.ProfCoh

universe u

section Generic

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]

def kerRes (A : Rep.{u} k G) [IsDiscreteRep A] : AddSubgroup (cohomology A 1) :=
  (LinearMap.ker (cohomologyRes A N 1).hom).toAddSubgroup

variable {N}

variable (N)

def invariantsMap {A B : Rep.{u} k G} (f : A ⟶ B) :
    A.quotientToInvariants N ⟶ B.quotientToInvariants N :=
  (Rep.quotientToInvariantsFunctor k N).map f

variable [CompactSpace (G ⧸ N)]

def invariantsQuotientEquiv (A : Rep.{u} k G) :
    (A.quotientToInvariants N).ρ.invariants ≃ A.ρ.invariants where
  toFun x := ⟨((x : A.quotientToInvariants N) : A), fun g => by
    have := x.2 (QuotientGroup.mk g)
    exact congrArg Subtype.val this⟩
  invFun a := ⟨⟨(a : A), fun n => a.2 n⟩, fun q => by
    induction q using QuotientGroup.induction_on with
    | H g => exact Subtype.ext (a.2 g)⟩
  left_inv x := rfl
  right_inv a := rfl

end Generic

section Local

open GroundTheory.LocalField GroundTheory.LocalField.Abstract

variable (K Ω : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem exists_isZHatGenerator_inertia :
    ∃ σ : Gal(Ω/K) ⧸ inertiaGroup K Ω, IsZHatGenerator σ := by
  have hker : (unramifiedDegree K Ω).ker = inertiaGroup K Ω := ker_unramifiedDegree
  let e : Gal(Ω/K) ⧸ inertiaGroup K Ω →* Multiplicative ℤ̂ :=
    QuotientGroup.lift (inertiaGroup K Ω) (unramifiedDegree K Ω) hker.ge
  have he : ∀ g : Gal(Ω/K), e (g : Gal(Ω/K) ⧸ inertiaGroup K Ω) = unramifiedDegree K Ω g :=
    fun g => rfl
  have hinj : Function.Injective e := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [he] at hq
      rw [QuotientGroup.eq_one_iff, ← hker]
      exact hq
  have hsurj : Function.Surjective e := fun z => by
    obtain ⟨g, hg⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) z
    exact ⟨g, hg⟩
  have hcont : Continuous e :=
    (QuotientGroup.isQuotientMap_mk (inertiaGroup K Ω)).continuous_iff.2
      continuous_unramifiedDegree
  let E : Gal(Ω/K) ⧸ inertiaGroup K Ω ≃* Multiplicative ℤ̂ := MulEquiv.ofBijective e ⟨hinj, hsurj⟩
  let h : Gal(Ω/K) ⧸ inertiaGroup K Ω ≃ₜ Multiplicative ℤ̂ :=
    Continuous.homeoOfEquivCompactToT2 (f := E.toEquiv) hcont
  refine ⟨E.symm (Multiplicative.ofAdd 1), ⟨?_, fun n hn => ?_⟩⟩
  · have himg : (Subgroup.zpowers (E.symm (Multiplicative.ofAdd 1)) : Set _) =
        h.symm '' (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) := by
      ext q
      simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_image]
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨Multiplicative.ofAdd 1 ^ m, ⟨m, rfl⟩, by change E.symm _ = _; rw [map_zpow]⟩
      · rintro ⟨y, ⟨m, rfl⟩, rfl⟩
        exact ⟨m, by change _ = E.symm _; rw [map_zpow]⟩
    rw [IsTopologicalGenerator, himg]
    exact h.symm.surjective.denseRange.dense_image h.symm.continuous dense_zpowers_ofAdd_one
  · let φ : Gal(Ω/K) ⧸ inertiaGroup K Ω →* Multiplicative (ZMod n) :=
      (AddMonoidHom.toMultiplicative (ProfiniteInteger.proj ⟨n, hn⟩).toAddMonoidHom).comp
        E.toMonoidHom
    have hφ : Continuous φ :=
      continuous_ofAdd.comp ((ProfiniteInteger.continuous_proj ⟨n, hn⟩).comp
        (continuous_toAdd.comp hcont))
    refine ⟨φ, ?_, ?_⟩
    · have hk : (φ.ker : Set (Gal(Ω/K) ⧸ inertiaGroup K Ω)) = φ ⁻¹' {1} := by
        ext q
        simp [MonoidHom.mem_ker]
      rw [hk]
      exact hφ.isOpen_preimage {1} (isOpen_discrete _)
    · show Multiplicative.ofAdd (ProfiniteInteger.proj ⟨n, hn⟩
          (Multiplicative.toAdd (E (E.symm (Multiplicative.ofAdd 1))))) = _
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, map_one]
      rfl

variable {K Ω}

def unramifiedClasses {k : Type u} [CommRing k] (M : Rep.{u} k Gal(Ω/K)) [IsDiscreteRep M] :
    AddSubgroup (cohomology M 1) :=
  kerRes (inertiaGroup K Ω) M

end Local

end GroundTheory.Arith.Selmer
