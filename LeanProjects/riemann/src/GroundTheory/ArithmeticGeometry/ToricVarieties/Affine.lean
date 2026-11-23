import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.ToricFaces

namespace GroundTheory.Arith.Toric

open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry

universe u

section SemigroupAlgebra

variable (k : Type*) [CommSemiring k] {G : Type*} [AddCommMonoid G]

noncomputable def semigroupAlgebra (S : AddSubmonoid G) : Subalgebra k (AddMonoidAlgebra k G) :=
  (AddMonoidAlgebra.supported k k (S : Set G)).toSubalgebra
    (by
      rw [AddMonoidAlgebra.mem_supported]
      exact (Finset.coe_subset.2 (support_coeff_one_subset)).trans
        (by simp [S.zero_mem]))
    (by
      classical
      intro x y hx hy
      rw [AddMonoidAlgebra.mem_supported] at hx hy ⊢
      intro m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset x y hm)
      exact S.add_mem (hx ha) (hy hb))

variable {k}

theorem mem_semigroupAlgebra {S : AddSubmonoid G} {f : AddMonoidAlgebra k G} :
    f ∈ semigroupAlgebra k S ↔ ↑f.coeff.support ⊆ (S : Set G) := Iff.rfl

theorem single_mem_semigroupAlgebra {S : AddSubmonoid G} {s : G} (hs : s ∈ S) (a : k) :
    single s a ∈ semigroupAlgebra k S := by
  rw [mem_semigroupAlgebra, coeff_single]
  exact (Finset.coe_subset.2 Finsupp.support_single_subset).trans (by simpa using hs)

theorem semigroupAlgebra_mono {S T : AddSubmonoid G} (h : S ≤ T) :
    semigroupAlgebra k S ≤ semigroupAlgebra k T :=
  fun _ hf => (mem_semigroupAlgebra.1 hf).trans (SetLike.coe_subset_coe.2 h)

theorem toSubmodule_semigroupAlgebra (S : AddSubmonoid G) :
    Subalgebra.toSubmodule (semigroupAlgebra k S) =
      Submodule.span k ((fun s => single s (1 : k)) '' (S : Set G)) :=
  AddMonoidAlgebra.supported_eq_span_single k (S : Set G)

theorem semigroupAlgebra_eq_adjoin (S : AddSubmonoid G) :
    semigroupAlgebra k S = Algebra.adjoin k ((fun s => single s (1 : k)) '' (S : Set G)) := by
  apply le_antisymm
  · intro f hf
    have : f ∈ Subalgebra.toSubmodule (semigroupAlgebra k S) := hf
    rw [toSubmodule_semigroupAlgebra] at this
    exact Algebra.span_le_adjoin k _ this
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨s, hs, rfl⟩
    exact single_mem_semigroupAlgebra hs 1

theorem semigroupAlgebra_closure (T : Set G) :
    semigroupAlgebra k (AddSubmonoid.closure T) =
      Algebra.adjoin k ((fun s => single s (1 : k)) '' T) := by
  apply le_antisymm
  · rw [semigroupAlgebra_eq_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨s, hs, rfl⟩
    induction hs using AddSubmonoid.closure_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero =>
      show single (0 : G) (1 : k) ∈ _
      rw [← AddMonoidAlgebra.one_def]; exact Subalgebra.one_mem _
    | add x y _ _ hx hy =>
      have e : single (x + y) (1 : k) = single x 1 * single y 1 := by
        rw [single_mul_single, one_mul]
      show single (x + y) (1 : k) ∈ _
      rw [e]
      exact Subalgebra.mul_mem _ hx hy
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨s, hs, rfl⟩
    exact single_mem_semigroupAlgebra (AddSubmonoid.subset_closure hs) 1

theorem finiteType_semigroupAlgebra {S : AddSubmonoid G} (hS : S.FG) :
    Algebra.FiniteType k (semigroupAlgebra k S) := by
  classical
  obtain ⟨T, rfl⟩ := hS
  rw [← Subalgebra.fg_iff_finiteType, semigroupAlgebra_closure]
  exact ⟨T.image fun s => single s (1 : k), by rw [Finset.coe_image]⟩

variable (k) in

noncomputable def semigroupAlgebraEquiv (S : AddSubmonoid G) :
    AddMonoidAlgebra k S ≃ₐ[k] semigroupAlgebra k S :=
  (AlgEquiv.ofInjective (AddMonoidAlgebra.mapDomainAlgHom k k S.subtype)
      (mapDomain_injective Subtype.val_injective)).trans
    (Subalgebra.equivOfEq _ _ (by
      apply le_antisymm
      · rintro _ ⟨f, rfl⟩
        induction f using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add f g hf hg => rw [map_add]; exact Subalgebra.add_mem _ hf hg
        | single s a =>
          have e : mapDomainAlgHom k k S.subtype (single s a) = single (s : G) a := by simp
          change mapDomainAlgHom k k S.subtype (single s a) ∈ _
          rw [e]
          exact single_mem_semigroupAlgebra s.2 a
      · rw [semigroupAlgebra_eq_adjoin, Algebra.adjoin_le_iff]
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨single ⟨s, hs⟩ 1, by simp [mapDomainAlgHom_apply, mapDomain_single]⟩))

end SemigroupAlgebra

section Domain

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]

theorem uniqueSums_of_free [Module.Free ℤ G] : UniqueSums G :=
  UniqueSums.of_injective_addHom
    ((Module.Free.chooseBasis ℤ G).repr.toLinearMap.toAddMonoidHom.toAddHom)
    (Module.Free.chooseBasis ℤ G).repr.injective inferInstance

instance isDomain_addMonoidAlgebra [IsDomain k] [Module.Free ℤ G] :
    IsDomain (AddMonoidAlgebra k G) :=
  haveI := uniqueSums_of_free (G := G)
  NoZeroDivisors.to_isDomain _

instance isDomain_semigroupAlgebra [IsDomain k] [Module.Free ℤ G] (S : AddSubmonoid G) :
    IsDomain (semigroupAlgebra k S) :=
  inferInstance

end Domain

section Localization

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]

noncomputable abbrev semigroupAlgebraAlgebra {S T : AddSubmonoid G} (h : S ≤ T) :
    Algebra (semigroupAlgebra k S) (semigroupAlgebra k T) :=
  (Subalgebra.inclusion (semigroupAlgebra_mono h)).toRingHom.toAlgebra

theorem isLocalization_away_semigroupAlgebra {S T : AddSubmonoid G} (h : S ≤ T) {u : G}
    (hu : u ∈ S) (hu' : -u ∈ T) (hT : ∀ m ∈ T, ∃ j : ℕ, m + j • u ∈ S) :
    letI := semigroupAlgebraAlgebra (k := k) h
    IsLocalization.Away (⟨single u 1, single_mem_semigroupAlgebra hu 1⟩ : semigroupAlgebra k S)
      (semigroupAlgebra k T) := by
  let := semigroupAlgebraAlgebra (k := k) h
  classical
  have hmap : ∀ x : semigroupAlgebra k S,
      ((algebraMap (semigroupAlgebra k S) (semigroupAlgebra k T) x : semigroupAlgebra k T) :
        AddMonoidAlgebra k G) = x := fun _ => rfl
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    have e1 : single u (1 : k) * single (-u) 1 = 1 := by
      rw [single_mul_single, add_neg_cancel, one_mul, ← AddMonoidAlgebra.one_def]
    have hunit : IsUnit (algebraMap (semigroupAlgebra k S) (semigroupAlgebra k T)
        ⟨single u 1, single_mem_semigroupAlgebra hu 1⟩) :=
      isUnit_iff_exists_inv.2 ⟨⟨single (-u) 1, single_mem_semigroupAlgebra hu' 1⟩, Subtype.ext e1⟩
    rw [map_pow]
    exact hunit.pow n
  · intro z
    have hz : ∀ m ∈ (z : AddMonoidAlgebra k G).coeff.support, ∃ j : ℕ, m + j • u ∈ S :=
      fun m hm => hT m (z.2 hm)
    choose! f hf using hz
    set n := (z : AddMonoidAlgebra k G).coeff.support.sup f
    have hmem : single (n • u) 1 * (z : AddMonoidAlgebra k G) ∈ semigroupAlgebra k S := by
      rw [mem_semigroupAlgebra]
      intro m hm
      obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1
        (support_coeff_single_mul_subset (z : AddMonoidAlgebra k G) 1 (n • u) hm)
      have hle : f m' ≤ n := Finset.le_sup hm'
      have : n • u + m' = (m' + f m' • u) + (n - f m') • u := by
        rw [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hle, add_comm]
      rw [this]
      exact S.add_mem (hf m' hm') (S.nsmul_mem hu _)
    refine ⟨(⟨_, hmem⟩, ⟨_, n, rfl⟩), ?_⟩
    apply Subtype.ext
    simp only [map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow, hmap, single_pow, one_pow]
    rw [mul_comm]
  · intro x y hxy
    have hxy' : x = y := Subtype.ext (by
      have := congrArg (fun z : semigroupAlgebra k T => (z : AddMonoidAlgebra k G)) hxy
      simpa only [hmap] using this)
    exact ⟨1, by rw [hxy']⟩

end Localization

section Toric

variable {N : Type u} [AddCommGroup N] (k : Type u) [CommRing k]

noncomputable abbrev toricAlgebra (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    Subalgebra k (AddMonoidAlgebra k (Dual ℤ N)) :=
  semigroupAlgebra k (dualMonoid σ)

noncomputable abbrev affineToricVariety (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) : Scheme.{u} :=
  Spec (CommRingCat.of (toricAlgebra k σ))

variable {k}
variable [Module.Free ℤ N] [Module.Finite ℤ N]

theorem finiteType_toricAlgebra {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) : Algebra.FiniteType k (toricAlgebra k σ) :=
  finiteType_semigroupAlgebra (dualMonoid_fg hσ)

instance affineToricVariety_isIntegral [IsDomain k] (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    IsIntegral (affineToricVariety k σ) :=
  inferInstance

end Toric

section Faces

variable {N : Type u} [AddCommGroup N] {k : Type u} [CommRing k]
variable [Module.Free ℤ N] [Module.Finite ℤ N]

variable (k) in

noncomputable def affineToricVarietyMap {σ τ : PointedCone ℝ (ℝ ⊗[ℤ] N)} (h : τ ≤ σ) :
    affineToricVariety k τ ⟶ affineToricVariety k σ :=
  Spec.map (CommRingCat.ofHom
    (Subalgebra.inclusion (semigroupAlgebra_mono (k := k) (dualMonoid_anti h))).toRingHom)

end Faces

section Torus

variable (N : Type u) [AddCommGroup N] (k : Type u) [CommRing k]

noncomputable abbrev torus : Scheme.{u} :=
  Spec (CommRingCat.of (AddMonoidAlgebra k (Dual ℤ N)))

variable {N k}

variable (k) in

noncomputable def torusToAffineToricVariety (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    torus N k ⟶ affineToricVariety k σ :=
  Spec.map (CommRingCat.ofHom (toricAlgebra k σ).val.toRingHom)

variable [Module.Free ℤ N] [Module.Finite ℤ N]

end Torus

end GroundTheory.Arith.Toric
