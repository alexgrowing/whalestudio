import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LamEqOfKer

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem sees_mono {n : ℕ} {R G : Type} [CommRing R] [Group G] (D : GDet n R G) (V V' : Subgroup G)
    [V.Normal] [V'.Normal] (h : V' ≤ V) (I : Ideal R) (hV : Sees D V I) : Sees D V' I := by
  intro i x y hxy
  apply hV i x y
  have h' : V' ≤ V.comap (MonoidHom.id G) := fun g hg => h hg
  have key : ∀ z : MonoidAlgebra R G, MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V) z =
      MonoidAlgebra.mapDomainRingHom R (QuotientGroup.map V' V (MonoidHom.id G) h')
        (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V') z) := by
    intro z
    simp only [MonoidAlgebra.mapDomainRingHom_apply]
    apply MonoidAlgebra.coeff_injective
    simp only [MonoidAlgebra.coeff_mapDomain]
    rw [← Finsupp.mapDomain_comp]
    rfl
  rw [key, key, hxy]

theorem UpperTheory.V.Pa.Core.phSees :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (j : ℕ), ∃ V : OpenNormalSubgroup Λ.Ph, V.toSubgroup ≤ Ph0 Λ ∧ Sees W.t.D (V.toSubgroup.subgroupOf (Ph0 Λ)) (maximalIdeal W.R ^ j) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W j
  letI := W.ring
  letI := W.alg
  haveI := W.co
  obtain ⟨V, hV⟩ := dSees n W.R (Ph0 Λ) W.t.D (maximalIdeal W.R) W.t.cont j
  have hUo : IsOpen (Subtype.val '' (V : Set (Ph0 Λ))) :=
    (Λ.Ph0_open).isOpenMap_subtype_val _ V.toOpenSubgroup.isOpen
  have h1U : (1 : Λ.Ph) ∈ Subtype.val '' (V : Set (Ph0 Λ)) := ⟨1, V.one_mem, rfl⟩
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
  have hHle : H.toSubgroup ≤ Ph0 Λ := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := hH hg
    exact x.2
  refine ⟨H, hHle, ?_⟩
  refine sees_mono W.t.D _ _ ?_ _ hV
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨y, hy, hxy⟩ := hH hx
  have hyx : y = x := Subtype.ext hxy
  rw [← hyx]
  exact hy
