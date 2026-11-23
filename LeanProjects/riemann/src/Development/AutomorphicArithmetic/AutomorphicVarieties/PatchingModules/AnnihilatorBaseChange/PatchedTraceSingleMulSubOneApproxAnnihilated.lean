import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PhSees
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.CloseLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tr_zero {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (hn : 1 ≤ n) : D.tr 0 = 0 := by
  have h1 : (MonoidAlgebra.single (1 : G) (Polynomial.X : Polynomial A))
      = (Polynomial.X : Polynomial A) • (1 : MonoidAlgebra (Polynomial A) G) := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single', mul_one]
  have hchi : D.chi 0 = Polynomial.X ^ n := by
    simp only [GDet.chi, map_zero, sub_zero]
    rw [h1, D.homog, map_one, mul_one]
  simp only [GDet.tr, GDet.lam, hchi, Polynomial.coeff_X_pow]
  rw [if_neg (by omega)]
  simp

theorem UpperTheory.V.Pa.Core.patched_trace_single_mul_sub_one_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), 1 ≤ n → Adapted T (r := r) → ∀ (h k : Ph0 Λ), πo0 Λ k = 1 → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k 1 - 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hn _ h k hk j
  obtain ⟨V, hVle, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  refine (Λ.ker_lim V).mono fun N hN => ?_
  have hk1 : Λ.πo (k : Λ.Ph) = 1 := congrArg Subtype.val hk
  have hkmem : (k : Λ.Ph) ∈ (Λ.π N).ker ⊔ (V.toOpenSubgroup : Subgroup Λ.Ph) := by
    rw [hN]
    exact Subgroup.mem_sup_left hk1
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.1 hkmem
  have haPh : a ∈ Ph0 Λ := by
    have : a = (k : Λ.Ph) * b⁻¹ := by rw [← hab]; group
    rw [this]
    exact (Ph0 Λ).mul_mem k.2 ((Ph0 Λ).inv_mem (hVle hb))
  set k' : Ph0 Λ := ⟨a, haPh⟩ with hk'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)), ?_, Or.inl ?_⟩
  · have hq : (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))) k
        = QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ)) k' := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : ((k⁻¹ * k' : Ph0 Λ) : Λ.Ph) = b⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk']
        rw [← hab]
        group
      rw [this]
      exact inv_mem hb
    have hxy : (MonoidAlgebra.mapDomainRingHom W.R
          (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))))
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k 1 - 1))
        = (MonoidAlgebra.mapDomainRingHom W.R
          (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))))
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)) := by
      simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, hq]
    exact hV 1 _ _ hxy
  · have hπ : πN0 Λ N k' = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have hmaps := (m.ρ_maps N).1
    have h1 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
      (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))).2 1
    have hy : (MonoidAlgebra.mapRingHom (Ph0 Λ) (m.ρ N).toRingHom)
        (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))
        = MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1) := by
      simp
    have h2 := (comap_lam n _ _ _ (πN0 Λ N) (A.A N).p.D).2.2.1
      (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))
    have h3 : (MonoidAlgebra.mapDomainRingHom (A.A N).R (πN0 Λ N))
        (MonoidAlgebra.single h (1 : (A.A N).R) * (MonoidAlgebra.single k' (1 : (A.A N).R) - 1)) = 0 := by
      rw [map_mul, map_sub, map_one]
      simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, hπ]
      rw [← MonoidAlgebra.one_def, sub_self, mul_zero]
    calc m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)))
        = (m.ρ N).toRingHom (W.t.D.lam 1 (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))) := rfl
      _ = (W.t.D.map (m.ρ N).toRingHom).lam 1 ((MonoidAlgebra.mapRingHom (Ph0 Λ) (m.ρ N).toRingHom)
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))) := h1.symm
      _ = ((A.A N).p.D.comap (πN0 Λ N)).tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)) := by
          rw [hy, hmaps]
          rfl
      _ = 0 := by rw [h2, h3]; exact tr_zero _ hn
