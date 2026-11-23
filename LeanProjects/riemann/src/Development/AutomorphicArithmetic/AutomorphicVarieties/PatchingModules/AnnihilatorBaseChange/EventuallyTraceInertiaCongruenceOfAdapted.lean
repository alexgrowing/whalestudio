import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PhSees
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.CloseLift
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_push {n : ℕ} {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G]
    {E : GDet n R H} {D : GDet n S G} {f : R →+* S} {φ : H →* G}
    (h : E.map f = D.comap φ) (i : ℕ) (y : MonoidAlgebra R H) :
    f (E.lam i y) = D.lam i (MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.mapRingHom H f y)) := by
  rw [← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, h]
  unfold GDet.lam
  generalize MonoidAlgebra.mapRingHom H f y = z
  congr 2
  change D.D (Polynomial S) (MonoidAlgebra.mapDomainRingHom (Polynomial S) φ _) = D.D (Polynomial S) _
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp

theorem UpperTheory.V.Pa.Core.eventually_trace_inertia_congruence_of_adapted :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (w : L.St) (g : L.Gu w) (ga h : Ph0 Λ), g ∈ L.Ju w → πo0 Λ ga = Λ.G.φu w g → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single ga 1 - 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m had w g ga h hg hga j
  obtain ⟨V, hV0, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.φu_lim V] with N hk hφ
  obtain ⟨g', hg', hgv⟩ := (closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (ga : Λ.Ph) (hφ w g)
    (congrArg Subtype.val hga)
  have hm : g' ∈ Ph0 Λ := by
    simpa using mul_mem ga.2 (hV0 hgv)
  let gN : Ph0 Λ := ⟨g', hm⟩
  have e0 : πN0 Λ N gN = (T.GN N).φu w g := Subtype.ext hg'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single gN 1 - 1)), hV 1 _ _ ?_, Or.inl ?_⟩
  · have e : QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) ga =
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) gN := QuotientGroup.eq.2 hgv
    simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, e]
  · have e1 : πN0 Λ N gN ∈ (A.A N).rN.Ip w := by
      rw [e0]
      refine ⟨⟨g, hg, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩
      have h1 : G0.φu w g ∈ r.Ip w := by
        rw [had.2]
        exact ⟨g, hg, rfl⟩
      rw [MonoidHom.mem_ker, (A.A N).compat.1 i, MonoidHom.comp_apply, (T.h N).p₀_φu]
      exact Subgroup.mem_iInf.1 h1.2 i
    have hl := lam_push (m.ρ_maps N).1 1 (MonoidAlgebra.single h 1 * (MonoidAlgebra.single gN 1 - 1))
    simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single] at hl
    exact hl.trans ((A.A N).p.I w _ e1 _)
