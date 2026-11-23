import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PhSees
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.CloseLift

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem gDet_chi_map_mapRingHom {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G]
    (D : GDet n R G) (f : R →+* R') (x : MonoidAlgebra R G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f x) = (D.chi x).map f := by
  unfold GDet.chi GDet.map
  dsimp only
  letI : Algebra R (Polynomial R') := ((algebraMap R' (Polynomial R')).comp f).toAlgebra
  let g : Polynomial R →ₐ[R] Polynomial R' :=
    { Polynomial.mapRingHom f with
      commutes' := fun c => by
        simp [RingHom.algebraMap_toAlgebra, Polynomial.algebraMap_apply] }
  have h := D.nat (Polynomial R) (Polynomial R') g
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C x)
  refine Eq.trans ?_ h
  congr 1
  rw [map_sub]
  congr 1
  · ext a
    simp [g, MonoidAlgebra.mapRingHom, Finsupp.single_apply]
  · ext a
    simp [g, MonoidAlgebra.mapRingHom]

private theorem gDet_tr_map_mapRingHom {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G]
    (D : GDet n R G) (f : R →+* R') (x : MonoidAlgebra R G) :
    (D.map f).tr (MonoidAlgebra.mapRingHom G f x) = f (D.tr x) := by
  unfold GDet.tr GDet.lam
  rw [gDet_chi_map_mapRingHom, Polynomial.coeff_map]
  simp

private theorem gDet_tr_comap_eq_tr_mapDomainRingHom {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H]
    (D : GDet n R G) (φ : H →* G) (x : MonoidAlgebra R H) :
    (D.comap φ).tr x = D.tr (MonoidAlgebra.mapDomainRingHom R φ x) := by
  unfold GDet.tr GDet.lam GDet.chi GDet.comap
  dsimp only
  rw [MonoidHom.comp_apply]
  congr 3
  show MonoidAlgebra.mapDomainRingHom _ φ _ = _
  rw [map_sub]
  congr 1
  · simp [MonoidAlgebra.mapDomainRingHom_apply]
  · ext a
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom]
    rw [Finsupp.mapDomain_mapRange _ _ _ _ (fun a b => Polynomial.C_add)]
    simp

theorem UpperTheory.V.Pa.Core.patched_trace_local_charPoly_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (v : L.Vl) (g : Fin n → L.Gv v) (ga : Fin n → Ph0 Λ) (h : Ph0 Λ), (∀ i, πo0 Λ (ga i) = Λ.G.φ v (g i)) → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (List.ofFn fun i => MonoidAlgebra.single (ga i) (1 : W.R) - MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.Rˣ) : W.R)).prod) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT v g ga h hga j
  obtain ⟨V, hVle, hsees⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.φ_lim V] with N hker hφ
  have hπo : ∀ i, Λ.πo (ga i) = ((Λ.G.φ v (g i) : Λ.G.G₀) : Λ.G.Γ) := fun i =>
    congrArg Subtype.val (hga i)
  have lift : ∀ i, ∃ x : Λ.Ph, Λ.π N x = (((T.GN N).φ v (g i) : (T.GN N).G₀) : (T.GN N).Γ) ∧
      (ga i : Λ.Ph)⁻¹ * x ∈ (V.toOpenSubgroup : Subgroup Λ.Ph) := fun i =>
    (closeLift _ _ _ (Λ.π N) Λ.πo _ hker).1 _ _ (ga i) (hφ v (g i)) (hπo i)
  choose x hx1 hx2 using lift
  have hmem : ∀ i, x i ∈ Ph0 Λ := fun i => by
    have := (Ph0 Λ).mul_mem (ga i).2 (hVle (hx2 i))
    simpa using this
  let gb : Fin n → Ph0 Λ := fun i => ⟨x i, hmem i⟩
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (List.ofFn fun i =>
    MonoidAlgebra.single (gb i) (1 : W.R) - MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.Rˣ) : W.R)).prod), ?_, Or.inl ?_⟩
  · refine hsees 1 _ _ ?_
    simp only [map_mul, map_list_prod, List.map_ofFn, map_sub, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    congr 2
    congr 1
    funext i
    simp only [Function.comp_apply, MonoidAlgebra.mapDomainRingHom_apply, map_sub, MonoidAlgebra.mapDomain_single]
    congr 2
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hx2 i
  · show (m.ρ N).toRingHom _ = 0
    rw [← gDet_tr_map_mapRingHom, (m.ρ_maps N).1, gDet_tr_comap_eq_tr_mapDomainRingHom]
    refine Eq.trans ?_ ((A.A N).p.Ord v g (πN0 Λ N h))
    congr 1
    unfold GFrame.oEl
    simp only [map_mul, map_list_prod, List.map_ofFn, map_sub, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single]
    rw [map_one]
    congr 2
    congr 1
    funext i
    simp only [Function.comp_apply, map_sub, MonoidAlgebra.mapRingHom_single,
      MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, map_one]
    rw [← (m.ρ_maps N).2.1 v i]
    congr 2
    exact Subtype.ext (hx1 i)
