import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PhSees
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.CloseLift
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mapDomain_partial_charpoly_power_zero {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H] (φ : G →* H) (h ph ta : G)
    (u : Fin n → R) (i : Fin n) (y : R) :
    MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single h 1 * q2El ph ta u i y) =
      MonoidAlgebra.single (φ h) 1 * q2El (φ ph) (φ ta) u i y := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single g c) =
      MonoidAlgebra.single (φ g) c := fun g c => by simp
  simp only [q2El, map_mul, map_sub, map_one, map_list_prod, List.map_ofFn, hs]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem mapRingHom_single_mul_partial_charpoly_element {n : ℕ} {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) (h ph ta : G)
    (u : Fin n → R) (i : Fin n) (y : R) :
    MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single h 1 * q2El ph ta u i y) =
      MonoidAlgebra.single h 1 * q2El ph ta (fun k => f (u k)) i (f y) := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g c) =
      MonoidAlgebra.single g (f c) := fun g c => by simp
  simp only [q2El, map_mul, map_sub, map_one, map_list_prod, List.map_ofFn, hs]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem comap_tr {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H] (D : GDet n R H) (φ : G →* H)
    (z : MonoidAlgebra R G) : (D.comap φ).tr z = D.tr (MonoidAlgebra.mapDomainRingHom R φ z) := by
  have hc : (D.comap φ).chi z = D.chi (MonoidAlgebra.mapDomainRingHom R φ z) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom (Polynomial R) φ _) = D.D _ _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single g r => simp
  simp only [GDet.tr, GDet.lam, hc]

theorem UpperTheory.V.Pa.Core.t3Q2 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (a : Fin T.q) (i : Fin n) (ph ta h : Ph0 Λ), πo0 Λ ph = Λ.ph a → πo0 Λ ta = Λ.ta a → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph ta (W.t.U a) i (W.t.y a i)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ a i ph ta h hph hta j
  obtain ⟨V, hV0, hV⟩ := UpperTheory.V.Pa.Core.phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.ph_lim V, Λ.ta_lim V] with N hk h1 h2
  have lift : ∀ (g : Ph0 Λ) (x : (T.GN N).G₀) (b : Λ.G.G₀), Close (Λ.π N) Λ.πo V.toSubgroup (x : (T.GN N).Γ) (b : Λ.G.Γ) →
      πo0 Λ g = b → ∃ g' : Ph0 Λ, πN0 Λ N g' = x ∧
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) g = QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) g' := by
    intro g x b hc hg
    obtain ⟨g', e, hv⟩ := (UpperTheory.V.Pa.Core.closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (g : Λ.Ph) hc
      (congrArg Subtype.val hg)
    have hm : g' ∈ Ph0 Λ := by
      have := (Ph0 Λ).mul_mem g.2 (hV0 hv)
      rwa [mul_inv_cancel_left] at this
    exact ⟨⟨g', hm⟩, Subtype.ext e, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hv)⟩
  obtain ⟨ph', e1, q1⟩ := lift ph _ _ (h1 a) hph
  obtain ⟨ta', e2, q2⟩ := lift ta _ _ (h2 a) hta
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i)), ?_, Or.inr fun x => ?_⟩
  · apply hV 1
    rw [mapDomain_partial_charpoly_power_zero, mapDomain_partial_charpoly_power_zero, q1, q2]
  · obtain ⟨hD, -, -, hU, hy⟩ := m.ρ_maps N
    have key : m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i))) =
        (A.A N).p.D.tr (MonoidAlgebra.single (πN0 Λ N h) 1 *
          q2El (T.ph N a) (T.ta N a) ((A.A N).U a) i ((A.A N).s (MvPowerSeries.X (a, i)))) := by
      have h3 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
        (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i))).2 1
      refine h3.symm.trans ?_
      rw [hD, mapRingHom_single_mul_partial_charpoly_element, hy a i, funext (hU a)]
      refine (comap_tr _ _ _).trans ?_
      rw [mapDomain_partial_charpoly_power_zero, e1, e2]
    rw [key]
    exact (A.m N).rel2 a i _ x
