import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PhSees
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.CloseLift
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_dom {n : ℕ} {S H G : Type} [CommRing S] [Group H] [Group G] (D : GDet n S G) (φ : H →* G)
    (i : ℕ) (z : MonoidAlgebra S H) : (D.comap φ).lam i z = D.lam i (MonoidAlgebra.mapDomainRingHom S φ z) := by
  unfold GDet.lam
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

private theorem mapDomain_single_mul_charpoly_element {n : ℕ} {S H G : Type} [CommRing S] [Group H] [Group G] (φ : H →* G) (h g : H)
    (U : Fin n → S) : MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.single h 1 * q1El g U) =
      MonoidAlgebra.single (φ h) 1 * q1El (φ g) U := by
  rw [map_mul, q1El, q1El, map_list_prod, List.map_ofFn]
  congr 1
  · simp
  · congr 2
    funext i
    rw [Function.comp_apply, map_sub]
    simp

private theorem mapRingHom_single_mul_charpoly_element {n : ℕ} {R S H : Type} [CommRing R] [CommRing S] [Group H] (f : R →+* S) (h g : H)
    (U : Fin n → R) : MonoidAlgebra.mapRingHom H f (MonoidAlgebra.single h 1 * q1El g U) =
      MonoidAlgebra.single h 1 * q1El g fun i => f (U i) := by
  rw [map_mul, q1El, q1El, map_list_prod, List.map_ofFn, MonoidAlgebra.mapRingHom_single, map_one]
  congr 3
  funext i
  simp only [Function.comp_apply, map_sub, MonoidAlgebra.mapRingHom_single, map_one]

theorem UpperTheory.V.Pa.Core.t3Q1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (a : Fin T.q) (ph h : Ph0 Λ), πo0 Λ ph = Λ.ph a → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * q1El ph (W.t.U a)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ a ph h hph j
  obtain ⟨V, hV0, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.ph_lim V] with N hk hc
  obtain ⟨g', hg', hgV⟩ := (closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (ph : Λ.Ph) (hc a)
    (congrArg Subtype.val hph)
  have hmem : g' ∈ Ph0 Λ := by
    have := mul_mem ph.2 (hV0 hgV)
    rwa [mul_inv_cancel_left] at this
  let p' : Ph0 Λ := ⟨g', hmem⟩
  have hp' : πN0 Λ N p' = T.ph N a := Subtype.ext hg'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * q1El p' (W.t.U a)), hV 1 _ _ ?_, Or.inr fun x => ?_⟩
  · have e : QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) ph =
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) p' :=
      QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hgV)
    rw [mapDomain_single_mul_charpoly_element, mapDomain_single_mul_charpoly_element, e]
  · obtain ⟨hD, -, -, hU, -⟩ := m.ρ_maps N
    have e : m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * q1El p' (W.t.U a))) =
        (A.A N).p.D.tr (MonoidAlgebra.single (πN0 Λ N h) 1 * q1El (T.ph N a) ((A.A N).U a)) := by
      have h1 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
        (MonoidAlgebra.single h 1 * q1El p' (W.t.U a))).2 1
      rw [hD, lam_dom, mapRingHom_single_mul_charpoly_element, mapDomain_single_mul_charpoly_element, hp', funext (hU a)] at h1
      exact h1.symm
    rw [e]
    exact (A.m N).rel1 a _ x
