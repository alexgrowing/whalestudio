import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermPrimeIdealMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermInjectiveClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSquareUnitsLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSquareFactorizationSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SquareNear

theorem stalk_props : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, IsDomain (G₁.left.presheaf.stalk x) ∧ IsNoetherianRing (G₁.left.presheaf.stalk x) ∧ IsIntegrallyClosed (G₁.left.presheaf.stalk x) := by
  intro R' _ _ _ hA G₁ _ _ hG x
  obtain ⟨_, -, _, -⟩ := hA
  haveI := hG.smooth
  have hS : GlobalTheory.IsNormalScheme (Sp R') := inferInstance
  have h := GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G₁.hom
    ((GlobalTheory.isNormalScheme_iff _).mp hS) x
  haveI : IsLocallyNoetherian G₁.left := LocallyOfFiniteType.isLocallyNoetherian G₁.hom
  exact ⟨h.1, inferInstance, h.2⟩

theorem exists_open_unit_mul_sq : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (L2 : LB G₁.left), L2.IsLB → ∀ (h : L2.Sec) (Lθ : LB (pullback G₁.hom (jK R'))), Lθ.IsLB → ∀ θ : Lθ.Sec, (∀ j i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (L2.U j)).hom (h.f j))) → ∀ x : G₁.left, G₁.hom x = closedPoint R' → (∀ j (hx : x ∈ L2.U j), (G₁.left.presheaf.germ (L2.U j) x hx).hom (h.f j) ∉ Ideal.map ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) (maximalIdeal R')) → (∀ j (hx : x ∈ L2.U j), ∃ (C' : Type) (_ : CommRing C') (_ : IsDomain C') (_ : IsNoetherianRing C') (_ : IsIntegrallyClosed C') (_ : Algebra (G₁.left.presheaf.stalk x) C') (_ : Module.FaithfullyFlat (G₁.left.presheaf.stalk x) C') (u : C'ˣ) (f : C'), algebraMap (G₁.left.presheaf.stalk x) C' ((G₁.left.presheaf.germ (L2.U j) x hx).hom (h.f j)) = u * f ^ 2) → ∃ V : G₁.left.Opens, x ∈ V ∧ ∃ a : Γ(G₁.left, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(G₁.left, V ⊓ L2.U j)ˣ, (G₁.left.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(G₁.left, V ⊓ L2.U j)) * (G₁.left.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  intro R' _ _ _ hA G₁ _ _ hG L2 hL2 h Lθ hLθ θ hθ x hx hvert hformal
  obtain ⟨hD, hN, hIC⟩ := stalk_props R' hA G₁ hG x
  obtain ⟨j₀, hj₀⟩ : ∃ j, x ∈ L2.U j := by
    have hmem : x ∈ (⨆ i, L2.U i) := by rw [hL2.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hmem
  have hne : (G₁.left.presheaf.germ (L2.U j₀) x hj₀).hom (h.f j₀) ≠ 0 := fun e =>
    hvert j₀ hj₀ (e ▸ Ideal.zero_mem _)
  obtain ⟨C', _, _, _, _, _, _, u', f', hf'⟩ := hformal j₀ hj₀
  have Hp : ∀ p : Ideal (G₁.left.presheaf.stalk x), p.IsPrime → p.height = 1 →
      ∃ a b c : G₁.left.presheaf.stalk x, b ∉ p ∧ c ∉ p ∧
        b * (G₁.left.presheaf.germ (L2.U j₀) x hj₀).hom (h.f j₀) = c * a ^ 2 := by
    intro p hp h1
    by_cases hq : Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p = ⊥
    · exact GlobalTheory.T.theta_section_square_units_local R' hA G₁ hG L2 h Lθ hLθ θ hθ x j₀ hj₀ p hp hq
    · refine ⟨1, 1, (G₁.left.presheaf.germ (L2.U j₀) x hj₀).hom (h.f j₀), ?_, ?_, by ring⟩
      · exact fun h1p => hp.ne_top ((Ideal.eq_top_iff_one _).2 h1p)
      · intro hmem
        apply hvert j₀ hj₀
        haveI hqp : (Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p).IsPrime := Ideal.comap_isPrime _ p
        haveI hP := GlobalTheory.T.semiabelian_germ_prime_ideal_map R' hA G₁ hG x hx (Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p) hqp
        have hle : Ideal.map ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) (Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p) ≤ p := Ideal.map_comap_le
        have hne0 : Ideal.map ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) (Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p) ≠ ⊥ := by
          intro e
          exact hq ((Ideal.map_eq_bot_iff_of_injective (GlobalTheory.T.semiabelian_germ_injective_closed_point R' hA G₁ hG x)).1 e)
        have heq : Ideal.map ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) (Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p) = p := by
          by_contra hne'
          have hlt := lt_of_le_of_ne hle hne'
          have h1' : (Ideal.map ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) (Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p)).height < 1 :=
            (Ideal.height_strict_mono_of_isPrime hlt).trans_le h1.le
          rw [ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1'
          exact hne0 h1'
        rw [← heq] at hmem
        exact Ideal.map_mono (IsLocalRing.le_maximalIdeal hqp.ne_top) hmem
  obtain ⟨u, a, hua⟩ := isUnit_mul_sq_of_faithfullyFlat _ C' _ hne ⟨u', f', hf'⟩ Hp
  have ha : a ≠ 0 := by
    rintro rfl
    apply hne
    rw [hua]
    simp
  exact GlobalTheory.T.local_square_factorization_sections G₁.left L2 h x j₀ hj₀ u a ha hua

end GlobalTheory.SquareNear
