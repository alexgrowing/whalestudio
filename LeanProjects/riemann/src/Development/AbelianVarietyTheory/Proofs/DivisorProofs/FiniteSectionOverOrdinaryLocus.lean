import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem finite_specialisations_of_finite_open {R : Type} [CommRing R] {X : Scheme.{0}} (sX : X ⟶ Sp R)
    [IsSeparated sX] (U : X.Opens) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ X) (gs : Y₀ ⟶ U.toScheme)
    (hgs : gs ≫ U.ι = s₀) [IsFinite gs] (u : X) (hu : u ∈ U) :
    {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K)
      (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀),
      spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  have hF : (s₀.base ⁻¹' {u}).Finite := by
    refine (gs.finite_preimage_singleton (⟨u, hu⟩ : U)).subset fun y hy => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hgs, hy]
    rfl
  refine (hF.image t₀.base).subset ?_
  rintro z ⟨V, K, _, _, _, _, _, _, y', z', x, h1, h2, h3, h4⟩
  have hrange : Set.range y'.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := V) w).map y'.continuous).mem_open U.isOpen (h3 ▸ hu)
  have hy''f : IsOpenImmersion.lift U.ι y' hrange ≫ U.ι = y' := IsOpenImmersion.lift_fac _ _ _
  have hE : ValuativeCriterion.Existence gs :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed gs) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) gs).1
  have hw : x ≫ gs = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ IsOpenImmersion.lift U.ι y' hrange := by
    rw [← cancel_mono U.ι, Category.assoc, hgs, Category.assoc, hy''f]
    exact h1.symm
  obtain ⟨⟨l, hl1, hl2⟩⟩ :=
    (hE { R := V, K := K, i₁ := x, i₂ := IsOpenImmersion.lift U.ι y' hrange, commSq := ⟨hw⟩ }).exists_lift
  have hl1' : spMap (algebraMap V K) ≫ l = x := hl1
  have hl2' : l ≫ gs = IsOpenImmersion.lift U.ι y' hrange := hl2
  have : IsDominant (spMap (algebraMap V K)) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)).le.trans bot_le)⟩
  have hlz : l ≫ t₀ = z' := by
    refine ext_of_isDominant_of_isSeparated (sX ≫ spMap (algebraMap ℤ R)) ?_ (spMap (algebraMap V K)) ?_
    · exact specZIsTerminal.hom_ext _ _
    · rw [reassoc_of% hl1', h2]
  refine ⟨l (IsLocalRing.closedPoint V), ?_, ?_⟩
  · simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hc : (l ≫ gs ≫ U.ι) (IsLocalRing.closedPoint V) = y' (IsLocalRing.closedPoint V) := by
      rw [reassoc_of% hl2', hy''f]
    calc s₀ (l (IsLocalRing.closedPoint V)) = (l ≫ gs ≫ U.ι) (IsLocalRing.closedPoint V) := by
          rw [hgs]; first | rfl | simp
      _ = u := hc.trans h3
  · rw [← h4, ← hlz]
    first | rfl | simp

theorem isSeparated_structure_morphism_model {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) : IsSeparated M.s := by
  obtain ⟨n, i, hi, -, e⟩ := M.qproj
  have := isProper_str R n
  rw [← e]
  infer_instance

theorem finite_specialisations_of_finite_source : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → IsFinite gs → ∀ u : M.X, u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ b N M Y₀ s₀ t₀ gs hgs hfin u hu
  have := isSeparated_structure_morphism_model M
  exact finite_specialisations_of_finite_open M.s _ Y₀ s₀ t₀ gs hgs u hu

end GlobalTheory.UPel.HT.ES.CorrQF
