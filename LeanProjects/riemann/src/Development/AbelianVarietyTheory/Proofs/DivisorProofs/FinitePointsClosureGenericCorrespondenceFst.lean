import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionOverOrdinaryLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyTargetOfDvrSpecialisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyTargetOfPointPairFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgClosedEmbeddingsOfFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenyTargetsAtCharPPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES
open GlobalTheory.UPel.HT.ES.CorrQF

theorem closure_points_finite_fst : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ u : M.X, {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp hpR r w j c hw huw hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hψ htj u
  by_cases hu : u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))
  · exact GlobalTheory.T.finite_section_over_ordinary_locus p D R b N M Y₀ s₀ t₀ gs hgs hfs u hu
  · set Z := {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} with hZ
    have key := fun (z : Z) => GlobalTheory.T.exists_pIsogenyTarget_of_dvr_specialisation p D R b N hN hNp c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ u z.1 z.2
    choose k hk _ σ ζ hζ hT using key
    obtain ⟨L, _, _, g, h, hg⟩ := GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family (M.X.residueField u) Z k σ
    refine (Set.Finite.biUnion (GlobalTheory.T.finite_pIsogenyTargets_at_charP_point p D R b N hN hNp hm c M u hu L h) fun ζ' _ => Set.finite_range (fun q : Sp L => ζ' q)).subset ?_
    intro z hz
    have h1 := GlobalTheory.T.isPIsogenyTargetOfPointPair_field_extension p D R b N M c (k ⟨z, hz⟩) L (g ⟨z, hz⟩) _ _ (hT ⟨z, hz⟩)
    have e : spMap (g ⟨z, hz⟩) ≫ spMap (σ ⟨z, hz⟩) ≫ M.X.fromSpecResidueField u = spMap h ≫ M.X.fromSpecResidueField u := by
      rw [← Category.assoc, ← hg ⟨z, hz⟩]
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [← Category.assoc] at h1
    simp only [Set.mem_iUnion, Set.mem_range]
    refine ⟨spMap (g ⟨z, hz⟩) ≫ ζ ⟨z, hz⟩, ?_, Classical.arbitrary _, ?_⟩
    · simpa [e] using h1
    · rw [Scheme.Hom.comp_apply, hζ ⟨z, hz⟩ _]

end GlobalTheory.UPel.HT.ES
