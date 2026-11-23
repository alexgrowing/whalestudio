import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.FibreDim

theorem charZero_residueField_genericPoint' (X : Scheme.{0}) [IsIntegral X] (hc : CharZero Γ(X, ⊤)) :
    CharZero (X.residueField (genericPoint X)) := by
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial) :=
    germ_injective_of_isIntegral X _ _
  have hr : Function.Injective (X.residue (genericPoint X)) := (X.residue (genericPoint X)).hom.injective
  exact charZero_of_injective_ringHom (f := (X.presheaf.germ ⊤ (genericPoint X) trivial ≫ X.residue _).hom)
    (by simpa using hr.comp hg)

theorem not_charZero_residueField {Z : Scheme.{0}} (p : ℕ) [Fact p.Prime] (s : Z ⟶ Sp (ZMod p)) (z : Z) :
    ¬ CharZero (Z.residueField z) := by
  intro hc
  let φ : ZMod p →+* Z.residueField z :=
    ((Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv ≫ s.appTop ≫ Z.Γevaluation z).hom
  have h0 : ((p : ZMod p) : ZMod p) = 0 := ZMod.natCast_self p
  have : (p : Z.residueField z) = 0 := by rw [← map_natCast φ p, h0, map_zero]
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this

end GlobalTheory.FibreDim

namespace GlobalTheory.FibreDim

theorem fibre_isProjOver_and_dim_le : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  intro k _ W q hq p _
  haveI hgc : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  refine ⟨?_, ?_⟩
  · letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    exact VertProj.isProjOver_strHom_zmod k W q 1 hq _
      (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) p
  · set f := q ≫ spMap (Int.castRingHom k)
    set g := spMap (Int.castRingHom (ZMod p))
    have := hq.isIntegral
    have hemb := (pullback.fst f g).isClosedEmbedding
    have hs : IsClosed (Set.range (pullback.fst f g)) := hemb.isClosed_range
    have hne : ∀ z, (pullback.fst f g) z ≠ genericPoint W := by
      intro z hz
      have h1 := charZero_residueField_genericPoint' W hq.charZero
      rw [← hz] at h1
      exact not_charZero_residueField p (pullback.snd f g) z
        (charZero_of_injective_ringHom ((pullback.fst f g).residueFieldMap z).hom.injective)
    have key := topologicalKrullDim_add_one_le hs isClosed_univ (T := W) fun x hx =>
      ⟨genericPoint W, trivial, fun ⟨z, hz⟩ => hne z hz, genericPoint_specializes x⟩
    have hW : topologicalKrullDim (Set.univ : Set W) ≤ 2 := by
      have := topologicalKrullDim_subspace_le W Set.univ
      rw [hq.dim_eq] at this
      exact this
    have heq : topologicalKrullDim (Set.range (pullback.fst f g)) =
        topologicalKrullDim ↥(pullback (C := Scheme.{0}) f g) :=
      GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb.isEmbedding rfl
    rw [← heq]
    have h2 := key.trans hW
    generalize topologicalKrullDim (Set.range (pullback.fst f g)) = d at h2 ⊢
    induction d with
    | bot => exact bot_le
    | coe n =>
      norm_cast at h2 ⊢
      induction n with
      | top => exact absurd h2 (by decide)
      | coe m =>
        norm_cast at h2 ⊢
        have h3 : m + 1 ≤ 2 := by exact_mod_cast h2
        omega

end GlobalTheory.FibreDim
