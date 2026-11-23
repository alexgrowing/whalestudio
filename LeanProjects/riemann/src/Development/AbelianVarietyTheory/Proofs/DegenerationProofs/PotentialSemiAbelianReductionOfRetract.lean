import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnIdempotentSplitsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfRetractStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

private theorem smConn_of_semiAbelian {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (hG : IsSemiAbelian G) : SmConn G := by
  obtain ⟨c, sm, se, qc, gc, -⟩ := hG
  exact ⟨c, sm, se, qc, gc⟩

theorem exists_semiAbelian_model_of_retract (W L : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L]
    (G : Over (Sp W)) [GrpObj G] (hG : IsSemiAbelian G) (C : Over (Sp L)) [GrpObj C]
    (a : C ⟶ (Over.pullback (spMap (algebraMap W L))).obj G)
    (b : (Over.pullback (spMap (algebraMap W L))).obj G ⟶ C) [IsMonHom a] [IsMonHom b]
    (hab : a ≫ b = 𝟙 C) :
    ∃ (G₁ : Over (Sp W)) (_ : GrpObj G₁), IsSemiAbelian G₁ ∧
      ∃ e : (Over.pullback (spMap (algebraMap W L))).obj G₁ ≅ C, IsMonHom e.hom := by

  obtain ⟨F, ⟨hF, hFe⟩, huniq⟩ :=
    GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W L G G hG hG (b ≫ a) inferInstance
  have hFF : F ≫ F = F := huniq (F ≫ F) ⟨inferInstance, by
    simp only [CategoryTheory.Functor.map_comp, hFe, Category.assoc, reassoc_of% hab]⟩

  obtain ⟨G₁, _, i, r, hSm₁, hi, hr, hir, hri⟩ :=
    GlobalTheory.T.exists_retract_of_smConn_idempotent (Sp W) G (smConn_of_semiAbelian G hG) F hF hFF
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.T.isSemiAbelian_of_retract' (Sp W) G G₁ hG hSm₁ i r hr hir
  subst hri

  refine ⟨G₁, inferInstance, hG₁,
    { hom := (Over.pullback (spMap (algebraMap W L))).map i ≫ b
      inv := a ≫ (Over.pullback (spMap (algebraMap W L))).map r
      hom_inv_id := ?_
      inv_hom_id := ?_ }, ?_⟩
  · calc ((Over.pullback (spMap (algebraMap W L))).map i ≫ b) ≫ a ≫ (Over.pullback (spMap (algebraMap W L))).map r = (Over.pullback (spMap (algebraMap W L))).map i ≫ (Over.pullback (spMap (algebraMap W L))).map (r ≫ i) ≫ (Over.pullback (spMap (algebraMap W L))).map r := by
          rw [hFe]; simp only [Category.assoc]
      _ = (Over.pullback (spMap (algebraMap W L))).map (i ≫ r ≫ i ≫ r) := by simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = 𝟙 _ := by rw [reassoc_of% hir, hir, CategoryTheory.Functor.map_id]
  · calc (a ≫ (Over.pullback (spMap (algebraMap W L))).map r) ≫ (Over.pullback (spMap (algebraMap W L))).map i ≫ b = a ≫ (Over.pullback (spMap (algebraMap W L))).map (r ≫ i) ≫ b := by
          simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = 𝟙 C := by rw [hFe, Category.assoc, reassoc_of% hab, hab]
  · show IsMonHom ((Over.pullback (spMap (algebraMap W L))).map i ≫ b)
    infer_instance

theorem potModel_semiAbelian_of_retract : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (B Q : Over (Sp K)) [GrpObj B] [GrpObj Q] (i : B ⟶ Q) (r : Q ⟶ B), IsMonHom i → IsMonHom r → i ≫ r = 𝟙 B → PotModel V K Q (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ B Q _ _ i r hi hr hir hQ
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hcomp, hfin, hloc, hcompl, G, _, ⟨e, he⟩, hG⟩ := hQ

  have hab : ((Over.pullback (spMap (algebraMap K L))).map i ≫ e.inv) ≫ e.hom ≫ (Over.pullback (spMap (algebraMap K L))).map r = 𝟙 ((Over.pullback (spMap (algebraMap K L))).obj B) := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]
  obtain ⟨G₁, _, hG₁, e₁, he₁⟩ :=
    exists_semiAbelian_model_of_retract W L G hG ((Over.pullback (spMap (algebraMap K L))).obj B) ((Over.pullback (spMap (algebraMap K L))).map i ≫ e.inv) (e.hom ≫ (Over.pullback (spMap (algebraMap K L))).map r) hab
  exact ⟨W, L, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, hcomp, hfin, hloc, hcompl, G₁, ‹_›, ⟨e₁, he₁⟩, hG₁⟩

end GlobalTheory.SS
