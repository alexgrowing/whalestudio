import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalHomValuationExtension
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupJetsChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeDirectionsEigenbasisValuedIntegersStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegralStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairDataStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteDvrExtensionEmbeddingResidueFieldStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationIntegersPadicComplete
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsCongruentEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusPowerEmbeddings
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TauBasisUnitDeterminant
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqMvExpOfAdditive

noncomputable section

namespace GlobalTheory.ChartCharacters

section Unif

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UnifAfterExt

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] (G : Over (Sp W)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, E, ⟨d⟩⟩ := exists_finite_split _ h₀
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, e, he⟩ := GlobalTheory.T.exists_finite_dvr_extension_embedding_residueField W k'
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, ?_⟩
  have key : (e.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') := RingHom.ext he
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e) E _ d)⟩

theorem exists_finite_ext_pelUnif {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (tK : SAB H (Sp T.Fr))
    (mK : SABMap tK t (jK T.V)) (x : Sp T.Fr ⟶ Xo.X) (mx : SABMap tK Xo.univ.t x) :
    ∃ (T' : Formalism.L2.Pj.CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)) (_ : SABMap t' t (spMap φ)),
      Function.Injective φ ∧ φ.Finite ∧ Nonempty (PELUnif (maximalIdeal T'.V) t') := by
  obtain ⟨W, _, _, _, hc, _, hf, hi, hS⟩ := exists_split_baseChange T.V t.G t.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  obtain ⟨t', m, hS'⟩ : ∃ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap (algebraMap T.V W))),
      ∃ S : SplitExt (Sp (ResidueField W)), S.IsGt ((Over.pullback (spMap (residue W))).obj t'.G) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap T.V W)) t
    exact ⟨_, m, hS⟩
  obtain ⟨gam, hsq⟩ := exists_generic_square (algebraMap T.V W) hi
  have hp := polAt_of_sabMap m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK W) gam hsq
  obtain ⟨-, P, -⟩ := isOpen_and_uniformised W hc t' hp hS'
  exact ⟨{ V := W }, algebraMap T.V W, t', m, hi, RingHom.finite_algebraMap.2 hf, ⟨P⟩⟩

end Unif

open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs GlobalTheory.CharDepth

open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw

section Map

variable {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) {dd : ℕ}

end Map

end GlobalTheory.ChartCharacters
