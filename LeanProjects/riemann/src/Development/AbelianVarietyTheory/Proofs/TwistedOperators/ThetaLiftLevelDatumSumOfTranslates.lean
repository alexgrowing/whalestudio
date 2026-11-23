import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdeleGeneratesPolarisationIdealConjPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitaryMoverStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesLiftLevelDatumEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftNsmulMemCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulMemLiftPointsOfCompletedHomLatticeHalfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPointsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftGroupPointsPairTrivialShiftedTensorLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledTensorLatticeLeCompletedHomLatticeOffPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedClassEqPartAddTwoMovedShiftedPointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumClassesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVectorDatumEqSumLevelClassIndicatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem lift_level_datum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ (Lv : GlobalTheory.SW.Level C.X) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (L : AddSubgroup (WO S T)), IdemTwo Lv.w ∧ (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ k₀ ∈ GfC S ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) ∧ Finite (GlobalTheory.LiftLevel.LvCls C Lv) ∧ (∀ x ∈ L, IsHalf (cA D e) x) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) ∧ (∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1) ∧ ∀ x, GlobalTheory.LiftLevel.thPDatum S T βS βT Pg Q ξ e x = ∑ᶠ c : GlobalTheory.LiftLevel.LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) * GlobalTheory.LiftLevel.indL L (x + GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)))) := by
  intro D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨hI1, hI2, hI3, hI4⟩ := GlobalTheory.T.conjugatePlacesProductIdeal_proper_odd_coprime D Pg Q e hPg h2 he
  obtain ⟨a, ha, hgen⟩ := GlobalTheory.T.exists_idele_generates_polarisationIdeal_conjPlaces D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₀, Λ', hmov, hM⟩ := GlobalTheory.T.exists_finite_unitary_mover_standard_lattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a ha
  obtain ⟨Lv, h𝔪, hw, hJ, hD2⟩ := GlobalTheory.T.conjugatePlaces_liftLevelDatum_eq D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ ha hmov hgen hI1 hI2 hI3 hI4
  obtain ⟨m1, hm1, hm1'⟩ := GlobalTheory.T.liftLattice_exists_nsmul_mem_standardTensorLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨m2, hm2, hm2'⟩ := GlobalTheory.T.nsmul_mem_lift_points_of_completed_hom_lattice_half D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  have hfin := GlobalTheory.T.finite_levelDatumClasses D S T C Lv
  refine ⟨Lv, k₀, Λ', liftL S T βS βT Pg Q e, hw, ?_, hJ, hmov.1, hM, hfin, fun x hx => hx.1,
    ⟨m1, hm1, hm1'⟩, ⟨m2, hm2, hm2'⟩,
    fun u hu => ⟨GlobalTheory.T.shiftedTensorLatticePart_mem_liftLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu, fun t ht => GlobalTheory.T.liftGroupPoints_pair_trivial_shiftedTensorLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu t ht, GlobalTheory.T.scaledTensorLattice_le_completedHomLattice_offPlaces D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu⟩,
    GlobalTheory.T.movedClass_eq_part_add_two_movedShiftedPoint D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪, GlobalTheory.T.liftVectorDatum_eq_sum_levelClassIndicators D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 hfin hD2⟩
  intro PP hPP
  rw [h𝔪]
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hPP))

end GlobalTheory.LiftLevel

end
