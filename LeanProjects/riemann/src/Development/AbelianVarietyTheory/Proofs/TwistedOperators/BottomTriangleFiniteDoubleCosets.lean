import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinClAndGamOrd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder Classical

namespace GlobalTheory.BotClassFin

variable {D : D7}

def finPart (V : HSp D) (g : GA D V) : GA D V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2.1

theorem continuous_finPart (V : HSp D) : Continuous (finPart V) :=
  continuous_subtype_val.comp (continuous_snd.comp (GlobalTheory.AdelicSplit.splitEquiv V).symm.continuous)

theorem finPart_mem (V : HSp D) (g : GA D V) : finPart V g ∈ GfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2.2

theorem finPart_one (V : HSp D) : finPart V 1 = 1 := by
  simp [finPart, map_one]

theorem finHom_finPart (V : HSp D) (g : GA D V) : finHom V (finPart V g) = finHom V g := by
  set p := (GlobalTheory.AdelicSplit.splitEquiv V).symm g with hp
  have e : g = p.1.1 * p.2.1 := ((GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g).symm
  have h1 : finHom V p.1.1 = 1 := p.1.2
  conv_rhs => rw [e]
  rw [map_mul, h1, one_mul]
  rfl

theorem exists_reps_of_open (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (GA D V))
    (hJ : IsOpen (J : Set (GA D V))) :
    ∃ H : Finset (GA D V), (∀ h ∈ H, h ∈ GfC V) ∧
      ∀ h ∈ GfC V, ∃ γ ∈ GQ V, ∃ r ∈ GinfC V, ∃ h₀ ∈ H, ∃ κ ∈ J, κ ∈ GfC V ∧ h = γ * r * h₀ * κ := by
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  set L : Subgroup (Bridge.Gf V) := (J ⊓ GfC V).map (finHom V).rangeRestrict with hL
  have hO : GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev V L := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev
    refine Subgroup.isOpen_of_mem_nhds (g := (1 : GA D V)) _ ?_
    have h1 : (finPart V) ⁻¹' (J : Set (GA D V)) ∈ nhds (1 : GA D V) := by
      refine (hJ.preimage (continuous_finPart V)).mem_nhds ?_
      show finPart V 1 ∈ J
      rw [finPart_one]
      exact J.one_mem
    refine Filter.mem_of_superset h1 fun g hg => ?_
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨finPart V g, ⟨hg, finPart_mem V g⟩, ?_⟩)
    exact Subtype.ext (finHom_finPart V g)
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover V hV L hO
  choose x hx using fun a => GlobalTheory.FunObj.ClassFin.gfcToGf_surjective V (c a)
  refine ⟨Finset.univ.image fun a => (x a).1, ?_, ?_⟩
  · intro h hh
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hh
    exact (x a).2
  · intro h hh
    obtain ⟨a, γ, k, e⟩ := hc ((finHom V).rangeRestrict h)
    obtain ⟨κ, ⟨hκJ, hκf⟩, hκ⟩ := Subgroup.mem_map.1 k.2
    have ex : finHom V (x a).1 = (c a).1 := congrArg Subtype.val (hx a)
    have ek : finHom V κ = k.1.1 := congrArg Subtype.val hκ
    have eγ : ((Bridge.ratF V γ : Bridge.Gf V) : _) = finHom V γ.1 := rfl
    have e' : finHom V h = finHom V γ.1 * finHom V (x a).1 * finHom V κ := by
      have := congrArg Subtype.val e
      rw [ex, ek, ← eγ]
      exact this
    refine ⟨γ.1, γ.2, γ.1⁻¹ * h * κ⁻¹ * (x a).1⁻¹, ?_, (x a).1, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩, κ, hκJ, hκf,
      by group⟩
    show finHom V _ = 1
    simp only [map_mul, map_inv, e']
    group

theorem exists_reps : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ J : Subgroup (GA D WW), IsOpen (J : Set (GA D WW)) → ∃ H : Finset (GA D WW), (∀ h ∈ H, h ∈ GfC WW) ∧
      ∀ h ∈ GfC WW, ∃ γ ∈ GQ WW, ∃ r ∈ GinfC WW, ∃ h₀ ∈ H, ∃ κ ∈ J, κ ∈ GfC WW ∧ h = γ * r * h₀ * κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX J hJ
  have hg : WW.gram = 1 := hX.stdW.1
  have hV : ∀ τ, (gramAt D WW τ).PosDef := by
    intro τ
    have : gramAt D WW τ = 1 := by
      unfold gramAt
      rw [hg]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this]
    exact Matrix.PosDef.one
  exact exists_reps_of_open WW hV J hJ

end GlobalTheory.BotClassFin

end
