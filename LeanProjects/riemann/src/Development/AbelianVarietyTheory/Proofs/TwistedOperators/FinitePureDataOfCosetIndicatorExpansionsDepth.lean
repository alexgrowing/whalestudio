import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

noncomputable section

namespace GlobalTheory.RowTest.CosetFin

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

theorem finDatum_eq {t : T} {p : Pair T} {k : ℕ} {a b : FinDatum G t p} (ha : IsCosetDatum k a) (hb : IsCosetDatum k b)
    (hP : a.P = b.P) (he : a.e = b.e) (hz : a.z = b.z) {u} (hu : a.fn u ≠ 0) (hu' : b.fn u ≠ 0) : a = b := by
  have hf := ha.fn_eq hb he hu hu'
  cases a
  cases b
  simp only at hP he hz hf
  subst hP he hz hf
  rfl

theorem pureDat_eq {t : T} {k : ℕ} {e : AE D} {d d' : PureDat G t}
    (hc : (∀ j, IsCosetDatum k (d.1 j)) ∧ ∀ i, IsCosetDatum k (d.2 i))
    (hc' : (∀ j, IsCosetDatum k (d'.1 j)) ∧ ∀ i, IsCosetDatum k (d'.2 i))
    (hp : (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧ ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1)
    (hp' : (∀ j, (d'.1 j).P = locPl G t ∧ (d'.1 j).e = e ∧ (d'.1 j).z = 1) ∧
      ∀ i, (d'.2 i).P = locPl G t ∧ (d'.2 i).e = e ∧ (d'.2 i).z = 1)
    (hx : ∀ j, ∃ u, (d.1 j).fn u ≠ 0 ∧ (d'.1 j).fn u ≠ 0) (hy : ∀ i, ∃ u, (d.2 i).fn u ≠ 0 ∧ (d'.2 i).fn u ≠ 0) : d = d' := by
  refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
  · obtain ⟨a1, a2, a3⟩ := hp.1 j
    obtain ⟨b1, b2, b3⟩ := hp'.1 j
    obtain ⟨u, hu, hu'⟩ := hx j
    exact finDatum_eq (hc.1 j) (hc'.1 j) (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm) hu hu'
  · obtain ⟨a1, a2, a3⟩ := hp.2 i
    obtain ⟨b1, b2, b3⟩ := hp'.2 i
    obtain ⟨u, hu, hu'⟩ := hy i
    exact finDatum_eq (hc.2 i) (hc'.2 i) (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm) hu hu'

end GlobalTheory.RowTest.CosetFin

namespace GlobalTheory.RowTest.CosetFin

section Sums

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
  {S : GridChoice W U} {t : T} {Φ : G.Datum} {β : CosFam G t}

theorem mem_support_of {k : ℕ} {τ₀ τ : PureDat G t →₀ ℂ} (h₀ : IsCosetExpansion S t Φ β k τ₀)
    (h : IsCosetExpansion S t Φ β k τ) {d : PureDat G t} (hd : d ∈ τ.support) : d ∈ τ₀.support := by
  obtain ⟨-, ⟨e, he, h1, h2⟩, h3⟩ := h
  obtain ⟨-, ⟨e₀, he₀, h1₀, h2₀⟩, h3₀⟩ := h₀
  have hee : e₀ = e := GlobalTheory.StepVecSum.idemSum_eq (G.V (.top 0)) he he₀
  subst hee
  choose x hx _ hx' using (h3 d hd).1
  choose y hy _ hy' using (h3 d hd).2
  have ex : ∀ j, (d.1 j).fn (x j) = 1 := fun j => by rw [hx', Set.indicator_of_mem (mem_halfCoset_self _ _ _ _)]; rfl
  have ey : ∀ i, (d.2 i).fn (y i) = 1 := fun i => by rw [hy', Set.indicator_of_mem (mem_halfCoset_self _ _ _ _)]; rfl
  have hs : (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) = τ d := by
    rw [Finsupp.sum, Finset.sum_eq_single_of_mem d hd]
    · simp [ex, ey]
    · intro d' hd' hne
      by_contra h0
      obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 h0
      exact hne (pureDat_eq (h3 d' hd') (h3 d hd) (h1 d' hd') (h1 d hd)
        (fun j => ⟨x j, Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h4) j (Finset.mem_univ _), by rw [ex]; exact one_ne_zero⟩)
        (fun i => ⟨y i, Finset.prod_ne_zero_iff.1 h5 i (Finset.mem_univ _), by rw [ey]; exact one_ne_zero⟩))
  have hxe := fun j => ((h1 d hd).1 j).2.1 ▸ hx j
  have hye := fun i => ((h1 d hd).2 i).2.1 ▸ hy i
  have hne : (τ₀.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) ≠ 0 := by
    rw [h2₀ x y hxe hye, ← h2 x y hxe hye, hs]
    exact Finsupp.mem_support_iff.1 hd
  obtain ⟨d', hd', h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 h0
  have hdd : d' = d := pureDat_eq (h3₀ d' hd') (h3 d hd) (h1₀ d' hd') (h1 d hd)
    (fun j => ⟨x j, Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h4) j (Finset.mem_univ _), by rw [ex]; exact one_ne_zero⟩)
    (fun i => ⟨y i, Finset.prod_ne_zero_iff.1 h5 i (Finset.mem_univ _), by rw [ey]; exact one_ne_zero⟩)
  exact hdd ▸ hd'

end Sums

theorem finite_pureDat_of_depth : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ), {d : PureDat G t | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}.Finite := by
  intro D T L sc G W U S t Φ β k
  by_cases h : ∃ τ₀, IsCosetExpansion S t Φ β k τ₀
  · obtain ⟨τ₀, h₀⟩ := h
    exact τ₀.support.finite_toSet.subset fun d ⟨τ, hτ, hd⟩ => mem_support_of h₀ hτ hd
  · refine Set.finite_empty.subset ?_
    rintro d ⟨τ, hτ, -⟩
    exact h ⟨τ, hτ⟩

end GlobalTheory.RowTest.CosetFin
