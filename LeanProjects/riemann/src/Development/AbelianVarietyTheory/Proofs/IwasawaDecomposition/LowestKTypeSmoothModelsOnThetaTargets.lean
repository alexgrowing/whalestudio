import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjModelExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowSmooth

open GlobalTheory.ConjDS GlobalTheory.ConjExt Formalism.MainNotions.S

variable {D : D7} {V : HSp D}

def glue {S : D.what₂.Tau → D.what₂.Tau → SPar} (N : ∀ τ, DSModel V (S τ)) : DSModel V fun τ => S τ τ where
  H τ := (N τ).H τ
  σ τ := (N τ).σ τ
  lam τ := (N τ).lam τ
  ε τ := (N τ).ε τ
  fr τ := (N τ).fr τ
  enum τ := (N τ).enum τ
  ds τ := (N τ).ds τ
  fr_unit τ := (N τ).fr_unit τ
  fr_gram τ := (N τ).fr_gram τ

theorem dualPar_dualPar (S : SPar) : dualPar (dualPar S) = S := by
  unfold dualPar
  ext x
  simp only [Finset.mem_image]
  exact ⟨fun ⟨_, ⟨y, hy, e⟩, e'⟩ => by subst e e'; simpa using hy,
    fun hx => ⟨(-x.1, x.2), ⟨x, hx, rfl⟩, by simp⟩⟩

theorem low_of_conj {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (h : lowKSub ((conjModel M).ε τ) ((conjModel M).lam τ) ((conjModel M).σ τ) ≤ (conjModel M).sm τ) :
    lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
  intro w hw
  let c : (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := cj (M.H τ)
  have h1 := h (lowKSub_transfer (ε := M.ε τ) (ε' := (conjModel M).ε τ) (σ' := (conjModel M).σ τ) (fun _ => rfl) c
    (fun _ _ => rfl) hw)
  have h2 : ∀ y ∈ (conjModel M).sm τ, c y ∈ M.sm τ := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (smoothVec_map c (conj_rep M τ) hy)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearIsometryEquiv.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have h3 := h2 _ h1
  simpa using h3

theorem shape_at {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (h : HCParam D.R) {p q : ℕ}
    (hn : V.rank = D.R.r) (hpq : p + q = V.rank)
    (hS : S τ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) :
    Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ p ≤ V.rank, ∀ a, M.ε τ a = decide ((a : ℕ) < p) := by
  have key := GlobalTheory.HolDict.isEnum_holPar_kapW h hn hpq (hS ▸ M.enum τ)
  refine ⟨⟨(M.enum τ).1, fun a => ?_⟩, p, by omega, fun a => (key a).2⟩
  obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int h a
  obtain ⟨s, hs⟩ := Formalism.L2.NTheta.odd_r D.R
  refine ⟨z - s, ?_⟩
  have hr : ((V.rank : ℕ) : ℝ) = 2 * s + 1 := by rw [hn, hs]; push_cast; rfl
  rw [(key a).1, hz, hr]
  push_cast
  ring

theorem lowSm_MW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i σ, LowSm (R.MW i σ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i σ
  have key : ∀ τ, ∃ (S : D.what₂.Tau → SPar) (N : DSModel (Wc D i) S),
      (Formalism.QuantumDeterminants.IsHCParam (N.lam τ) ∧ ∃ p ≤ (Wc D i).rank, ∀ a, N.ε τ a = decide ((a : ℕ) < p)) ∧
      (lowKSub (N.ε τ) (N.lam τ) (N.σ τ) ≤ N.sm τ →
        lowKSub ((R.MW i σ).ε τ) ((R.MW i σ).lam τ) ((R.MW i σ).σ τ) ≤ (R.MW i σ).sm τ) := fun τ => by
    have hpq := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i τ
    by_cases hb : labE σ (lab σ τ) = tauE D τ
    · exact ⟨_, R.MW i σ, shape_at _ τ (D.hc (lab σ τ)) (rank_Wc i) hpq (if_pos hb), id⟩
    · refine ⟨_, conjModel (R.MW i σ), shape_at _ τ (D.hc (lab σ τ)) (rank_Wc i) hpq ?_, low_of_conj _ τ⟩
      unfold Links.parAt
      rw [if_neg hb, dualPar_dualPar]
      rfl
  choose S N hN hL using key
  exact fun τ => hL τ ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ (glue N) hN).1 τ)

end GlobalTheory.LowSmooth

end
