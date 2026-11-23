import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleExistsNonzeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFormula

theorem conj_finsum {α : Type*} (f : α → ℂ) : starRingEnd ℂ (∑ᶠ a, f a) = ∑ᶠ a, starRingEnd ℂ (f a) := by
  by_cases hs : (Function.support f).Finite
  · exact map_finsum (starRingEnd ℂ) hs
  · have hs' : ¬ (Function.support fun a => starRingEnd ℂ (f a)).Finite := by
      have : (Function.support fun a => starRingEnd ℂ (f a)) = Function.support f := by ext a; simp
      rwa [this]
    rw [finsum_of_infinite_support hs, finsum_of_infinite_support hs', map_zero]

end GlobalTheory.BotFormula

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.BotFormula.bottom_big : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T, starRingEnd ℂ (P.coord h T) = Ω * u * X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g := by
  intro hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := GlobalTheory.T.bottom_triangle_nonzero_period hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := GlobalTheory.T.bottom_triangle_exists_nonzero hPr hK hM hI hB
  refine ⟨max cA cB, fun ε CF hCF => ?_⟩
  obtain ⟨CA, xA, hA⟩ := hA ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max CA CB, max xA xB, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have hA := hA C (le_trans (le_max_left _ _) hC0) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  have hB' := hB' C (le_trans (le_max_right _ _) hC0) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hL G
  intro W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω₀, hΩ₀, HK⟩ := hA W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨v, hv, HC⟩ := hB' W hψ i j A A' WW X δ t0 hX
  refine ⟨(v * Ω₀)⁻¹, inv_ne_zero (mul_ne_zero hv hΩ₀), fun s Q P P' hP => ?_⟩
  obtain ⟨u, hu, huQ, huU, HK⟩ := HK s Q P P' hP
  have huQ' : u⁻¹ ∈ Qbar := inv_mem huQ
  refine ⟨u⁻¹, inv_ne_zero hu, huQ', fun p _ hp lam => ?_, fun ea ed h g hg T => ?_⟩
  · have h1 := GlobalTheory.BotFormula.lamC_mul lam huQ huQ'
    rw [mul_inv_cancel₀ hu] at h1
    have h2 : lamC lam (1 : ℂ) = 1 := by
      unfold lamC
      rw [dif_pos (one_mem Qbar)]
      exact (congrArg lam (Subtype.ext rfl : (⟨1, one_mem Qbar⟩ : Qbar) = 1)).trans (map_one lam)
    rw [h2] at h1
    have h3 := congrArg norm h1
    rw [norm_mul, huU p hp lam, one_mul, norm_one] at h3
    exact h3.symm
  have pts : ∀ x : GA D P.a, ∃ y : GA D A, GlobalTheory.BotFormula.IsFinPt A y x := fun x =>
    GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne A hX.std.1 x ea.symm
  choose pt hpt using pts
  rw [HC s Q P P' hP ea ed g pt hpt T]
  simp_rw [HK ea ed h g _ (pt _) hg (hpt _) T]
  rw [GlobalTheory.NormSum.Pair.coord, GlobalTheory.BotFormula.conj_finsum]
  have e1 : ∀ x : GlobalTheory.NormSum.Cls D P.a (GlobalTheory.NormSum.intG D P.a),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * (Ω₀ * u * starRingEnd ℂ (P.term x.out h T)) =
      (Ω₀ * u) * starRingEnd ℂ (((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * P.term x.out h T) := by
    intro x
    rw [map_mul, map_inv₀, map_natCast]; ring
  simp_rw [e1, ← mul_finsum]
  field_simp
