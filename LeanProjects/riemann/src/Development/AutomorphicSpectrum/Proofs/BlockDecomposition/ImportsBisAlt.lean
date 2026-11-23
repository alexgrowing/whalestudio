import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.MatrixInfinitySpan.RealMatch
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.PfSWUS.MonoSplit

theorem main : ∀ (D : D7) (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (fr : D.what₂.Tau → GL (Fin V.rank) ℂ) (e : D.what₂.Tau × Fin V.rank × Fin n × Bool →₀ ℕ) (c : ℂ), Nonempty D.what₂.Tau → (∀ τ, ((fr τ).1)ᴴ * (gramAt D V τ * s τ) * (fr τ).1 = 1) → ∃ P : D.what₂.Tau → PositivityTheory.Rg.Sw.PX V.rank n, ∀ z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ, evalPoly (MvPolynomial.monomial e c) z * gauss V l s z = ∏ τ, PositivityTheory.Rg.Sw.evX (P τ) (((fr τ)⁻¹).1 * z τ) * PositivityTheory.Rg.Sw.gs (2 * Real.pi * |l τ|) (((fr τ)⁻¹).1 * z τ) := by
  classical
  intro D n V l s fr e c hne hfr
  obtain ⟨τ0⟩ := hne
  obtain ⟨PG, hPG⟩ : ∃ PG : D.what₂.Tau → PositivityTheory.Rg.Sw.PX V.rank n, ∀ τ,
      PG τ = MvPolynomial.C (if τ = τ0 then c else 1) *
        ∏ k ∈ e.support, (if k.1 = τ then PositivityTheory.PfSWUS.SwSpanR.lz (fr τ).1 k.2 else 1) ^ (e k) :=
    ⟨_, fun τ => rfl⟩
  refine ⟨PG, fun z => ?_⟩
  have hinv : ∀ τ, (fr τ).1 * ((fr τ)⁻¹).1 = 1 := fun τ => Units.mul_inv (fr τ)
  have hZ : ∀ τ, (fr τ).1 * (((fr τ)⁻¹).1 * z τ) = z τ := fun τ => by
    rw [← Matrix.mul_assoc, hinv τ, Matrix.one_mul]

  have hG : gauss V l s z = ∏ τ, PositivityTheory.Rg.Sw.gs (2 * Real.pi * |l τ|) (((fr τ)⁻¹).1 * z τ) := by
    unfold gauss PositivityTheory.Rg.Sw.gs
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [PositivityTheory.PfSWUS.SwSpanR.trace_frame (fr τ).1 ((fr τ)⁻¹).1 _ _ (hinv τ) (hfr τ),
      PositivityTheory.PfSWUS.SwSpanR.trace_ct_mul_self]
    push_cast
    ring

  have hP : evalPoly (MvPolynomial.monomial e c) z =
      ∏ τ, PositivityTheory.Rg.Sw.evX (PG τ) (((fr τ)⁻¹).1 * z τ) := by
    set f : D.what₂.Tau × Fin V.rank × Fin n × Bool → ℂ := fun k =>
      if k.2.2.2 then (starRingEnd ℂ) (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1 with hf
    have hτ : ∀ τ, PositivityTheory.Rg.Sw.evX (PG τ) (((fr τ)⁻¹).1 * z τ) =
        (if τ = τ0 then c else 1) * ∏ k ∈ e.support, (if k.1 = τ then f k else 1) ^ (e k) := fun τ => by
      rw [hPG τ]
      simp only [PositivityTheory.Rg.Sw.evX, map_mul, MvPolynomial.eval_C, map_prod, map_pow]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases h : k.1 = τ
      · subst h
        rw [if_pos rfl, if_pos rfl]
        have := PositivityTheory.PfSWUS.SwSpanR.evX_lz (fr k.1).1 (((fr k.1)⁻¹).1 * z k.1) k.2
        unfold PositivityTheory.Rg.Sw.evX at this
        rw [this, hZ k.1, hf]
        simp only [starRingEnd_apply]
      · rw [if_neg h, if_neg h, map_one]
    simp only [hτ]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ τ0, if_pos (Finset.mem_univ _),
      Finset.prod_comm]
    unfold evalPoly
    rw [MvPolynomial.eval_monomial]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [ite_pow, one_pow]
    rw [Finset.prod_ite_eq Finset.univ k.1, if_pos (Finset.mem_univ _)]
    simp only [hf, ite_pow]
  rw [hP, hG, ← Finset.prod_mul_distrib]

end GlobalTheory.CompanionTheory.PfSWUS.MonoSplit
