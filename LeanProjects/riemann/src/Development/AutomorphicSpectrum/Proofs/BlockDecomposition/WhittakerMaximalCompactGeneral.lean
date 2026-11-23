import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGenLt
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolValueAtFinsetSum
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

theorem data_zero_of_data {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
    {bs : Module.Basis (Fin d) F E} {ψ} {ι : Type} [Fintype ι] {θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν}
    (h : PositivityTheory.SiegelWeilFormula.Gen.Dat (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν) :
    PositivityTheory.SiegelWeilFormula.Gen.Dat0 (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν :=
  { cm := h.cm, herm := h.herm, hT := h.hT, det := h.det, chr := h.chr, places := h.places,
    frames := h.frames, haar := h.haar, co := h.co, std := h.std, pure := h.pure, prod := h.prod,
    sdW := h.sdW, sdH := h.sdH }

theorem whitKAOfGenLt : PositivityTheory.PfSWUS.WhitKAOfGenLt := by
  intro hGen hDict hAn D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, vals, ⟨t, ht⟩, hv, hm⟩ := hDict D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν hS.hν
  have key : ∀ j, HolValueAt (whitT ψ V μ lam nb w H (φs j) (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n) (vals j) := by
    intro j
    obtain ⟨d, bs, θG, lG, εG, frG, gG, PG, lamG, L₁, L₂, ΦG, Φf, Φv, μG, νG, ψG, hDat, C, ⟨t', ht'⟩, hval⟩ := hm j
    have h := hGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (data_zero_of_data hDat) hDat.lt (hAn D n V hR) False.elim
      ⟨t', fun z hz => (ht' z hz).1⟩ ν 𝓕 hS.hν h𝓕
    have e : ((V.rank : ℂ) - n) / 2 = s0 V n := by
      simp only [s0]
      ring
    rw [hval ν 𝓕 hS.hν h𝓕]
    rw [one_mul] at h
    have h2 := (holValueAt_const C _).mul h
    rw [e] at h2
    exact h2.congr ⟨t', fun z hz => ((ht' z hz).2).symm⟩
  rw [hv]
  exact (holValueAt_finset_sum Finset.univ fun j _ => key j).congr ⟨t, fun z hz => (ht z hz).symm⟩

end GlobalTheory.CompanionTheory.IwaAd

end
