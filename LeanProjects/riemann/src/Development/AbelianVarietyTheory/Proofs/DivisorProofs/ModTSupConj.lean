import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondESupConj
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem modT_sup_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (t : T),
    modT G t ⊔ D.host.conj • modT G t = ⊤ := by
  intro D T L sc μ₀ hL G t
  classical
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hund : ∀ PP PP' : HeightOneSpectrum (𝓞 D.host.E), PP.asIdeal = D.host.conj • PP'.asIdeal →
      PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) := by
    intro PP PP' h
    have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv PP' PP := by
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
      intro x y hxy
      have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
      rw [hy, h]
      exact Ideal.smul_mem_pointwise_smul_iff.symm
    exact (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) PP' PP).2
      (Or.inr hc)
  have hmax' : ∀ PP : HeightOneSpectrum (𝓞 D.host.E), (D.host.conj • PP.asIdeal).IsMaximal := by
    intro PP
    have := PP.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => PP.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have hmem : ∀ w ∈ twPl G t, w ∈ L.Q t ∧ w ∉ G.pl.W0 := by
    intro w hw
    rw [twPl, Finset.mem_filter, GlobalTheory.FunObj.locPl, Finset.mem_union] at hw
    exact ⟨hw.1.resolve_left hw.2, hw.2⟩
  have hoff : ∀ w ∈ twPl G t, w.under (𝓞 D.host.F) ∉ G.pl.S0 := by
    intro w hw hS
    obtain ⟨hQ, hW⟩ := hmem w hw
    rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
    · exact G.pl.levelPlace_ne_basePlace t w hQ h0
    · apply hW
      rw [G.pl.w_Q t w hQ h1]
      exact Finset.mem_image_of_mem _ hS
  have hAB : ∀ v ∈ G.pl.S0, ∀ w ∈ twPl G t, (G.pl.w v).asIdeal ≠ D.host.conj • w.asIdeal := by
    intro v hv w hw h
    exact hoff w hw (by rw [← hund _ _ h, G.pl.under_w hv]; exact hv)
  have hBA : ∀ w ∈ twPl G t, ∀ v ∈ G.pl.S0, w.asIdeal ≠ D.host.conj • (G.pl.w v).asIdeal := by
    intro w hw v hv h
    exact hoff w hw (by rw [hund _ _ h, G.pl.under_w hv]; exact hv)
  have hBB : ∀ w ∈ twPl G t, ∀ w' ∈ twPl G t, w.asIdeal ≠ D.host.conj • w'.asIdeal := by
    intro w hw w' hw' h
    refine (hL.Q_pl t w' (hmem w' hw').1).2 w (hmem w hw).1 fun c hc => ⟨D.host.conj • c, ?_, ?_⟩
    · rw [h]; exact Ideal.smul_mem_pointwise_smul _ _ _ hc
    · exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [modT, smul_mul', ← Ideal.isCoprime_iff_sup_eq]
  refine IsCoprime.mul_left (IsCoprime.mul_right ?_ ?_) (IsCoprime.mul_right ?_ ?_) <;> rw [Ideal.isCoprime_iff_sup_eq]
  · exact condE_sup_conj G.pl
  · rw [Finset.smul_prod']
    refine Ideal.prod_sup_eq_top fun v hv => Ideal.sup_prod_eq_top fun w hw => ?_
    exact Ideal.pow_sup_eq_top (Ideal.IsMaximal.coprime_of_ne (G.pl.w v).isMaximal (hmax' w) (hAB v hv w hw))
  · rw [GlobalTheory.FunObj.SqNum.condE, Finset.smul_prod']
    simp only [smul_pow']
    refine Ideal.prod_sup_eq_top fun w hw => Ideal.sup_prod_eq_top fun v hv => ?_
    exact Ideal.sup_pow_eq_top (Ideal.IsMaximal.coprime_of_ne w.isMaximal (hmax' _) (hBA w hw v hv))
  · rw [Finset.smul_prod']
    exact Ideal.prod_sup_eq_top fun w hw => Ideal.sup_prod_eq_top fun w' hw' =>
      Ideal.IsMaximal.coprime_of_ne w.isMaximal (hmax' w') (hBB w hw w' hw')

end GlobalTheory.SqTop

end
