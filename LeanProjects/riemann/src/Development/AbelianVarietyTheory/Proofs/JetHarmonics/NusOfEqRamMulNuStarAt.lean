import Mathlib
import Development.AutomorphicArithmetic.CMTraceForms.CmDatumNatCastMemHeightOneSpectrumIff
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

noncomputable section

namespace GlobalTheory.RunDepthScale

open Formalism.MainNotions.ModuliIntegralCharts.H1 in
theorem nusOf_eq_nuN {D : D7} (B : WeightFamilies.Prov D) {j : ℕ} (w : WeightFamilies.Wt D j)
    (nu : HeightOneSpectrum (𝓞 B.KO) → ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : DepPage)
    (h1 : Q.g1 = D.host.g 0) (h2 : Q.g2 = D.host.g 1) (hq1 : Q.q1 = D.host.q) (hdd : Q.dd = D.host.d)
    (hsm : Q.sm = D.host.small) (hvd : Q.vd = vdOf D) :
    nusOf B w nu la = (ramOverZ la : ℝ) * Q.nuN (WeightAlgebra.DF w) (nu la) (resCharOf la) := by
  classical
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  unfold nusOf DepPage.nuN
  rw [H1algLink.eWL_eq la, h1, h2]
  by_cases hc : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
  · rw [dif_pos hc]
    have hch := (H1algLink.prime_mem_iff la (D.host.g_prime _)).1 (Classical.choose_spec hc)
    rw [← hch, mul_div_assoc]
    congr 1
    by_cases e0 : resCharOf la = D.host.g 0
    · rw [if_pos e0, e0]
    · rw [if_neg e0]
      have e1 : resCharOf la = D.host.g 1 := by
        generalize Classical.choose hc = i at hch
        fin_cases i
        · exact absurd hch e0
        · exact hch
      rw [if_pos e1, e1]
  · rw [dif_neg hc]
    have e0 : ¬ resCharOf la = D.host.g 0 := fun e =>
      hc ⟨0, (H1algLink.prime_mem_iff la (D.host.g_prime 0)).2 e⟩
    have e1 : ¬ resCharOf la = D.host.g 1 := fun e =>
      hc ⟨1, (H1algLink.prime_mem_iff la (D.host.g_prime 1)).2 e⟩
    rw [if_neg e0, if_neg e1]
    congr 2
    unfold DepPage.cP DepPage.IsRam
    rw [hq1, hdd, hvd, hsm, show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
    have hS : ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ↔ resCharOf la ∈ D.host.small :=
      (UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff D.host.toHostRaw B.KO la).1
    simp only [hS, H1algLink.prime_mem_iff la hq, H1algLink.prime_mem_iff la hd]
    by_cases a2 : resCharOf la ∈ D.host.small
    · rw [if_pos a2, if_pos (Or.inl a2)]
      unfold c2 vdOf
      rw [if_pos a2, Int.ceil_toNat, ← Nat.cast_mul, Nat.ceil_natCast]
    · rw [if_neg a2]
      by_cases b : resCharOf la = D.host.q ∨ resCharOf la = D.host.d
      · rw [if_pos b, if_pos (Or.inr b)]
        unfold Formalism.MainNotions.DIV.Cons.cHalf vdOf
        rw [if_neg a2, Int.ceil_toNat]
        congr 2
        ring
      · rw [if_neg b, if_neg (fun h => h.elim a2 b)]
        simp

theorem nusOf_eq_ram_mul_nuStarAt : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Top D) (h : LawsP T) (EX : ErrX D) (j : ℕ), InR D j → letI := T.Q.H.starRing; ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), nusOf (recB h.toLawsCore) (lR Tp hK j) (fun la' => (nuW (T.Q.Xo j) T.Q.c la' T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn).toReal / (ramOverZ la' : ℝ)) la = (ramOverZ la : ℝ) * nuStarAt (Xo := T.Q.Xo j) (c := T.Q.c) (depOf T.toCore EX Tp hK) la j := by
  intro D L Pm Tp hK T h EX j hj la
  letI := T.Q.H.starRing
  refine (nusOf_eq_nuN (recB h.toLawsCore) (lR Tp hK j) _ la (depOf T.toCore EX Tp hK).Q rfl rfl rfl rfl rfl rfl).trans ?_
  rw [← GlobalTheory.WeightExponents.DF_wtA h.pins hj (lR Tp hK j)]
  rfl

end GlobalTheory.RunDepthScale
