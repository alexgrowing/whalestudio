import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDlNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsAlt
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LossOne
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ExpLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open GlobalTheory.SumSize.TopInt
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pair_integral_ratio_of_norm_sums : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → GlobalTheory.SumSize.PairInt.PairIntRatK := by
  intro hP hI hD
  obtain ⟨C1, hC1, hPL⟩ := UpperTheory.WildA.ker
  obtain ⟨C0, hC0, hS⟩ := UpperTheory.WildA.lossOne C1 hC1
  obtain ⟨CF2, hD⟩ := hD
  refine ⟨CF2, fun CF hCF => ?_⟩
  obtain ⟨C02, hD⟩ := hD CF hCF
  refine ⟨max C0 C02, fun ε C hC => ?_⟩
  obtain ⟨x2, hD⟩ := hD ε C (le_of_max_le_right hC)
  refine ⟨x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hch hsc hfo => ?_⟩
  have dict : DictAt ch := hD D large₂ he hx Γ Pl0 T A Ks R F hs ch hch hsc hfo
  obtain ⟨S, δ, hL⟩ := (GlobalTheory.NormSum.letters_and_sizes D (hI D).g1).1
  have hgap : ch.sc.cGap = 1 := by
    have e : ch.sc = ⟨1, CF, large₂.sc.b⟩ := hsc
    rw [e]
  obtain ⟨S', h, hE, hh⟩ := hS (G := ch.G) large₂ hs.size hs.host hgap S δ hL
  obtain ⟨l1, l2, l3⟩ := UpperTheory.WildA.expLoss D S' h _ hE
  obtain ⟨-, -, -, -, hm2, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs.size
  refine ⟨_, ⟨l1, l2, fun s => (l3 s).trans ?_⟩, ?_⟩
  · have hlog : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
    have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have hCC : C0 ≤ C := le_of_max_le_left hC
    have h1 : C0 ≤ C * D.R.m := by nlinarith
    have h2 : (0 : ℝ) ≤ D.R.f * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b := by
      have : (0 : ℝ) ≤ large₂.sc.b := by linarith
      positivity
    have := mul_le_mul_of_nonneg_right h1 h2
    unfold bOne
    linarith
  · intro t p hp w hw k d hk hcos hz hPl hdep x y hr a v hv
    have key := hPL D large₂ Γ Pl0 T A Ks R F hs ch CF hch hsc hfo hP (hI D) dict S δ hL t p hp k d hk hcos hz hPl x y hr
      w (primeUnder w) (primeUnder_prime w) (primeUnder_mem w) hw a v hv
    refine inLat_mono key ?_
    have h1 := kerLoss_mono ch.G δ C1 large₂.sc.b p.small p.big (primeUnder w)
      (hdep _ (primeUnder_prime w) (primeUnder_mem w))
    have h2 := (mul_le_mul_of_nonneg_left h1 hC1.le).trans (hh p hp _ (primeUnder_prime w))
    have h0 : (0 : ℝ) ≤ (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) := by exact_mod_cast vw_natCast_nonneg w _
    have h3 := mul_le_mul_of_nonneg_left h2 h0
    rw [mul_assoc]
    linarith
