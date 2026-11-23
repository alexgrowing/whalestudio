import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFifth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumSmallTypePrimeAnyLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BadPrimesSharp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.UnfoldS

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.PadicUnfold GlobalTheory.PadicUnfold.Period GlobalTheory.ColNorms.Unfold

theorem locSmall_XiAt_sharp : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (P : rowSG Pr sel mu), LocSmall (Formalism.L2.Col.qOf P.1) (stdAt X.E (N.R.N i) P.1) (stdAt X.E (N.R.N (i + 1)) P.1) (XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) ((Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2)) := by
  refine ⟨2, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be P => ?_⟩
  obtain ⟨hvG, hpr, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hP : P.1 ∈ Pr.vGs := hvG _ P.2
  obtain ⟨g, -, hg, -, hg2, -⟩ := hpr _ hP
  have hom := GlobalTheory.T.movedDatum_small_typePrime_any_level CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i (by omega) P (I.h i al P) (I.h (i + 1) be P)
  obtain ⟨hH, -, -, -, -, hsharp, hI, -⟩ := H
  have hPr : Pr.Ok := hH.2.2.2.2.2.2.2.2.2.1
  have hq : (Formalism.L2.Col.qOf P.1).Prime := hg ▸ hPr.g_prime g
  rw [← hg] at hg2
  have hs' := hI.stabG (i + 1) be P hP
  replace hom := hom (hI.stabG i al P hP) hs'
  unfold lamYat at hom hs'
  rw [if_pos hP] at hom hs'
  have hE := unfolding_smallHomFunction_levelPrime_bounded hq (c' := cOf N.R i) (c := cOf N.R (i + 1)) (by unfold cOf; omega) cst.A cst.B (cst.psi P)
    (fun a ha => by
      have := GlobalTheory.GO.ChRoot.psi_root hI.cst_ok P a (by rwa [hI.depthG P hP, pow_one])
      rwa [hI.depthG P hP, pow_one] at this) _ hom
  refine ⟨fun x hx => hE.1 x (right_ne_zero_of_mul hx), fun x z hz => ?_, fun σ x => ?_⟩
  · unfold XiAt E1at
    rw [hE.2.1 x z hz]
  · have hq1 : (1 : ℝ) ≤ Formalism.L2.Col.qOf P.1 := by exact_mod_cast hq.one_le
    unfold XiAt E1at
    rw [map_mul, norm_mul]
    have h1 := (norm_volN_inv_le (K := X.K) _ _ σ).trans (Nat.cast_le.2
      (relIndex_le hg2 N.R.k N.R.rS N.R.r N.R.t (N.R.N (i + 1)) (cOf N.R (i + 1)) _ hs'))
    unfold Jat lamYat
    rw [if_pos hP, if_pos hP, if_pos hsharp]
    refine (mul_le_mul h1 (hE.2.2 σ x) (norm_nonneg _) (Nat.cast_nonneg _)).trans ?_
    rw [Nat.cast_pow, ← pow_add]
    refine pow_le_pow_right₀ hq1 ?_
    have a1 := rank_le N.R (j := i) (by omega)
    have a2 := rank_le N.R (j := i + 1) (by omega)
    have a3 : cOf N.R i + 1 ≤ N.R.m := by unfold cOf; omega
    unfold NumDatum.Nm
    generalize N.R.N i + cOf N.R i = a at a1 ⊢
    generalize N.R.N (i + 1) + cOf N.R (i + 1) = b at a2 ⊢
    generalize N.R.N N.R.m = M at a1 a2 ⊢
    have b1 : b * b ≤ M * M := Nat.mul_le_mul a2 a2
    have b2 : b * a ≤ M * M := Nat.mul_le_mul a2 a1
    calc b * b + cOf N.R i * (b * a) ≤ M * M + cOf N.R i * (M * M) := by gcongr
      _ = (cOf N.R i + 1) * M ^ 2 := by ring
      _ ≤ (2 * N.R.m ^ 2) * M ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)

end GlobalTheory.Core.Ht2.UnfoldS
