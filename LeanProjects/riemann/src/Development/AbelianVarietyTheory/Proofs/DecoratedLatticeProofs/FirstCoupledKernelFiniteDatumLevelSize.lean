import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSeventh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BadPrimesSharp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumSmallTypePrimeAnyLevelStatement

noncomputable section

namespace GlobalTheory.Core.Ht2.DatOneS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem smallDatum_xiCpl1_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (al : I.β (N.R.m - 2)) (p₀ : ChPt (R := N.R) sel mu u (N.R.m - 2)) (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (Y : Set (Sp X.E (N.R.N (N.R.m - 2 + 1)))), SmallDatum (Sall sel mu u) p₀.deco.1.N p.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH al p₀ p Y
  obtain ⟨hrow, hG, hT, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH
  have hI : I.Ok Ch sel mu cst G (N.R.m - 2) := hH.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (r : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu r P x ∈ r.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j r P x
    have hP := hrow P.1 P.2
    simp only [frsF, hP, dif_pos]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ r.deco ⟨P.1, hP⟩).1 x
  have key := @GlobalTheory.ColNorms.DatOne.smallDatum_of_frames X.E X.K _ _ _ _ _ _ (Pr.vT u) _ _ (rowSG Pr sel mu) (fun a b => Classical.propDecidable (a = b))
    p₀.deco.1 p.deco (frsF sel mu p₀) (frsF sel mu p) (hfr p₀) (hfr p) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P => Formalism.L2.Col.qOf P.1) ?_ ?_
    (fun P x => PsiAt Ch sel mu cst (N.R.m - 2) P (I.h (N.R.m - 2) al P) x ((frsF sel mu p P).symm (repY Y))) (fun _ => 1) ?_
  · rw [Finset.prod_const_one] at key
    exact key
  · intro P
    obtain ⟨i, -, hq, -⟩ := hG P.1 (hrow P.1 P.2)
    show Formalism.L2.Col.qOf P.1 ∣ _
    rw [hq]
    refine Dvd.dvd.mul_left ?_ _
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  · intro P hP
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hT P hP)
  · intro P
    have hm := hI.hm
    have h := GlobalTheory.T.movedDatum_small_typePrime_any_level CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH (N.R.m - 2) (by omega) P
      (I.h (N.R.m - 2) al P) 1 (hI.stabG _ al P (hrow P.1 P.2)) (one_mem _)
    exact GlobalTheory.ColNorms.DatOne.locSmall_joinCol h _

end GlobalTheory.Core.Ht2.DatOneS

end
