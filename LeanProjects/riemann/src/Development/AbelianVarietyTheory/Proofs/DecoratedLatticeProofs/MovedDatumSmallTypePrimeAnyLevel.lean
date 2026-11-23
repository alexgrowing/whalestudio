import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BadPrimesSharp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFourth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmallStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.MovedDatumS

theorem omPhi_locSmall_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 1 < N.R.m → ∀ (P : rowSG Pr sel mu) (h : AutY X N.R i) (h' : AutY X N.R (i + 1)), h ∈ stabL X.E _ (lamYat (Pr := Pr) i P.1) → h' ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1) → LocSmall (Formalism.L2.Col.qOf P.1) (lamYat (Pr := Pr) (R := N.R) i P.1) (lamYat (Pr := Pr) (R := N.R) (i + 1) P.1) (omPhi Ch sel mu cst i P h h') 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi P h h' hh hh'
  have hP : P.1 ∈ Pr.vGs :=
    (GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H).1 P.1 P.2
  have hs : cst.sharp = true := H.2.2.2.2.2.1
  unfold omPhi muAt
  unfold lamYat LocE.lamY at hh hh' ⊢
  refine GlobalTheory.ColNorms.MovedDatum.locSmall_om _ _ _ hh hh' ?_
  unfold PhiAt
  rw [hs]
  simp only [if_pos hP, if_true]
  have hq0 : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hN : ∀ j, N.R.N j = N.R.k + j * N.R.t + j := fun j => by unfold Ranks.N; ring
  have h2 := N.R.two_le_m
  refine GlobalTheory.T.symmetricLevel_typePrime_datum_locally_small X.E X.K P.1 _ _ _ _ _ _ _ (i + 1) _ _ _ _ hq0 (Ideal.absNorm_mem _) ?_ ?_ ?_ ?_ ?_
  · rw [hN, Nat.add_sub_cancel]; unfold Formalism.L2.Col.cOf Ranks.r; omega
  · rw [hN, hN, add_mul]; unfold Formalism.L2.Col.cOf; omega
  · rw [hN]; omega
  · rw [hN]; omega
  · unfold Ranks.r; omega

end GlobalTheory.Core.Ht2.MovedDatumS
