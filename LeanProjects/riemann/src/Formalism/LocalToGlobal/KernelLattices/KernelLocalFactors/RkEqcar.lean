import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPAmbOfTiesD
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkConj
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkThindEq
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.ChainOneOkF

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.Cd.CarC

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m} (u : Pr.Word)
  {D : Car} (s : Cd.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ) (χ : Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem thIndEq_ambOf_car (hok : s.Ok) (hcc : Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Cd.TaylorLogMetric.IsChi D χ)
    {a b : ℕ} (ha : Even a) (hb : Even b) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) {D' : ℕ} (hD : 0 < D')
    (hLa : (Cd.ambOf s B χ cD : Amb X).LaHyp a b Sall) : (Cd.ambOf s B χ cD : Amb X).ThIndEq a b Sall D' :=
  theta_coset_indicator_natural X _ a b Sall D' (ambOf_conj s B χ cD hok) hD hLa
    (eqLaw_ambOf_of s B χ cD hok (Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SqG.eqP_car B hcc hδ χ hχ) ha hb)

theorem thEquivP_ambOf_tiesD (hok : s.Ok) (hcc : Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Cd.TaylorLogMetric.IsChi D χ)
    (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hg : XiOffG Pr (mu : Chr X.F X.E X.K)) (hT : LawTies W Ch sel mu cst G) (hTu : 0 < Pr.T u) {i : ℕ} (hi : i < R.m) (e : X.Tau → ℤ)
    (he : ∀ τ, (e τ : ℚ) = (W.row τ).e ⟨i, hi⟩)
    (hLa : (Cd.ambOf s B χ cD : Amb X).LaHyp (R.N i) (R.N (i + 1)) (Sall sel mu u))
    (hrat : (Cd.ambOf s B χ cD : Amb X).JetsRatDeg (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i)) :
    ThEquivP (stepT W Ch sel mu cst (Cd.ambOf s B χ cD) u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho := by
  have he' : ∀ τ, (e τ : ℚ) = (W.hc u τ).e ⟨i, hi⟩ := by
    intro τ
    rw [he τ, ← hT.2.2.2 u τ]
    rfl
  exact thEquivP_stepT_ofD W Ch sel mu cst (Cd.ambOf s B χ cD) u hi e he' hrat (eOmega_ambOf_of s B χ cD (B.stdOK hcc hδ) _ _)
    (thIndEq_ambOf_car s B χ cD hok hcc hδ hχ (even_rankN R i) (even_rankN R (i + 1)) _ (modulus_pos sel mu cst u hTu) hLa)
    (chiLaw_ambOf_of s B χ cD hok hχ (even_rankN R i) (even_rankN R (i + 1)))
    (muProdLaw_of hX hPr hsel hg hT i hi e he _) (muProdLaw_of hX hPr hsel hg hT i hi e he _)

end Step

section All

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {u : Pr.Word} {m2 : ℕ}
  {D : Car} (s : Cd.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ) (χ : Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem thEquivP_ambOf_car (hok : s.Ok) (hcc : Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Cd.TaylorLogMetric.IsChi D χ)
    (hX : X.Ok) (hX1 : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok) (hsel : IsSel X sel)
    (hg0 : XiOffG Pr ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (Gc : ChGlob X R.m)
    {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied Gc.σ₀ (fun j τ => (W.row τ).e j) Gc.mu0 eta) (hWe : Ch.WeilTied Gc.σ₀ Gc.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs → ∃ y : X.K, Gc.σ₀ y = ((((Gc.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    (hm : R.m = m2 + 2) (e : ℕ → X.Tau → ℤ) (he : ∀ i (hi : i < R.m) τ, (e i τ : ℚ) = (W.row τ).e ⟨i, hi⟩)
    (hLa : ∀ i j, (Cd.ambOf s B χ cD : Amb X).LaHyp (R.N i) (R.N j) (Sall sel (mu0 X.F X.E X.K S) u))
    (hRat : ∀ i, i < R.m → (Cd.ambOf s B χ cD : Amb X).JetsRatDeg (R.N i) (R.N (i + 1)) (Sall sel (mu0 X.F X.E X.K S) u)
      (cAof sel (mu0 X.F X.E X.K S) (ookCstR Ch sel S Gc) * cBof sel (mu0 X.F X.E X.K S) (ookCstR Ch sel S Gc) u) (stepDeg W u i)) :
    ∀ i, i < R.m → ThEquivP (stepT W Ch sel (mu0 X.F X.E X.K S) (ookCstR Ch sel S Gc) (Cd.ambOf s B χ cD) u i (W.lamTrue u (i + 1)))
      (Sall sel (mu0 X.F X.E X.K S) u) (cAof sel (mu0 X.F X.E X.K S) (ookCstR Ch sel S Gc) * cBof sel (mu0 X.F X.E X.K S) (ookCstR Ch sel S Gc) u)
      (colValF W sel (mu0 X.F X.E X.K S) u i).rho (colValF W sel (mu0 X.F X.E X.K S) u (i + 1)).rho := by
  have hL := oneIdx_ok_closed sel S hX hPr hCh h4 Gc hT hWe hval hm
  have hTies : LawTies W Ch sel (mu0 X.F X.E X.K S) (ookCstR Ch sel S Gc) Gc := lawTies_of_ok W Ch sel _ _ _ Gc m2 hL hW ⟨eta, hT⟩
  exact fun i hi => thEquivP_ambOf_tiesD u s B χ cD hok hcc hδ hχ hX1 hPr hsel hg0 hTies (hPr.T_prime u).pos hi (e i) (he i hi) (hLa _ _) (hRat i hi)

end All

end Formalism.L2.Ker.Cd.CarC
