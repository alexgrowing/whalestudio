import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThIndEqAmbOfOf
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section Rec

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m} (u : Pr.Word)
  {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem thEquivP_ambOf_ties (hIT : ThIndOfEq) {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hg : XiOffG Pr (mu : Chr X.F X.E X.K)) (hT : LawTies W Ch sel mu cst G) (hTu : 0 < Pr.T u) {i : ℕ} (hi : i < R.m) (e : X.Tau → ℤ)
    (he : ∀ τ, (e τ : ℚ) = (W.row τ).e ⟨i, hi⟩)
    (hLa : (ambOf s B χ cD : Amb X).LaHyp (R.N i) (R.N (i + 1)) (Sall sel mu u))
    (hrat : (ambOf s B χ cD : Amb X).JetsRat (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)) :
    ThEquivP (stepT W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho := by
  have he' : ∀ τ, (e τ : ℚ) = (W.hc u τ).e ⟨i, hi⟩ := by
    intro τ
    rw [he τ, ← hT.2.2.2 u τ]
    rfl
  exact thEquivP_ambOf W Ch sel mu cst u s B χ cD hN hi e he' hrat
    (thIndEq_ambOf_of s B χ cD hIT hN (even_rankN R i) (even_rankN R (i + 1)) _ (modulus_pos sel mu cst u hTu) hLa)
    (muProdLaw_of hX hPr hsel hg hT i hi e he _) (muProdLaw_of hX hPr hsel hg hT i hi e he _)

end Rec

end Formalism.L2.Ker
