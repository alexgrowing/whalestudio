import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.FunDef
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem arcDet_ne_zero (K₁ : Type) [Field K₁] : arcDet Dw K₁ ≠ 0 := by
  unfold arcDet
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have h : Matrix.of (fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K₁))) =
      (MvPolynomial.rename (fun p : Fin (Dw.mult τ) × Fin (Dw.mult τ) => (⟨τ, p.1, p.2⟩ : ArcLt Dw))).mapMatrix
        (Matrix.mvPolynomialX (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (LaurentSeries K₁)) := by
    ext i k; simp [Matrix.mvPolynomialX]
  rw [h, ← AlgHom.map_det]
  intro h0
  have hinj : Function.Injective (MvPolynomial.rename
      (fun p : Fin (Dw.mult τ) × Fin (Dw.mult τ) => (⟨τ, p.1, p.2⟩ : ArcLt Dw)) :
      MvPolynomial _ (LaurentSeries K₁) → MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) :=
    MvPolynomial.rename_injective _ (fun p q hpq => by
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at hpq
      exact Prod.ext (congrArg Prod.fst hpq) (congrArg Prod.snd hpq))
  exact Matrix.det_mvPolynomialX_ne_zero (Fin (Dw.mult τ)) (LaurentSeries K₁) (hinj (h0.trans (map_zero _).symm))

instance (K₁ : Type) [Field K₁] : IsDomain (ArcS Dw K₁) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero (Dw := Dw) K₁))

end Formalism.L2.Pj.QAt
