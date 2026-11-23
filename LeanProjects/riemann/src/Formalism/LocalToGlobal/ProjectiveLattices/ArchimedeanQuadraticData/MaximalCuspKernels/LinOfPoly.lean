import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.PolyFr

noncomputable section

namespace Formalism.L2.Pj.QAt.LinOfPoly

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

private theorem det_X_ne_zero_lemma {ι n R : Type} [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]
    (g : n × n → ι) (hg : Function.Injective g) :
    (Matrix.of fun i k => (MvPolynomial.X (g (i, k)) : MvPolynomial ι R)).det ≠ 0 := by
  intro hz
  apply Matrix.det_mvPolynomialX_ne_zero n R
  apply MvPolynomial.rename_injective g hg
  rw [map_zero, AlgHom.map_det]
  convert hz using 2
  ext i k
  simp [Matrix.mvPolynomialX]

theorem arcDet_ne_zero (Dw : Datum H) (K₁ : Type) [Field K₁] : arcDet Dw K₁ ≠ 0 := by
  classical
  unfold arcDet
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  convert det_X_ne_zero_lemma (R := LaurentSeries K₁) (fun p => (⟨τ, p⟩ : ArcLt Dw))
    (fun p q hpq => by simpa using hpq)

theorem inj (Dw : Datum H) (K₁ : Type) [Field K₁] :
    Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)) := by
  first
  | exact IsFractionRing.injective _ _
  | exact NoZeroSMulDivisors.algebraMap_injective _ _
  | exact IsLocalization.injective (M := Submonoid.powers (arcDet Dw K₁)) _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K₁))

theorem arcNum_map (Dw : Datum H) (K₁ : Type) [Field K₁]
    (P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) :
    arcNum (algebraMap _ (ArcS Dw K₁) P) = P := by
  classical
  have hex : ∃ Q, algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) Q =
      algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) P := ⟨P, rfl⟩
  unfold arcNum
  rw [dif_pos hex]
  exact inj Dw K₁ hex.choose_spec

theorem laur_alg {S K : Type} [CommRing S] [Field K] [Algebra S K] (x : S) :
    algebraMap S (LaurentSeries K) x = HahnSeries.C (algebraMap S K x) := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_add (f g : Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (f + g) y = evR Xo c f y + evR Xo c g y := by
  first
  | exact evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g y
  | simp [evR, map_add]

theorem evR_smul (a : c.F) (f : Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (a • f) y = algebraMap c.F S a * evR Xo c f y := by
  first
  | exact evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) a f y
  | simp [evR, Algebra.smul_def]

end Formalism.L2.Pj.QAt.LinOfPoly

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

variable {D : D7} {T : Core D}

theorem hcomp (j : ℕ) (K₁ : Type) [Field K₁] [Algebra T.Q.c.F K₁] (a : T.Q.c.F) :
    algebraMap T.Q.c.F (ArcS (T.Q.Dw j) K₁) a =
      algebraMap (MvPolynomial (ArcLt (T.Q.Dw j)) (LaurentSeries K₁)) (ArcS (T.Q.Dw j) K₁)
        (algebraMap T.Q.c.F (MvPolynomial (ArcLt (T.Q.Dw j)) (LaurentSeries K₁)) a) := rfl

end Formalism.L2.Pj.QAt
