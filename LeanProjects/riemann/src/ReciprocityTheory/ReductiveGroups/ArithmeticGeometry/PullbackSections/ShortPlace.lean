import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramified

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

def ShortPlaceASt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la),
      (∀ p ∈ ({2, D.host.q, D.host.d, D.host.g 0, D.host.g 1, (T.dδ j w.n).pd} : Finset ℕ),
        ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) → 0 ≤ vAtV y g

def ShortSeriesRamifiedPlaceTwo : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la),
      (((2 : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la ((2 : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
          ((D.R.e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ D.R.e) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g

def ShortPlaceBqdSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (p : ℕ),
      p ∈ ({D.host.q, D.host.d} : Finset ℕ) → ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * (1 / 2) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g

def ShortPlaceCSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (i : Fin 2)
      (πE : 𝓞 D.host.E) (τ : D.host.E →+* ℂ),
      InPsi T.Q.H τ → πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar πE} → ((D.host.g i : 𝓞 T.Q.c.F) ∈ la.asIdeal) → D.host.g i ≠ D.host.q →
      (((-(((vLa la (embK T.Q.c τ πE) : ℤ) : ℝ) * ((∑ t, ∑ k, w.aP t k : ℕ) : ℝ) +
          ((vLa la (embK T.Q.c τ (T.Q.H.bar πE)) : ℤ) : ℝ) * ((∑ t, ∑ k, w.aM t k : ℕ) : ℝ) +
          ((vLa la ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) : ℤ) : ℝ) * (D.R.f * D.R.r * w.n : ℕ))) : ℝ) : EReal) ≤
        vAtV y g

def ShortPlaceDSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la),
      (((T.dδ j w.n).pd : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la ((T.dδ j w.n).pd : T.Q.c.F) : ℤ) : ℝ) *
          ((DF w : ℝ) + 2 * D.R.f * D.R.r * w.n))) : ℝ) : EReal) ≤ vAtV y g

def ThcAssemblySt : Prop :=
  ∀ (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (s : 𝓞 T.Q.c.F) (w : WeightFamilies.Wt D j),
    s ≠ 0 →
    (∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (g : T.toTop.R j), g ∈ T.toTop.sh j w →
      (((-(((vLa la ((s : T.Q.c.F) * ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) ^ (D.R.f * D.R.r * w.n)) : ℤ) : ℝ))) : ℝ)
        : EReal) ≤ vAtV y g) →
    (recPJ hF.p j hj).Thc s w ≤ (recB hF.p.toLawsCore).Mlat j w

end ReciprocityTheory.ChartRestriction.G.PullbackSections
