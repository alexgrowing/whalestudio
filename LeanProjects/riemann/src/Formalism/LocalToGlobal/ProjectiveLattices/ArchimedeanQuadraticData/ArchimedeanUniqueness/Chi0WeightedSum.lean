import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.QbridgeOf
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef

noncomputable section

namespace Formalism.L2.Pj.QAt.Arch

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions

variable {D : D7} {T : Core D} {j : ℕ} {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
  [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)]

def DlogTan {K₁ : Type} [Field K₁] {D₀ : ReciprocityTheory.ChartRestriction.G.Out.DegPre K₁} (v : ReciprocityTheory.ChartRestriction.G.Out.GtPt D₀ (epsR K₁))
    (χ : D₀.X) (y : K₁) : Prop :=
  ∀ j, ⊤ ≤ LB.wchart D₀.P.L (ReciprocityTheory.ChartRestriction.G.Out.DegPre.gtφT D₀ (epsR K₁) v.b χ) j →
    TrivSqZeroExt.snd (valR (A := DualNumber K₁) (𝟙 _) _ ((v.s χ).s j).val) =
      TrivSqZeroExt.fst (valR (A := DualNumber K₁) (𝟙 _) _ ((v.s χ).s j).val) * y

noncomputable def xiVal {E : Type} [Field E] [NumberField E] {K₁ : Type} [Field K₁] {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] (τK : E →+* K₁) (ξ : Module.Dual ℤ X) (χ : X) : K₁ :=
  ∑ i, τK ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (NumberField.integralBasis E) i) *
    ((ξ ((NumberField.RingOfIntegers.basis E i) • χ) : ℤ) : K₁)

noncomputable def pairE {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (ξ : Module.Dual ℤ X) (x : X) : E :=
  ∑ i, (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (NumberField.integralBasis E) i *
    ((ξ ((NumberField.RingOfIntegers.basis E i) • x) : ℤ) : E)

structure EtaLetter (d : ArcDatumAt T j K₁) where
  A : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)
  ph : A.A ⟶ d.a.D₀.P.A
  [ph_hom : IsMonHom ph]
  vec : epsR K₁ ⟶ A.A
  vec_tan : IsTangent vec
  vec_ne : vec ≠ toUnit (epsR K₁) ≫ η[A.A]

structure S1ArchimedeanData (d : ArcDatumAt T j K₁) where
  n' : ℕ
  n'_pos : 0 < n'
  La : ℝ
  c₁ : ℝ
  xi : Module.Dual ℤ d.a.D₀.X
  xi_ne : xi ≠ 0
  sB : ∀ Tt : Over (Sp K₁), (Tt ⟶ d.a.D₀.P.A) → ReciprocityTheory.ChartRestriction.G.Out.GtPt d.a.D₀ Tt
  sB_over : ∀ Tt b, (sB Tt b).b = b ^ n'
  sB_add : ∀ Tt b b', ReciprocityTheory.ChartRestriction.G.Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))
  sB_nat : ∀ (Tt Tt' : Over (Sp K₁)) (h : Tt' ⟶ Tt) b,
    ReciprocityTheory.ChartRestriction.G.Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))
  c_kill : ∀ χ, d.a.D₀.c χ ^ n' = 1
  sT : (epsR K₁ ⟶ d.a.D₀.P.A) → ReciprocityTheory.ChartRestriction.G.Out.GtPt d.a.D₀ (epsR K₁)
  sT_def : ∀ v, ReciprocityTheory.ChartRestriction.G.Out.GtPt.IsPull (spMap (epsScaleR ((n' : K₁)⁻¹))) (sB (epsR K₁) v) (sT v)
  sT_b : ∀ v, (sT v).b = v
  kind : ∀ τ, Fin ((T.Q.Dw j).mult τ) → Option (EtaLetter d)
  eta_tie : ∀ τ k (L : EtaLetter d), kind τ k = some L → d.e τ k = sT (L.vec ≫ L.ph)
  ι₁ : K₁ →+* ℂ
  τK : (D.host.E →+* ℂ) → (D.host.E →+* K₁)
  τK_spec : ∀ τ, ι₁.comp (τK τ) = τ
  xi_zero : ∀ τ k, kind τ k = none → (d.e τ k).b = toUnit (epsR K₁) ≫ η[d.a.D₀.P.A]
  xi_dlog : ∀ τ k, kind τ k = none → ∀ χ, DlogTan (d.e τ k) χ (xiVal (X := d.a.D₀.X) (τK τ) xi χ)
  chi0 : d.a.D₀.X →₀ ℚ
  chi0_nonneg : ∀ x, 0 ≤ chi0 x
  chi0_weighted_sum : ∑ x ∈ chi0.support, chi0 x * ((d.a.be x x : ℤ) : ℚ) / 2 = d.jj
  chi0_trace : (Algebra.trace ℚ D.host.E (letI := D.host.cmStar;
      ∑ x ∈ chi0.support, (chi0 x : D.host.E) * pairE xi x * star (pairE xi x)) : ℝ) / 2 ≤ c₁
  nth : InfinitePlace K₁ → ℝ
  nth_is : ∀ σ : InfinitePlace K₁, IsThNormAt d.a.D₀.P d.a.D₀.rig d.th σ.embedding (nth σ)
  lη : ∀ τ, Fin ((T.Q.Dw j).mult τ) → InfinitePlace K₁ → ℝ
  lη_eta : ∀ τ k (L : EtaLetter d), kind τ k = some L →
    ∀ σ : InfinitePlace K₁, IsLieNormAt L.A L.vec σ.embedding (lη τ k σ)
  lη_xi : ∀ τ k, kind τ k = none → ∀ σ, lη τ k σ = 0
  la_bd : ∀ τ k (L : EtaLetter d), kind τ k = some L → ∀ (σ : InfinitePlace K₁) (v v' : ℝ),
    IsLieNormAt L.A L.vec σ.embedding v → IsLieNormAt d.a.D₀.P (L.vec ≫ L.ph) σ.embedding v' →
      v' ≤ Real.log La + v

def archAOf {d : ArcDatumAt T j K₁} (s : S1ArchimedeanData d) (n : ℕ) (σ : InfinitePlace K₁) : ℝ :=
  archA n s.nth s.lη d.μ σ

def archLrd (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.log (|((NumberField.discr E : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))

def archP {d : ArcDatumAt T j K₁} (s : S1ArchimedeanData d) : ℝ :=
  Real.log (max 1 s.c₁) / 2 + Real.log s.La + archLrd D.host.E + 2 * Real.log (2 * (D.R.f : ℝ) * (D.R.r : ℝ))

end Formalism.L2.Pj.QAt.Arch
