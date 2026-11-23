import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

variable {D : D7} {T : Core D}

structure QDataAt (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) where
  K₁ : Type
  [fK : Field K₁]
  [nfK : NumberField K₁]
  [alg : Algebra T.Q.c.F K₁]
  d : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → ArcDatumAt T j K₁
  cfL : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) →
    Module.Dual K₁ (K₁ ⊗[T.Q.c.F] (recB h).Cusp j ka)
  cfL_eq : ∀ i (F : (recB h).Cusp j ka),
    cfL i ((1 : K₁) ⊗ₜ[T.Q.c.F] F) = cfOf (d i).yF (d i).μ (d i).jj F.1

attribute [instance] QDataAt.fK QDataAt.nfK QDataAt.alg

variable {h : LawsCore T} {j : ℕ} {ka : WeightFamilies.Wt D j} {CR Tt cc : ℝ}

def KerAt (q : QDataAt h j ka CR Tt cc) : Prop :=
  ∀ x : q.K₁ ⊗[T.Q.c.F] (recB h).Cusp j ka, (∀ i, q.cfL i x = 0) ↔
    x ∈ Submodule.span q.K₁ ((fun F : (recB h).Cusp j ka => (1 : q.K₁) ⊗ₜ[T.Q.c.F] F) ''
      (WeightFamilies.MggK (recB h) CR Tt cc j ka : Set ((recB h).Cusp j ka)))

def FinAt (q : QDataAt h j ka CR Tt cc) (large₂ : SizeData₂ D) (Cc Ac : ℝ)
    (be : HeightOneSpectrum (𝓞 T.Q.c.F) → ℝ)
    (s : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → HeightOneSpectrum (𝓞 q.K₁) → ℝ) : Prop :=
  (∀ la, 0 ≤ be la) ∧ (Function.support be).Finite ∧
  (∑ᶠ la, be la * WeightFamilies.lnN (recB h) la) / WeightFamilies.degO (recB h) ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size ∧
  (∀ i, (Function.support (s i)).Finite) ∧
  ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (w : HeightOneSpectrum (𝓞 q.K₁)), LiesOver w la →
    ∀ i, ∀ F ∈ (recB h).Mlat j ka, q.cfL i ((1 : q.K₁) ⊗ₜ[T.Q.c.F] F) ≠ 0 →
      -((w.asIdeal.ramificationIdx (𝓞 T.Q.c.F) : ℝ) * be la) ≤
        (ordAt w (q.cfL i ((1 : q.K₁) ⊗ₜ[T.Q.c.F] F)) : ℝ) + s i w

def ArchAtQ (q : QDataAt h j ka CR Tt cc)
    (a : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → InfinitePlace q.K₁ → ℝ) (Carch : ℝ) : Prop :=
  ∀ (σ : InfinitePlace q.K₁) i, ∀ F ∈ (recB h).Mlat j ka,
    q.cfL i ((1 : q.K₁) ⊗ₜ[T.Q.c.F] F) ≠ 0 →
      Real.log (σ (q.cfL i ((1 : q.K₁) ⊗ₜ[T.Q.c.F] F))) + a i σ ≤
        Real.log ((recB h).supN j ka (σ.embedding.comp (algebraMap T.Q.c.F q.K₁)) F) + Carch

def DegAt (q : QDataAt h j ka CR Tt cc)
    (s : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → HeightOneSpectrum (𝓞 q.K₁) → ℝ)
    (a : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → InfinitePlace q.K₁ → ℝ) (Bdeg : ℝ) : Prop :=
  ∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace q.K₁, (σ.mult : ℝ) * a i σ) /
    (Module.finrank ℚ q.K₁ : ℝ) ≤ Bdeg

theorem qbridge_of (large₂ : SizeData₂ D) (Ch Ah Cc Ac : ℝ) (q : QDataAt h j ka CR Tt cc)
    (be : HeightOneSpectrum (𝓞 T.Q.c.F) → ℝ)
    (s : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → HeightOneSpectrum (𝓞 q.K₁) → ℝ)
    (a : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → InfinitePlace q.K₁ → ℝ) (Carch Bdeg : ℝ)
    (hK : KerAt q) (hF : FinAt q large₂ Cc Ac be s) (hA : ArchAtQ q a Carch) (hD : DegAt q s a Bdeg)
    (hconj : ∀ τ F, (recB h).supN j ka ((starRingEnd ℂ).comp τ) F = (recB h).supN j ka τ F)
    (hroom : WeightFamilies.PPv D large₂ Ch Ah * ka.size + Carch + Bdeg +
        Real.log (WeightFamilies.rhoP (recB h) CR Tt cc j ka : ℝ) / 2 ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size) :
    QBridgeAt large₂ (recB h) j ka CR Ch Ah Cc Ac Tt cc :=
  ⟨q.K₁, q.fK, q.nfK, q.alg, q.cfL, be, s, a, Carch, Bdeg, hK, hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1,
    hF.2.2.2.2, hconj, hA, hD, hroom⟩

end Formalism.L2.Pj.QAt
