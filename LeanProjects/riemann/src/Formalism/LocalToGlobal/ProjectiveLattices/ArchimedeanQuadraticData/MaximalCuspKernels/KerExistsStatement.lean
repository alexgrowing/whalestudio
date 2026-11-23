import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.QbridgeOf

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

variable {D : D7} {T : Core D}

abbrev ArcFam (T : Core D) (j : ℕ) : Type 1 :=
  ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁],
    ArcDatumAt T j K₁ → Prop

def KillAt (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fam : ArcFam T j) : Prop :=
  ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁],
    ∀ (d : ArcDatumAt T j K₁), Fam K₁ d →
      ∀ F : (recB h).Cusp j ka, F ∈ WeightFamilies.MggK (recB h) CR Tt cc j ka → cfOf d.yF d.μ d.jj F.1 = 0

def DetectKAt (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fam : ArcFam T j) : Prop :=
  ∀ F : (recB h).Cusp j ka,
    (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁],
        ∀ (d : ArcDatumAt T j K₁), Fam K₁ d → cfOf d.yF d.μ d.jj F.1 = 0) →
    F ∈ WeightFamilies.MggK (recB h) CR Tt cc j ka

def EnlargeAt (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (Fam : ArcFam T j) : Prop :=
  ∀ (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra T.Q.c.F K'] [Field K₁] [NumberField K₁]
    [Algebra T.Q.c.F K₁] (f : K' →ₐ[T.Q.c.F] K₁) (d : ArcDatumAt T j K'),
    Fam K' d →
    ∃ d₁ : ArcDatumAt T j K₁, Fam K₁ d₁ ∧
      ∀ F : (recB h).Cusp j ka, cfOf d₁.yF d₁.μ d₁.jj F.1 = f (cfOf d.yF d.μ d.jj F.1)

def LinAt (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (Fam : ArcFam T j) : Prop :=
  ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁],
    ∀ (d : ArcDatumAt T j K₁), Fam K₁ d →
      ∃ f : (recB h).Cusp j ka →ₗ[T.Q.c.F] K₁, ∀ F, f F = cfOf d.yF d.μ d.jj F.1

set_option synthInstance.maxHeartbeats 400000 in

def KerExistsStatement (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : Prop :=
  ∀ (Fam : ArcFam T j), KillAt h j ka CR Tt cc Fam → DetectKAt h j ka CR Tt cc Fam →
    EnlargeAt h j ka Fam → LinAt h j ka Fam →
    WeightFamilies.rhoP (recB h) CR Tt cc j ka + Module.finrank T.Q.c.F (WeightFamilies.MggK (recB h) CR Tt cc j ka) =
      Module.finrank T.Q.c.F ((recB h).Cusp j ka) →
    ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra T.Q.c.F K₁)
      (d : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → ArcDatumAt T j K₁)
      (cfL : Fin (WeightFamilies.rhoP (recB h) CR Tt cc j ka) → Module.Dual K₁ (K₁ ⊗[T.Q.c.F] (recB h).Cusp j ka)),
      (∀ i, Fam K₁ (d i)) ∧
      (∀ i (F : (recB h).Cusp j ka), cfL i ((1 : K₁) ⊗ₜ[T.Q.c.F] F) =
        cfOf (d i).yF (d i).μ (d i).jj F.1) ∧
      ∀ x : K₁ ⊗[T.Q.c.F] (recB h).Cusp j ka, (∀ i, cfL i x = 0) ↔
        x ∈ Submodule.span K₁ ((fun F : (recB h).Cusp j ka => (1 : K₁) ⊗ₜ[T.Q.c.F] F) ''
          (WeightFamilies.MggK (recB h) CR Tt cc j ka : Set ((recB h).Cusp j ka)))

end Formalism.L2.Pj.QAt
