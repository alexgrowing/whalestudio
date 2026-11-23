import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.Statement

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

def LocEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (_ : Formalism.BasicNotions.CMData F E) (n : ℕ) (PP : Formalism.L2.DIV.Pl E) (L : Submodule (𝓞 E) (Sp E n)),
    Formalism.HermitianLatticesTheory.loc (K := E) PP.asIdeal L = locF (Formalism.L2.DIV.underPl F PP) L

def IdemDenom : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (u : E ⊗[F] Formalism.L2.Herm.Af F), eAt E v * u ∈ Formalism.L2.Herm.intAf F E →
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ iA F E (algebraMap (𝓞 F) E r) * u ∈ Formalism.L2.Herm.intAf F E

def IdemInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F), r ∉ v.asIdeal → ∀ u : E ⊗[F] Formalism.L2.Herm.Af F,
    iA F E (algebraMap (𝓞 F) E r) * u ∈ Formalism.L2.Herm.intAf F E → eAt E v * u ∈ Formalism.L2.Herm.intAf F E

def MemLocFStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (z : Sp E n),
    z ∈ locF v (stdLat E n) ↔ ∀ i, eAt E v * iA F E (z i) ∈ Formalism.L2.Herm.intAf F E

def IdemCof : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : 𝓞 F), D ≠ 0 → ∀ u : E ⊗[F] Formalism.L2.Herm.Af F,
    iA F E (algebraMap (𝓞 F) E D) * u ∈ Formalism.L2.Herm.intAf F E →
    eP E (fun v : HeightOneSpectrum (𝓞 F) => D ∉ v.asIdeal) * u ∈ Formalism.L2.Herm.intAf F E

def IdemCalc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    (∀ P : HeightOneSpectrum (𝓞 F) → Prop, eP E P ∈ Formalism.L2.Herm.intAf F E) ∧
    (∀ P Q : HeightOneSpectrum (𝓞 F) → Prop, eP E P * eP E Q = eP E (fun v => P v ∧ Q v)) ∧
    (∀ T : Finset (HeightOneSpectrum (𝓞 F)), ∑ v ∈ T, eAt E v + eP E (fun v => v ∉ T) = 1)

def GlueExists : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (γ : HeightOneSpectrum (𝓞 F) → URat hc n), ∃ x ∈ UAd hc n,
    (∀ v ∈ T, eAt E v • ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      eAt E v • ((Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) ∧
    eP E (fun v => v ∉ T) • ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      eP E (fun v => v ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))

def Commens : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E N →
    ∃ D : 𝓞 F, D ≠ 0 ∧ (∀ y ∈ N, algebraMap (𝓞 F) (𝓞 E) D • y ∈ stdLat E n) ∧
      (∀ y ∈ stdLat E n, algebraMap (𝓞 F) (𝓞 E) D • y ∈ N)

end Formalism.L2.GenusGluing.Gen
