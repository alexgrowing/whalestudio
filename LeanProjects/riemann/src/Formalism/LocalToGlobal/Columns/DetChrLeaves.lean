import Mathlib
import Formalism.LocalToGlobal.Columns.MuDetOfLoc
import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IntAtI (P : HeightOneSpectrum (𝓞 E)) (y : AfE F E) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s) * y ∈ RInt F E

def UnitAtI (P : HeightOneSpectrum (𝓞 E)) (y : (AfE F E)ˣ) : Prop := IntAtI P (y : AfE F E) ∧ IntAtI P ((y⁻¹ : (AfE F E)ˣ) : AfE F E)

def CongOneAtI (P : HeightOneSpectrum (𝓞 E)) (y : AfE F E) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ z ∈ P.asIdeal.map (toRInt F E),
    Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s) * (y - 1) = (z : AfE F E)

end Defs

def HilbertNinetyDeterminant : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n]
    (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), g ∈ UAd hc n →
      ∃ x : (AfE F E)ˣ, h90 hc.sig x = Matrix.GeneralLinearGroup.det g

def DetAtP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n]
    (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), g ∈ UAd hc n →
      (∀ P : HeightOneSpectrum (𝓞 E), ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (decoOf ST SG g).1.N ↔ z ∈ stdAt E n P) ∧
      (∀ (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n),
        (∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (decoOf ST SG g).1.N ↔ z ∈ stdAt E n P) →
        UnitAtI P (Matrix.GeneralLinearGroup.det g * (ratId F E (LinearEquiv.det f))⁻¹)) ∧
      ∀ w : SG, CongOneAtI w.1
        ((Matrix.GeneralLinearGroup.det g * (ratId F E (LinearEquiv.det ((decoOf ST SG g).1.liftFr w)))⁻¹ : (AfE F E)ˣ) : AfE F E)

def CharFactor : Prop :=
  ∀ (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field L]
    (hc : CMData F E) (ξ : Chr F E L) (S : Finset (HeightOneSpectrum (𝓞 E))) (sel : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
    (c : HeightOneSpectrum (𝓞 E) → Lˣ) (χ : ∀ P : HeightOneSpectrum (𝓞 E), (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ)
    (k : HeightOneSpectrum (𝓞 E) → Lˣ) (a : HeightOneSpectrum (𝓞 E) → Eˣ) (x : (AfE F E)ˣ),
    (∀ v, (sel v).asIdeal.under (𝓞 F) = v.asIdeal) →
    (∀ P ∈ S, ∃ P' : HeightOneSpectrum (𝓞 E), P' ≠ P ∧ P'.asIdeal.under (𝓞 F) = P.asIdeal.under (𝓞 F) ∧ P' ∉ S) →
    (∀ P ∈ S, ChainCounts.UnifAt P) →
    (h90 hc.sig).ker ≤ ξ.ker →
    (∀ y ∈ intU F E, (∀ P ∈ S, ∀ v : HeightOneSpectrum (𝓞 F), P.asIdeal.under (𝓞 F) = v.asIdeal →
      Units.map (Formalism.UG.prV (E := E) v).toMonoidHom y = 1) → ξ y = 1) →
    (∀ P : HeightOneSpectrum (𝓞 E), (¬ ∃ P' ∈ S, P'.asIdeal.under (𝓞 F) = P.asIdeal.under (𝓞 F)) → IsUnifVal ξ P (c P)) →
    (∀ P ∈ S, ∀ v : HeightOneSpectrum (𝓞 F), P.asIdeal.under (𝓞 F) = v.asIdeal → wildAt E v ≤ ξ.ker) →
    (∀ P ∈ S, IsResChar ξ P (χ P)) →
    (∀ P ∈ S, IsQValC ξ P (k P)) →
    {P : HeightOneSpectrum (𝓞 E) | ordE P (a P : E) ≠ 0}.Finite →
    (∀ P : HeightOneSpectrum (𝓞 E), UnitAtI P (h90 hc.sig x * (ratId F E (a P))⁻¹)) →
    (∀ P ∈ S, CongOneAtI P ((h90 hc.sig x * (ratId F E (a P))⁻¹ : (AfE F E)ˣ) : AfE F E)) →
    (((ξ x)⁻¹ : Lˣ) : L) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        open Classical in
        if ∃ P ∈ S, P.asIdeal.under (𝓞 F) = v.asIdeal then (1 : L) else (((c (sel v))⁻¹ ^ ordE (sel v) (a (sel v) : E) : Lˣ) : L)) *
      ∏ P ∈ S, LocE.locChar (qOf P) (((k P)⁻¹ : Lˣ) : L) (χ P)⁻¹ (a P : E)

end DetChrL

end Formalism.L2.Col
