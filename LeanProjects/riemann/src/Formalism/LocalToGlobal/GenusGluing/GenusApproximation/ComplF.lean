import Formalism.LocalToGlobal.Columns.AdelicLemmas

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

def eP (P : HeightOneSpectrum (𝓞 F) → Prop) : E ⊗[F] Formalism.L2.Herm.Af F :=
  (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd P : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F)

def eAt (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] Formalism.L2.Herm.Af F := eP E (fun w => w = v)

def complF (v : HeightOneSpectrum (𝓞 F)) : Submonoid (𝓞 E) :=
  v.asIdeal.primeCompl.map (algebraMap (𝓞 F) (𝓞 E))

variable {E}

def locF {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) W) :
    Submodule (𝓞 E) W :=
  Formalism.HermitianLatticesTheory.locS (complF E v) L

def IntAt {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Prop :=
  ∀ i j, eAt E v * y i j ∈ Formalism.L2.Herm.intAf F E

end Formalism.L2.GenusGluing.Gen
