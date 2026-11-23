import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

def VolTO (ι : Type) : Set (ι → Fv F v ⊗[F] E) := {x | ∀ i, x i ∈ OEv (E := E) v}

def VolTOne (ι : Type) [Fintype ι] : Prop := sdE (E := E) ψ v ι (VolTO (E := E) v ι) = 1

def VolTAff (g : ℕ) (ι : Type) [Fintype ι] : Prop :=
  ∀ (b : ι → Fv F v ⊗[F] E) (S : Set (ι → Fv F v ⊗[F] E)),
    sdE (E := E) ψ v ι {w | (fun i => (w i - b i) * sc (E := E) v (g : Fv F v)⁻¹) ∈ S} =
      ((g : ℝ≥0∞) ^ (2 * Fintype.card ι))⁻¹ * sdE (E := E) ψ v ι S

def VolTLocPres (r : ℕ) : Prop :=
  ∀ S : Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E),
    sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) {z | (fun p => locZ (E := E) v z p.1 p.2) ∈ S} =
      sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) S

def VolTW (g r : ℕ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :
    Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {Y | ∀ i j, Y (i, j) ∈ OEv (E := E) v ∧
    (Y (i, j) + sigR (Fv F v) σ (Y (j, i)) - c i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}

def VolTHermInt (r : ℕ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) : Prop :=
  (∀ i j, c j i = sigR (Fv F v) σ (c i j)) ∧ ∀ i j, c i j ∈ OEv (E := E) v

def VolTHermCnt (g r : ℕ) : Prop :=
  ∀ c, VolTHermInt σ v r c →
    sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) (VolTW σ v g r c) = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹

def VolTUSet (g r : ℕ) : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E)) :=
  {p | (∀ q, p.1 q ∈ OEv (E := E) v) ∧ ∀ q, (p.2 q - p.1 q) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}

def VolTUOEq (g r : ℕ) : Prop := deepCongruenceVolume (E := E) v g r = VolTUSet (E := E) v g r

def VolTProdU (g r : ℕ) : Prop :=
  ((sdE (E := E) ψ v (UIdx r)).prod (sdE (E := E) ψ v (UIdx r))) (VolTUSet (E := E) v g r) =
    sdE (E := E) ψ v (UIdx r) (VolTO (E := E) v (UIdx r)) * ((g : ℝ≥0∞) ^ (2 * Fintype.card (UIdx r)))⁻¹

end Gen

section OfX

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def VolTZZAt (v : PlX X) : Prop :=
  ZZX X u u' ψ v = (gAt X v : ℝ) ^ (-((3 * (D.R.rS + 1) ^ 2 : ℕ) : ℤ))

def VolumeDeepCongruenceSubgroup (v : PlX X) : Prop :=
  localVolumeUnit X ψ v = (gAt X v : ℝ) ^ (-((D.R.rS * (D.R.rS + 1) : ℕ) : ℤ))

def VolTTFCong (v : PlX X) : Prop :=
  VolTHermInt X.B.I.cm.sig v D.R.rS
    (fun i j => (TFv X u' v i j - TFv X u v i j) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹)

end OfX

end Formalism.L2.SG.Pf.NcVal
