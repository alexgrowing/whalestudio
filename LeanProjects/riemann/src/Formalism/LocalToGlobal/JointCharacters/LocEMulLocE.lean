import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.JoinChr

open Formalism.L2.Theta

variable (D : D7)

def locE (e : AE D) (k : D.host.E) : AE D := 1 + e * (incA D k - 1)

def IsPlIdem (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  e * e = e ∧
  (∃ v ε, IsPlaceIdem D v ε ∧
    ((e * cA D e = 0 ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∨ e = algebraMap (AF D.host.F) (AE D) ε)) ∧
  ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)

def plOf (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau) : InfinitePlace D.host.E :=
  InfinitePlace.mk ((θ τ).comp ((infPart D).comp (incA D)))

def IsInfLoc (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau) (k : D.host.E) (x : AE D) : Prop :=
  finPart D x = 1 ∧ (∀ τ', τ' ≠ τ → θ τ' (infPart D x) = 1) ∧ θ τ (infPart D x) = θ τ (infPart D (incA D k))

variable {D}

theorem locE_mul_locE {e : AE D} (he : e * e = e) (k l : D.host.E) : locE D e k * locE D e l = locE D e (k * l) := by
  unfold locE
  rw [map_mul]
  linear_combination ((incA D k - 1) * (incA D l - 1)) * he

theorem isUnit_locE {e : AE D} (he : e * e = e) (k : D.host.Eˣ) : IsUnit (locE D e k) := by
  refine isUnit_iff_exists_inv.mpr ⟨locE D e ((k⁻¹ : D.host.Eˣ) : D.host.E), ?_⟩
  rw [locE_mul_locE he]
  simp [locE]

def locU {e : AE D} (he : e * e = e) (k : D.host.Eˣ) : (AE D)ˣ := (isUnit_locE he k).unit

theorem locU_val {e : AE D} (he : e * e = e) (k : D.host.Eˣ) : ((locU he k : (AE D)ˣ) : AE D) = locE D e k := rfl

end Formalism.L2.JoinChr

end
