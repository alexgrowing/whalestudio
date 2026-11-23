import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjectiveVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP MvPolynomial
open scoped ComplexConjugate ENNReal ContDiff

noncomputable section

variable {N : ℕ}

namespace ProjFS

end ProjFS

open ProjFS

open Classical in

def polySection (P : MvPolynomial (Fin (N + 1)) ℂ) : Fin (N + 1) → CP N → ℂ :=
  fun j x => if x ∈ chartDomain j then eval (chartVec j (chartCoord j x)) P else 0

def polySectionLin : MvPolynomial (Fin (N + 1)) ℂ →ₗ[ℂ] (Fin (N + 1) → CP N → ℂ) where
  toFun := polySection
  map_add' P Q := by
    funext j x; simp only [polySection, Pi.add_apply]; split_ifs <;> simp
  map_smul' c P := by
    funext j x; simp only [polySection, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

instance (n : ℕ) : FiniteDimensional ℂ (homogeneousSubmodule (Fin (N + 1)) ℂ n) :=
  Module.Finite.iff_fg.2 (homogeneousSubmodule_fg (Fin (N + 1)) ℂ n)

def polySections (N n : ℕ) : Submodule ℂ (Fin (N + 1) → CP N → ℂ) :=
  LinearMap.range ((polySectionLin (N := N)).domRestrict (homogeneousSubmodule (Fin (N + 1)) ℂ n))

instance (n : ℕ) : FiniteDimensional ℂ (polySections N n) := by
  unfold polySections; infer_instance

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
