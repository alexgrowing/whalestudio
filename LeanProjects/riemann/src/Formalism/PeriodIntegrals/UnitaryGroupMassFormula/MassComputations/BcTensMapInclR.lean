import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.UnfAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsHermNDOfSetting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal Pointwise Matrix

namespace MassDataMassesW

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem haMap_stabT {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') {a : ℕ} (X0 : Fin a → Fin n → E) (g : HA R σ J) (hg : g ∈ stabT R σ J X0) :
    haMap σ J φ g ∈ stabT R' σ J X0 := by
  rw [mem_stabT] at hg ⊢
  intro b
  have h := hg b
  have e1 : ratV (F := F) R' (X0 b) = (tensMap (E := E) φ) ∘ ratV (F := F) R (X0 b) := by
    funext i
    simp [ratV, tensMap_inclR]
  rw [e1]
  show (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (tensMap (E := E) φ)) *ᵥ
    ((tensMap (E := E) φ) ∘ ratV (F := F) R (X0 b)) = _
  funext i
  rw [← RingHom.map_mulVec]
  simp only [Function.comp_apply]
  congr 1
  exact congrFun h i

theorem continuous_haMap [FiniteDimensional F E] {R S : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing S] [Algebra F S] [TopologicalSpace S] [IsTopologicalRing S]
    (φ : R →ₐ[F] S) (hφ : Continuous φ) : Continuous (haMap σ J φ) := by
  have ht : Continuous (tensMap (E := E) φ) :=
    PI.VolStabSW.PositiveNearLattice.continuous_map_tens (Module.finBasis F E) φ hφ
  have hv : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Units.continuous_val.comp (continuous_subtype_val : Continuous fun g : HR R σ J => (g : GL (Fin n) (R ⊗[F] E)))
  have hi : Continuous fun g : HA R σ J =>
      (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Units.continuous_coe_inv.comp (continuous_subtype_val : Continuous fun g : HR R σ J => (g : GL (Fin n) (R ⊗[F] E)))
  have key : Continuous fun g : HA R σ J => Formalism.UG.bc (tensMap (E := E) φ) (HA.mat R σ J g) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun g : HA R σ J =>
        ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (tensMap (E := E) φ)
      exact continuous_pi fun i => continuous_pi fun j =>
        ht.comp ((continuous_apply j).comp ((continuous_apply i).comp hv))
    · show Continuous fun g : HA R σ J =>
        (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (tensMap (E := E) φ)
      exact continuous_pi fun i => continuous_pi fun j =>
        ht.comp ((continuous_apply j).comp ((continuous_apply i).comp hi))
  exact key.subtype_mk _

theorem inclR_comp_sig (R : Type) [CommRing R] [Algebra F R] :
    (inclR (F := F) R).comp (σ : E →+* E) = (sigR R σ).comp (inclR R) := by
  ext e
  simp [inclR, sigR]

def ratPt (R : Type) [CommRing R] [Algebra F R] (γ0 : GL (Fin n) E) (h : γ0 ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    HA R σ J :=
  ⟨Formalism.UG.bc (inclR R) γ0, Formalism.UG.P.bc_mem (σ : E →+* E) (sigR R σ) (inclR R) (inclR_comp_sig σ R) J γ0 h⟩

end Gen

end MassDataMassesW
