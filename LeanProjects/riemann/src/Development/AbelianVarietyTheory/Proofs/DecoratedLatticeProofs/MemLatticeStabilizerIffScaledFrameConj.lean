import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.StabFin

section General

variable {A R n : Type} [CommRing A] [CommRing R] [Algebra R A] [Fintype n] [DecidableEq n]

theorem mem_stab_conj {L S : Submodule R (n → A)} {b : GL n A} (h : ∀ y, y ∈ S ↔ b.1 *ᵥ y ∈ L) (x : GL n A) :
    x ∈ Formalism.UG.stabGL L ↔ b⁻¹ * x * b ∈ Formalism.UG.stabGL S := by
  have key : ∀ y, (b⁻¹ * x * b).1 *ᵥ y ∈ S ↔ x.1 *ᵥ (b.1 *ᵥ y) ∈ L := fun y => by
    rw [h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel, one_mul]
  constructor
  · intro hx y
    rw [key, h]
    exact hx _
  · intro hx y
    have h1 := hx ((b⁻¹).1 *ᵥ y)
    rw [key, h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
    exact h1

omit [CommRing R] [Algebra R A] in

theorem conj_eq_of_smul {m m' : GL n A} {w : A} (h : m.1 = w • m'.1) (z : GL n A) :
    m⁻¹ * z * m = m'⁻¹ * z * m' := by
  have hc : m * m'⁻¹ * z = z * (m * m'⁻¹) := by
    apply Units.ext
    have e : (m * m'⁻¹).1 = w • (1 : Matrix n n A) := by
      rw [Units.val_mul, h, Matrix.smul_mul, Units.mul_inv]
    rw [Units.val_mul _ z, Units.val_mul z, e, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  calc m⁻¹ * z * m = m⁻¹ * (z * (m * m'⁻¹)) * m' := by group
    _ = m⁻¹ * (m * m'⁻¹ * z) * m' := by rw [hc]
    _ = m'⁻¹ * z * m' := by group

end General

theorem mem_stab_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {m : GL (Fin N) (Fv F v ⊗[F] E)} (h : ∀ i j, m.1 i j ∈ intLoc F E v)
    (h' : ∀ i j, (m⁻¹).1 i j ∈ intLoc F E v) : m ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  have key : ∀ (M : Matrix (Fin N) (Fin N) (Fv F v ⊗[F] E)), (∀ i j, M i j ∈ intLoc F E v) →
      ∀ y, y ∈ latLoc F (stdLattice E N) v → M *ᵥ y ∈ latLoc F (stdLattice E N) v := fun M hM y hy =>
    mem_latLoc_stdLattice.2 fun i => show ∑ j, M i j * y j ∈ _ from
      sum_mem fun j _ => mul_mem (hM i j) (mem_latLoc_stdLattice.1 hy j)
  intro y
  refine ⟨key _ h y, fun hy => ?_⟩
  have h1 := key _ h' _ hy
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1

theorem mem_stab_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)) (b M M' : GL (Fin N) (AF F ⊗[F] E)) (u : (AF F ⊗[F] E)ˣ), IsLatticeFrame Λ b → (∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v) → M.1 = (u : AF F ⊗[F] E) • M'.1 → ∀ (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (Fv F v ⊗[F] E)), x ∈ Formalism.UG.stabGL (latLoc F Λ v) ↔ (Formalism.UG.bc (compFin F E v) (b * M))⁻¹ * x * Formalism.UG.bc (compFin F E v) (b * M) ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  intro F E _ _ _ _ _ N Λ b M M' u hb hM' hM v x
  have hs : Formalism.UG.bc (compFin F E v) M' ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
    refine mem_stab_std (fun i j => (hM' v i j).1) (fun i j => ?_)
    rw [← map_inv]
    exact (hM' v i j).2
  have he : (Formalism.UG.bc (compFin F E v) M).1 =
      compFin F E v (u : AF F ⊗[F] E) • (Formalism.UG.bc (compFin F E v) M').1 := by
    ext i j
    change compFin F E v (M.1 i j) = compFin F E v (u : AF F ⊗[F] E) * compFin F E v (M'.1 i j)
    rw [hM, ← map_mul]
    rfl
  rw [mem_stab_conj (S := latLoc F (stdLattice E N) v) (b := Formalism.UG.bc (compFin F E v) b)
    (fun y => mem_latLoc_stdLattice.trans (hb v y)) x, map_mul, mul_inv_rev]
  set β := Formalism.UG.bc (compFin F E v) b
  have e : (Formalism.UG.bc (compFin F E v) M)⁻¹ * β⁻¹ * x * (β * Formalism.UG.bc (compFin F E v) M) =
      (Formalism.UG.bc (compFin F E v) M)⁻¹ * (β⁻¹ * x * β) * Formalism.UG.bc (compFin F E v) M := by group
  rw [e, conj_eq_of_smul he, Subgroup.mul_mem_cancel_right _ hs, Subgroup.mul_mem_cancel_left _ (inv_mem hs)]

end GlobalTheory.StdUnn.StabFin

end
