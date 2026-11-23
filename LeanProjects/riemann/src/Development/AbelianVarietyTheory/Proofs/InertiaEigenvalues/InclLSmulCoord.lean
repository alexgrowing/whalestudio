import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.BKGal

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]

theorem inclL_smul_coord (P : PhiMod O K l e a ι) (m : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (fun i => m * c i) = inclO l O m • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply]
  have h : (fun i => inclO l O (m * c i)) = inclO l O m • fun i => inclO l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  rw [h, Matrix.mulVec_smul]

theorem IsCrisVal.sub {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w w' : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w' b') : IsCrisVal t ϖ P jB (w - w') (b - b') := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  obtain ⟨m', c', hu', hc', hb'⟩ := h'
  refine ⟨m * m', fun i => m' * c i - m * c' i, by rw [map_mul]; exact hu.mul hu', ?_, ?_⟩
  · have e1 : (fun i => m' * c i - m * c' i) = (fun i => m' * c i) - (fun i => m * c' i) := rfl
    rw [e1, map_sub, inclL_smul_coord, inclL_smul_coord, ← hc, ← hc', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (inclO l O m')]
  · have e2 : (fun i => toB l O (m' * c i - m * c' i)) =
        toB l O m' • (fun i => toB l O (c i)) - toB l O m • (fun i => toB l O (c' i)) :=
      funext fun i => by simp only [map_sub, map_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e2, map_sub, map_smul, map_smul, ← hb, ← hb', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (toB l O m')]

end GlobalTheory.BKGal
