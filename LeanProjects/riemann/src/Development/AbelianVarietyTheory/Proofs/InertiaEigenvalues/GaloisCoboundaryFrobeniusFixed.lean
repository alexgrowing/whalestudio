import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyMemRangeOfInvariantVectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceOfFinitePadicIntUnitBallStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSubSubMemXiOfMonodromyEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiMemInvertedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiMemInvertedPrimeLatticeOfMemEisensteinInvariaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorBcrisValueFrobeniusOfInverseEisensteinTwisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.PhiFix

theorem frob_actB {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K]
    [Algebra O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (x : TW (OB l O) T) :
    TWmap (frobOB l O) T (actB (sQ l) T g x) = actB (sQ l) T g (TWmap (frobOB l O) T x) := by
  have hB : ∀ r : OB l O, frobOB l O (galOB O (sQ l g) r) = galOB O (sQ l g) (frobOB l O r) := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul o β =>
      simp only [frobOB, galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact congrArg (fun y : Per.Bcris l => o ⊗ₜ[ℤ_[l]] y) ((GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.1 _ β)
    | add r s hr hs => rw [map_add (galOB O (sQ l g)), map_add (frobOB l O), map_add (frobOB l O), map_add (galOB O (sQ l g)), hr, hs]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [actB, TWmap, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, hB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem frob_fixed_coboundary : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → TWmap (frobOB l O) T (actB (sQ l) T g b - b) = actB (sQ l) T g b - b := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY b hb g hg
  obtain ⟨hy, m₀, σ, b₀, hm₀, -, hconn, hb₀, rfl⟩ := hb
  haveI : CompleteSpace K := GlobalTheory.T.completeSpace_of_finite_padicInt_unitBall l O K
  obtain ⟨d, hd⟩ := GlobalTheory.T.phi_sub_sub_mem_xi_of_monodromy_eq O K l e a ι η H D y hyY σ.1 hconn
  obtain ⟨-, hall⟩ := GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I
  obtain ⟨hφ, huniq, hfrobv, -, -⟩ := hall R.jB R.cmp
  have hσφ : D.phi σ.1 ∈ D.MMl := GlobalTheory.T.phi_mem_invertedLattice O K l e a ι η H D σ.1 σ.2
  have hyφ : D.phi y ∈ D.MMl := GlobalTheory.T.phi_mem_invertedPrime_lattice_of_mem_eisensteinInvariants O K l e a ι η H D y hyY

  have hv1 := IsCrisVal.sub t ϖ (hfrobv _ _ hb₀) hb₀
  have hv2 := GlobalTheory.T.tensorBcris_value_frobenius_of_inverse_eisenstein_twist l a e O K t ϖ ι η H D T R.jB y hyY hy hyφ
  have hw : phiW t ϖ D.toPhiMod (phiW t ϖ D.toPhiMod m₀) - phiW t ϖ D.toPhiMod m₀ =
      phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩) := by rw [← hm₀, map_sub]
  rw [hw] at hv1
  have hb0 := huniq _ _ _ hv1 hv2
  have hs := hφ σ ⟨D.phi σ.1, hσφ⟩ rfl
  have hmem : D.xi d ∈ D.MMl := by
    rw [← hd]; exact sub_mem (sub_mem hσφ σ.2) hyφ
  have hkey : TWmap (frobOB l O) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₀) -
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₀) = R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi d, hmem⟩) := by
    have he : (⟨D.xi d, hmem⟩ : D.MMl) = ⟨D.phi σ.1, hσφ⟩ - σ - ⟨D.phi y, hyφ⟩ := Subtype.ext (by
      simp only [Submodule.coe_sub]; exact hd.symm)
    rw [he, map_sub, map_sub, map_sub, map_sub, map_sub, ← hs, ← hb0]
    abel
  have hfix := R.horiz g hg d hmem
  rw [← hkey, map_sub] at hfix
  rw [map_sub, frob_actB]
  exact sub_eq_sub_iff_sub_eq_sub.1 hfix

end GlobalTheory.BKGal.PhiFix
