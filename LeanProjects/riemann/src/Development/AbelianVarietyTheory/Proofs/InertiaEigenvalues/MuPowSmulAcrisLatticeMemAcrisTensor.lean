import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrisInt

theorem tw_incl_smul {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

theorem tw_incl_comp {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' R'' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [CommRing R''] [Algebra O R'']
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G Qp LL O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a t => simp [TWincl]

theorem mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ ε : OCb l, IsEps ε → ∀ z : ι → OCr l O, ∃ w : TW (OCr l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (fun i => toOB l O (z i)) = TWincl (toOB l O) T w := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hLM hML jB hcmp ε hε z
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hK := (GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hLM hML ε δ hε hδ).2.2.2
  have step1 : ∀ c : ι → OA l O, ∃ y : TW (OA l O) T,
      jB (fun i => toB l O (((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) * c i)) = TWincl (toB l O) T y := by
    intro c
    obtain ⟨y, hy⟩ := hK (inclL t ϖ P c) ⟨c, rfl⟩
    refine ⟨y, hcmp _ y ?_⟩
    rw [← hy]
    congr 1
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [map_mul, Algebra.TensorProduct.tmul_pow]
  choose y hy using fun i : ι => step1 (Pi.single i 1)
  refine ⟨∑ i, z i • TWincl (toOCr l O) T (y i), ?_⟩
  have hsingle : ∀ i, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (Pi.single i 1) =
      TWincl (toB l O) T (y i) := by
    intro i
    rw [← hy i, ← map_smul]
    congr 1
    funext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hz : (fun i => toOB l O (z i)) = ∑ i, toOB l O (z i) • (Pi.single i (1 : OB l O)) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [hz, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm, hsingle, tw_incl_smul, tw_incl_comp]
  rfl

end GlobalTheory.BKGal.CrisInt
