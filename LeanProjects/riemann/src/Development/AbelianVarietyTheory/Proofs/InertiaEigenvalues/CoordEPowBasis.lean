import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal.BasisCoord

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem tWincl_smul' {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

end GlobalTheory.BKGal.HatVal.BasisCoord

open GlobalTheory.BKGal.HatVal.BasisCoord in

theorem GlobalTheory.BKGal.HatVal.coord_E_pow_basis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (ε δ : OCb l), IsEps ε → δ ^ l = ε → ∀ j : ι, ∃ c : ι → OA l O, inclL t ϖ D.toPhiMod c = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) ∧ ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η)) • R.jB (fun i => toB l O (c i)) = TWincl (toB l O) T (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H • z) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R ε δ hε hδ j

  let ej : Vec K a ι := fun _ => Pi.single j 1
  have hej : ej ∈ D.toPhiMod.M := mem_tot.2 fun τ i => by
    by_cases h : i = j
    · subst h; simp only [ej, Pi.single_eq_same]; exact one_mem _
    · simp only [ej, Pi.single_eq_of_ne h]; exact zero_mem _
  have hL : E K l e ^ H • ej ∈ D.toPhiMod.L := D.lower _ hej
  obtain ⟨c, hc⟩ := toW_mem_LA t ϖ D.toPhiMod hL

  have hw : toW t ϖ D.toPhiMod ⟨ej, mem_ME_of_mem_M hej⟩ = (Pi.single j 1 : ι → OW l O) := by
    ext1 i
    rw [toW_apply]
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      convert map_one (ϖ.iW t K) using 1
      exact congrArg _ (funext fun τ => Subtype.ext (by simp [ej]))
    · rw [Pi.single_eq_of_ne h]
      convert map_zero (ϖ.iW t K) using 1
      exact congrArg _ (funext fun τ => Subtype.ext (by simp [ej, Pi.single_eq_of_ne h]))

  have hE : ϖ.iW t K (fun _ => ⟨E K l e ^ H, le_away _ _ (pow_mem (E_mem l e _) H)⟩) =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) := by
    have h1 := ϖ.iW_of_mem t K (fun _ => EIn l e (A O K) ^ H)
    have h2 : ϖ.iTot t K (fun _ => EIn l e (A O K) ^ H) = ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H := by
      rw [show (fun _ : ZMod a => EIn l e (A O K) ^ H) = (fun _ => EIn l e (A O K)) ^ H from rfl, map_pow,
        PiSys.iTot_E t K ϖ]
    rw [h2] at h1
    rw [← h1]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [EIn]))
  have hwE : toW t ϖ D.toPhiMod ⟨E K l e ^ H • ej, mem_ME_of_mem_L hL⟩ =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) := by
    rw [toW_smul t ϖ D.toPhiMod (fun _ => ⟨E K l e ^ H, le_away _ _ (pow_mem (E_mem l e _) H)⟩)
      ⟨ej, mem_ME_of_mem_M hej⟩ _ (fun τ => rfl), hE, hw]
  have h1 : inclL t ϖ D.toPhiMod c =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) :=
    hc.trans hwE
  refine ⟨c, h1, ?_⟩

  obtain ⟨-, hK2, -, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ
  have hv : (Pi.single j 1 : ι → OW l O) ∈ MA D.toPhiMod :=
    ⟨Pi.single j 1, funext fun i => by
      by_cases h : i = j
      · subst h; simp [inclV]
      · simp [inclV, Pi.single_eq_of_ne h]⟩
  obtain ⟨z, hz⟩ := hK2 _ hv
  refine ⟨z, ?_⟩
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η) with hm
  set Eh : OA l O := ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H with hEh
  have hB := R.cmp (fun i => m * c i) (Eh • z) (by
    rw [inclL_smul_coord, h1, smul_comm, map_smul, hz, tWincl_smul'])
  have e1 : (fun i => toB l O (m * c i)) = toB l O m • fun i => toB l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  rw [e1, map_smul] at hB
  exact hB
