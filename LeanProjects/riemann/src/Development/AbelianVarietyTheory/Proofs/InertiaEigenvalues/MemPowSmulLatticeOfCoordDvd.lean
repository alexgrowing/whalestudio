import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem mem_pow_smul_of_coord_dvd : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (x : ↥T.L.T) (k : ℕ), (∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ k ∣ φ x) → ∃ y ∈ T.L.T, (x : T.V) = ((l : O) ^ k) • y := by
  intro l _ O K _ _ _ _ _ _ _ _ G _ _ T x k h
  haveI : Module.Free O ↥T.L.T := T.L.free
  let b := Module.Free.chooseBasis O ↥T.L.T
  let f := Module.Free.chooseBasis ℤ_[l] O
  have hφ : ∀ i j, (l : ℤ_[l]) ^ k ∣ f.repr (b.repr x i) j := by
    intro i j
    let φ : ↥T.L.T →+ ℤ_[l] := ((f.coord j).toAddMonoidHom).comp (b.coord i).toAddMonoidHom
    have := h φ (by
      intro z t
      show f.coord j (b.coord i (algebraMap ℤ_[l] O z • t)) = z * f.coord j (b.coord i t)
      rw [LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])
    simpa [φ] using this
  choose w hw using hφ
  let c : _ → O := fun i => ∑ j ∈ (f.repr (b.repr x i)).support, w i j • f j
  let y : ↥T.L.T := ∑ i ∈ (b.repr x).support, c i • b i
  have hc : ∀ i, (l : O) ^ k * c i = b.repr x i := by
    intro i
    have hl : (l : O) ^ k = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ k) := by simp
    conv_rhs => rw [← f.linearCombination_repr (b.repr x i)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hl, ← Algebra.smul_def, smul_smul, hw i j]
  have hx : x = (l : O) ^ k • y := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hc i]
  refine ⟨(y : T.V), y.2, ?_⟩
  rw [hx]
  rfl

end GlobalTheory.InertiaEigenvalues
