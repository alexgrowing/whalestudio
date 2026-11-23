import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem AnArc.FSum_sum_smul {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (j : ℕ) [NeZero j] (α : A.X)
    {K : Type} (s : Finset K) (c : K → ℂ) (th : K → (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum j α (∑ i ∈ s, c i • th i) v = ∑ i ∈ s, HahnSeries.single 0 (c i) * A.FSum j α (th i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := A.FSum_smul j α 0 0 v
    rw [zero_smul, zero_smul] at h
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, A.FSum_add, ih, A.FSum_smul,
      HahnSeries.single_zero_mul_eq_smul]

theorem AnArc.exists_basis_FSum : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), AnFin A → ∀ (j : ℕ) [NeZero j], ∃ (n : ℕ) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ) (T₀ : ℝ), (∀ i, th i ∈ A.Theta j (α i)) ∧ LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum j (α i) (th i) v) ∧ (∀ w : ℂ, T₀ < w.im → LinearIndependent ℂ (fun i v => A.Sum j (α i) (th i) w v)) ∧ ∀ α', ∀ th' ∈ A.Theta j α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧ ∀ v, A.FSum j α' th' v = ∑ i, r i * A.FSum j (α i) (th i) v := by
  intro O _ _ A hA j _
  classical
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul A.X j hj
  obtain ⟨T₀, hT⟩ := A.exists_isConvLine
  have : ∀ c, Module.Finite ℂ (A.Theta j (e c)) := fun c => hA.1 j (e c) hj
  let b := fun c => Module.finBasis ℂ (A.Theta j (e c))
  let I := fun c => Fin (Module.finrank ℂ (A.Theta j (e c)))
  let t : ∀ c, I c → (Fin A.gB → ℂ) → ℂ := fun c i => b c i
  have ht : ∀ c, LinearIndependent ℂ (t c) := fun c =>
    (b c).linearIndependent.map' (A.Theta j (e c)).subtype (Submodule.ker_subtype _)
  have htm : ∀ c i, t c i ∈ A.Theta j (e c) := fun c i => (b c i).2
  have hrep : ∀ c c' y, e c = e c' + j • y → c = c' := fun c c' y h =>
    (he (e c)).unique ⟨0, by simp⟩ ⟨y, h⟩
  let s := (Fintype.equivFin (Σ c, I c)).symm
  refine ⟨_, fun i => e (s i).1, fun i => t (s i).1 (s i).2, T₀, fun i => htm _ _,
    (A.linearIndependent_FSum_sigma hrep ht).comp s s.injective, fun w hw =>
    (A.linearIndependent_Sum_sigma (NeZero.ne j) hrep ht w fun c i z =>
      AnArc.summable_term hT (NeZero.ne j) (htm c i) hw (0, z)).comp s s.injective, fun α' th' hth' => ?_⟩
  obtain ⟨c, ⟨m, hm⟩, -⟩ := he α'
  have hα : α' + j • (-m) = e c := by rw [hm]; simp
  have hmem := A.translate_mem_Theta hth' (-m)
  rw [hα] at hmem
  let x := (b c).repr ⟨_, hmem⟩
  have hx : (fun z => th' (z + A.ct (-m))) = ∑ i, x i • t c i := by
    have := congrArg Subtype.val ((b c).sum_repr ⟨_, hmem⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  let u : ℂ⸨X⸩ := HahnSeries.single (A.exponent j α' (-m)) ((A.psi (-m) : ℂ) ^ j * eTwoPi (A.T (-m) α'))
  obtain ⟨r, hr1, hr0⟩ : ∃ r : ∀ c', I c' → ℂ⸨X⸩, (∀ i, r c i = u * HahnSeries.single 0 (x i)) ∧
      ∀ c', c' ≠ c → ∀ i, r c' i = 0 :=
    ⟨Pi.single (M := fun c' => I c' → ℂ⸨X⸩) c fun i => u * HahnSeries.single 0 (x i),
      fun i => by rw [Pi.single_eq_same], fun c' h i => by rw [Pi.single_eq_of_ne h]; rfl⟩
  refine ⟨fun i => r (s i).1 (s i).2, fun i T => ?_, fun v => ?_⟩
  · beta_reduce
    generalize s i = p
    obtain ⟨c', i'⟩ := p
    by_cases h : c' = c
    · subst h
      rw [hr1]
      exact mul_mem (Conv.single_mem_halfRing _ _ _) (Conv.single_mem_halfRing _ _ _)
    · rw [hr0 c' h]
      exact zero_mem _
  · rw [s.sum_comp (fun p : Σ c, I c => r p.1 p.2 * A.FSum j (e p.1) (t p.1 p.2) v), Fintype.sum_sigma,
      Finset.sum_eq_single c (fun c' _ h => by simp [hr0 c' h]) (by simp),
      A.FSum_eq_translate j α' th' (-m) v, hα, hx, A.FSum_sum_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hr1, _root_.mul_assoc]

end GlobalTheory
