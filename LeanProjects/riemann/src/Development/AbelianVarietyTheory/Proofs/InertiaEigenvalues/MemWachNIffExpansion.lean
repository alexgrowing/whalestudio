import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem mem_N_iff_of_points (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (nb : Module.Basis ι (LetA O n) ↥(W.N T)) (P : ZMod n → LL → Prop) (Φ : ZMod n → LL → Prop)
    (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T)
    (hkey : ∀ i ζ, P i ζ → (Φ i ζ ↔ ∀ j, nb.repr ⟨W.Q ^ k • x, hx⟩ j ∈ van W i ζ k))
    (hQ : ∀ i ζ, P i ζ → ∃ w : PowerSeries LL, W.lev i ζ W.Q = PowerSeries.X * w)
    (hdiv : ∀ a : LetA O n, (∀ i ζ, P i ζ → a ∈ van W i ζ k) → W.Q ^ k ∣ a)
    (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) :
    x ∈ W.N T ↔ ∀ i ζ, P i ζ → Φ i ζ := by
  constructor
  · intro hxN i ζ hζ
    rw [hkey i ζ hζ]
    intro j
    have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • (⟨x, hxN⟩ : ↥(W.N T)) := rfl
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    obtain ⟨w, hw⟩ := hQ i ζ hζ
    refine Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ?_)
    rw [map_mul, map_pow, hw]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_mul_right _ _) k) _
  · intro H
    have hd : ∀ j, W.Q ^ k ∣ nb.repr ⟨W.Q ^ k • x, hx⟩ j := fun j =>
      hdiv _ (fun i ζ hζ => (hkey i ζ hζ).1 (H i ζ hζ) j)
    choose b hb using hd
    let z : ↥(W.N T) := ∑ j, b j • nb j
    have hz : W.Q ^ k • ((z : ↥(W.N T)) : W.DD T) = W.Q ^ k • x := by
      have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • z := by
        conv_lhs => rw [← nb.sum_repr ⟨W.Q ^ k • x, hx⟩]
        simp only [z, Finset.smul_sum, hb, mul_smul]
      exact (congrArg Subtype.val e).symm
    have hu : IsUnit (algebraMap (LetA O n) W.EE (W.Q ^ k)) := by
      rw [map_pow]
      exact hunit.pow k
    obtain ⟨u, hu'⟩ := hu
    have h1 : ∀ y : W.DD T, W.Q ^ k • y = (u : W.EE) • y := fun y => by
      rw [hu', algebraMap_smul]
    rw [h1, h1] at hz
    have hx' : x = (z : W.DD T) := by
      have := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) hz
      simp only [smul_smul, Units.inv_mul, one_smul] at this
      exact this.symm
    rw [hx']
    exact z.2

end Generic

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem mem_N_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  intro D HW F Cm l _ K s LL h W C T hT k x hx
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  refine mem_N_iff_of_points W T nb (fun i ζ => IsPrimitiveRoot ζ (l ^ s)) _ k x hx ?_ ?_ ?_ ?_
  · intro i ζ hζ
    exact ((GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hζ⟩
      (GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ)).2 _ nb).2.2 _ k
  · intro i ζ hζ
    obtain ⟨⟨w, _, hw⟩, -⟩ := (GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hζ⟩).2.2.2.1 hζ
    exact ⟨w, hw⟩
  · exact (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).1 k
  · have h0 := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    simpa using h0

end GlobalTheory.NL.WachModulePoleQuotient
