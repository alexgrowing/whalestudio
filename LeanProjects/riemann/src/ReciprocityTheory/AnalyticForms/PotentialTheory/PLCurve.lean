import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveB

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

def PLCurveLocalStatement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas 1 X)
    (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (p : Fin r → X),
    Function.Injective p → IsPotential A L → IsSection A L s → IsSNC A L s m (fun k => {p k}) →
    ∀ (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ)), IsCompatChart A ψ →
    ∀ v : X → ℝ, A.Smooth v → tsupport v ⊆ ψ.source →
      mInt A ![LocPot.ofFun v] (logNormSec L s) = ∑ k, (m k : ℝ) * v (p k) - mInt A ![L] v

namespace PLC

variable {X : Type} [TopologicalSpace X]

theorem plDefect_add [CompactSpace X] [T2Space X] (A : FinHolAtlas 1 X) (L : LocPot X)
    (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (p : Fin r → X)
    (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m (fun k => {p k}))
    {f f' : X → ℝ} (hf : A.Smooth f) (hf' : A.Smooth f') :
    plDefect A L s m p (fun z => f z + f' z) = plDefect A L s m p f + plDefect A L s m p f' := by
  have hPf := isPotential_ofFun A f hf
  have hPf' := isPotential_ofFun A f' hf'
  have hI : ∀ {h : X → ℝ}, IsPotential A (LocPot.ofFun h) →
      MIntegrable A (Fin.cons (LocPot.ofFun h) ![]) (logNormSec L s) := fun hP =>
    logNormIntegrable A L s m _ hL hs hsnc _ (Fin.forall_fin_one.2 hP)
  have h1 : mInt A ![LocPot.ofFun (fun z => f z + f' z)] (logNormSec L s) =
      mInt A ![LocPot.ofFun f] (logNormSec L s) + mInt A ![LocPot.ofFun f'] (logNormSec L s) := by
    exact (mInt_congr_phi A _ (Fin.cons (LocPot.ofFun f + LocPot.ofFun f') ![])
      (fun i a b => by fin_cases i; rfl) _).trans
      (mIntAdd (e := 0) A _ _ ![] hPf hPf' (fun i => i.elim0) _ (hI hPf) (hI hPf'))
  have hLp : ∀ i, IsPotential A (![L] i) := Fin.forall_fin_one.2 hL
  have h2 : mInt A ![L] (fun z => f z + f' z) = mInt A ![L] f + mInt A ![L] f' := by
    have := mIntLinear A ![L] hLp 1 f f' (mIntegrableCont A _ hLp f (continuous_of_smooth A hf))
      (mIntegrableCont A _ hLp f' (continuous_of_smooth A hf'))
    simpa using this
  unfold plDefect
  rw [h1, h2]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem plDefect_zero (A : FinHolAtlas 1 X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ}
    (m : Fin r → ℕ) (p : Fin r → X) : plDefect A L s m p (fun _ => 0) = 0 := by
  unfold plDefect
  have h0 : mInt A ![LocPot.ofFun fun _ => (0 : ℝ)] (logNormSec L s) = 0 :=
    mIntConstPot (e := 0) A 0 ![] _
  rw [h0, mInt_zero]
  simp

theorem plc_global [CompactSpace X] [T2Space X] (A : FinHolAtlas 1 X) (L : LocPot X)
    (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (p : Fin r → X)
    (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m (fun k => {p k}))
    (v : X → ℝ) (hv : A.Smooth v) :
    mInt A ![LocPot.ofFun v] (logNormSec L s) = ∑ k, (m k : ℝ) * v (p k) - mInt A ![L] v := by
  classical
  choose ψ hψ hxψ hloc using fun x => plc_local A L s m p hL hs hsnc x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (ψ x).source)
    (fun x => (ψ x).open_source) (fun x _ => Set.mem_iUnion.2 ⟨x, hxψ x⟩)
  let F : Fin t.card → OpenPartialHomeomorph X (Fin 1 → ℂ) := fun i => ψ (t.equivFin.symm i)
  obtain ⟨B, hAB, -, hB⟩ := atlasOfCompat A F (fun i => hψ _) (by
    intro x
    obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨y, hy⟩, by simpa [F] using hx⟩)
  obtain ⟨P⟩ := existsPartition B
  have hχ : ∀ j, A.Smooth (P.χ j) := fun j =>
    smoothOn_of_compatible hAB.symm' isOpen_univ (P.smooth j)
  have hpiece : ∀ j, plDefect A L s m p (fun z => P.χ j z * v z) = 0 := by
    intro j
    obtain ⟨i, hi⟩ := hB j
    have hsub : tsupport (P.χ j) ⊆ (ψ (t.equivFin.symm i)).source := by
      have := P.tsupport_subset j
      rwa [hi] at this
    have := hloc (t.equivFin.symm i) (fun z => P.χ j z * v z) (smooth_mul A (hχ j) hv)
      (tsupport_mul_subset_left.trans hsub)
    unfold plDefect
    rw [this]
    ring
  have hind : ∀ S : Finset (Fin B.n),
      plDefect A L s m p (fun z => ∑ j ∈ S, P.χ j z * v z) = 0 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simpa using plDefect_zero A L s m p
    · intro a S ha ih
      have hfun : (fun z => ∑ j ∈ insert a S, P.χ j z * v z) =
          fun z => P.χ a z * v z + ∑ j ∈ S, P.χ j z * v z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hfun, plDefect_add A L s m p hL hs hsnc (smooth_mul A (hχ a) hv)
        (smooth_sum A S fun j => smooth_mul A (hχ j) hv), hpiece a, ih, add_zero]
  have hv' : (fun z => ∑ j, P.χ j z * v z) = v := by
    funext z
    rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
  have h := hind Finset.univ
  rw [hv'] at h
  unfold plDefect at h
  linarith

end PLC

theorem plCurve : PoincareLelongCurveStatement := by
  intro X _ _ _ A L s r m p _ hL hs hsnc v hv
  exact PLC.plc_global A L s m p hL hs hsnc v hv

end

end ReciprocityTheory.AnForm.M
