import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory

namespace DiffLin

open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR jetAug dualLift dualLift_zR fstD_comp_dualLift ker_jetAug_pow)

variable {R : Type} [CommRing R] {n : ℕ}

theorem fst_dualLift (t : Fin n → R) (y : JetR R (Fin n) 1) :
    (dualLift t y).fst = jetAug R (Fin n) 1 y :=
  AlgHom.congr_fun (fstD_comp_dualLift t) y

theorem snd_dualLift_sum {k : ℕ} (c : Fin k → R) (t : Fin k → Fin n → R) (y : JetR R (Fin n) 1) :
    (dualLift (∑ i, c i • t i) y).snd = ∑ i, c i * (dualLift (t i) y).snd := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ s : Fin n → R,
        (dualLift s (Ideal.Quotient.mk _ (MvPolynomial.C a))).snd = 0 := fun s => by
      have := (dualLift s).commutes a
      exact (congrArg TrivSqZeroExt.snd this).trans rfl
    simp only [h, mul_zero, Finset.sum_const_zero]
  | add p q hp hq =>
    simp only [map_add, TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have h : ∀ s : Fin n → R,
        (dualLift s (Ideal.Quotient.mk _ (p * MvPolynomial.X j))).snd =
          jetAug R (Fin n) 1 (Ideal.Quotient.mk _ p) * s j := fun s => by
      rw [map_mul, map_mul, dualLift_zR, DualNumber.snd_mul, fst_dualLift]
      simp
    simp only [h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem spMap_dualLift_surjective (t : Fin n → R) :
    Function.Surjective (spMap (dualLift t : JetR R (Fin n) 1 →+* DualNumber R)) := by
  intro p
  have hs : Function.Surjective (jetAug R (Fin n) 1 : JetR R (Fin n) 1 →+* R) := fun a =>
    ⟨algebraMap R _ a, (jetAug R (Fin n) 1).commutes a⟩
  have hp : (p : PrimeSpectrum (JetR R (Fin n) 1)) ∈
      Set.range (PrimeSpectrum.comap (jetAug R (Fin n) 1 : JetR R (Fin n) 1 →+* R)) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    apply (PrimeSpectrum.isPrime p).mem_of_pow_mem (1 + 1)
    have : a ^ (1 + 1) ∈ (RingHom.ker (jetAug R (Fin n) 1)) ^ (1 + 1) := Ideal.pow_mem_pow ha _
    rw [ker_jetAug_pow, Ideal.mem_bot] at this
    rw [this]
    exact Ideal.zero_mem _
  obtain ⟨q, rfl⟩ := hp
  refine ⟨PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun y => ?_)
  change (dualLift t y).fst ∈ q.asIdeal ↔ jetAug R (Fin n) 1 y ∈ q.asIdeal
  rw [fst_dualLift]

theorem top_le_preimage_of_dualLift {X : Scheme.{0}} (x : Sp (JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (t : Fin n → R)
    (h : ⊤ ≤ (spMap (dualLift t : JetR R (Fin n) 1 →+* DualNumber R) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := spMap_dualLift_surjective t p
  exact h (Set.mem_univ q)

open GlobalTheory.TangentOrigin in
theorem evalPt_of_eq {X : Scheme.{0}} (x : Sp (JetR R (Fin n) 1) ⟶ X) (U : X.Opens)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (t : Fin n → R) (v : Sp (DualNumber R) ⟶ X)
    (e : v = spMap (dualLift t : JetR R (Fin n) 1 →+* DualNumber R) ≫ x) (f : Γ(X, U)) :
    ∃ h : ⊤ ≤ v ⁻¹ᵁ U, evalPt v U h f = dualLift t (evalPt x U hx f) := by
  subst e
  exact ⟨fun p _ => hx (Set.mem_univ _), evalPt_spMap_comp _ x U hx _ f⟩

end DiffLin

open GlobalTheory.TangentOrigin DiffLin in

theorem isDiff_sum_smul_of_isLieComb :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g n : ℕ) (u : HolUnif A L g)
    (v : Fin n → (epsR ℂ ⟶ A)) (W : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A),
    (∀ i, IsTangent (v i)) → (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w := by
  intro A _ hA L g n u v W c w hv hd hc U h f
  have : Smooth A.hom := hA.smooth
  obtain ⟨m, x, hx⟩ := Chart.univChartLoc A
  have htan : ∀ i, Chart.IsTan (v i) := fun i => (Chart.isTan_iff _).mpr (hv i)
  obtain ⟨hw, e⟩ := Chart.prodPts_tan hx c v htan
  have ew : w.left = spMap (Chart.dualLift (∑ i, c i • Chart.tcoord hx (v i) (htan i)) :
      Chart.JetR ℂ (Fin m) 1 →+* DualNumber ℂ) ≫ (x 1).left := by
    rw [← e, (Chart.isLieComb_iff c v w).1 hc]
    exact congrArg CommaMorphism.left (Chart.tcoord_spec hx _ hw)
  have ev : ∀ i, (v i).left = spMap (Chart.dualLift (Chart.tcoord hx (v i) (htan i)) :
      Chart.JetR ℂ (Fin m) 1 →+* DualNumber ℂ) ≫ (x 1).left := fun i =>
    congrArg CommaMorphism.left (Chart.tcoord_spec hx _ (htan i))
  have hU : ⊤ ≤ (x 1).left ⁻¹ᵁ U := top_le_preimage_of_dualLift _ U _ (ew ▸ h)
  obtain ⟨h', e'⟩ := evalPt_of_eq (x 1).left U hU _ w.left ew f
  change (evalPt (R := DualNumber ℂ) w.left U h' f).snd = _
  rw [e', snd_dualLift_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨hi, ei⟩ := evalPt_of_eq (x 1).left U hU _ (v i).left (ev i) f
  rw [← ei, map_smul, smul_eq_mul]
  exact congrArg (c i * ·) (hd i U hi f)

end GlobalTheory
