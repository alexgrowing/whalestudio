import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChartStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.OmegaCoord

variable {k : Type} [CommRing k] {d : ℕ}

theorem coeff_eq_zero_of_mem_sq {g : MvPowerSeries (Fin d) k}
    (hg : g ∈ RingHom.ker (constantCoeff (R := k) (σ := Fin d)) ^ 2) (α : Fin d →₀ ℕ)
    (hα : α.degree < 2) : coeff α g = 0 := by
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hdeg : q.1.degree + q.2.degree < 2 := by rw [← map_add, hq]; exact hα
    rw [RingHom.mem_ker] at ha hb
    rcases Nat.lt_or_ge q.1.degree 1 with h | h
    · have : q.1 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, ha, zero_mul]
    · have : q.2 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, hb, mul_zero]
  · rw [map_add, ha, hb, add_zero]

variable {A : Type} [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i))
  (haug : ∀ i, Coalgebra.counit (R := k) (x i) = 0)

include haug in

theorem exists_eq_sum (hsurj : Function.Surjective (evA k x hx)) (u : Cot k A) :
    ∃ w : Fin d → k, u = ∑ i, w i • dUnit k (x i) := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ u
  obtain ⟨f, rfl⟩ := hsurj a
  exact ⟨lin f, (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug f).2⟩

include haug in

theorem eq_zero_of_sum (hsurj : Function.Surjective (evA k x hx))
    (hker : ∀ f, evA k x hx f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < 2 → coeff α f = 0)
    (w : Fin d → k) (hw : ∑ i, w i • dUnit k (x i) = 0) : w = 0 := by
  set f : MvPowerSeries (Fin d) k := ∑ i, w i • X i with hf
  have hlin : lin f = w := by
    funext i
    simp [f, lin, coeff_X, Finsupp.single_eq_single_iff]
  have hcc : constantCoeff f = 0 := by simp [f]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug f
  have hd : dUnit k (evA k x hx f) = 0 := by rw [h2, hlin, hw]
  have hε : ∀ g, Bialgebra.counitAlgHom k A (evA k x hx g) = constantCoeff g := fun g =>
    (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug g).1
  rw [dUnit, AugCot.d_eq_zero_iff, hε, hcc, map_zero, sub_zero] at hd
  have hK : RingHom.ker (Bialgebra.counitAlgHom k A) =
      Ideal.map (evA k x hx) (RingHom.ker (constantCoeff (R := k) (σ := Fin d))) := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective _ hsurj]
    constructor
    · intro ha
      obtain ⟨g, rfl⟩ := hsurj a
      refine ⟨g, ?_, rfl⟩
      rw [RingHom.mem_ker] at ha ⊢
      rw [← hε]; exact ha
    · rintro ⟨g, hg, rfl⟩
      rw [RingHom.mem_ker] at hg ⊢
      rw [hε]; exact hg
  rw [hK, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hsurj] at hd
  obtain ⟨g, hg, hgf⟩ := hd
  have hfg : evA k x hx (f - g) = 0 := by rw [map_sub, hgf, sub_self]
  funext i
  have hdeg : (Finsupp.single i 1 : Fin d →₀ ℕ).degree < 2 := by simp
  have e1 := hker _ hfg (Finsupp.single i 1) hdeg
  rw [map_sub, coeff_eq_zero_of_mem_sq hg _ hdeg, sub_zero] at e1
  rw [← hlin]; exact e1

end GlobalTheory.OmegaCoord

namespace GlobalTheory.OmegaCoord

theorem omega_coord : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), (∀ w : Fin d → k, (fun n => ∑ i, w i • dUnit k (c.x n i)) ∈ G.omegaSub) ∧
      ∀ u : G.omega, ∃! w : Fin d → k, ∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i) := by
  intro p k _ d G c
  have hres : ∀ n (w : Fin d → k), cotMap (G.res n) (∑ i, w i • dUnit k (c.x (n + 1) i)) =
      ∑ i, w i • dUnit k (c.x n i) := by
    intro n w
    simp only [map_sum, map_smul, cotMap_d, c.res]
  refine ⟨fun w n => hres n w, fun u => ?_⟩
  have hu : ∀ n, cotMap (G.res n) (u.1 (n + 1)) = u.1 n := u.2
  obtain ⟨n0, hn0⟩ := c.presents.2 2
  have hone := (GlobalTheory.T.functions_eq_series_in_chart p k d G c).1
  have hker : ∀ j f, c.ev (n0 + j) f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < 2 → coeff α f = 0 := by
    intro j
    induction j with
    | zero => exact hn0
    | succ j ih =>
      intro f hf
      refine ih f ?_
      rw [← hone (n0 + j) f]
      exact (congrArg (G.res (n0 + j)) hf).trans (map_zero _)
  have hind : ∀ j (v w : Fin d → k), ∑ i, v i • dUnit k (c.x (n0 + j) i) =
      ∑ i, w i • dUnit k (c.x (n0 + j) i) → v = w := by
    intro j v w h
    have := eq_zero_of_sum (c.x (n0 + j)) (c.nil _) (c.aug _) (c.presents.1 _) (hker j) (v - w)
      (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
    exact sub_eq_zero.1 this
  have hspan : ∀ n, ∃ w : Fin d → k, u.1 n = ∑ i, w i • dUnit k (c.x n i) := fun n =>
    exists_eq_sum (c.x n) (c.nil n) (c.aug n) (c.presents.1 n) (u.1 n)
  obtain ⟨w, hw⟩ := hspan n0
  have hup : ∀ j, u.1 (n0 + j) = ∑ i, w i • dUnit k (c.x (n0 + j) i) := by
    intro j
    induction j with
    | zero => exact hw
    | succ j ih =>
      obtain ⟨v, hv⟩ := hspan (n0 + j + 1)
      have h1 : ∑ i, v i • dUnit k (c.x (n0 + j) i) = ∑ i, w i • dUnit k (c.x (n0 + j) i) := by
        rw [← hres, ← hv, hu, ih]
      rw [← hind j v w h1]
      exact hv
  have hdown : ∀ n j, u.1 (n + j) = ∑ i, w i • dUnit k (c.x (n + j) i) →
      u.1 n = ∑ i, w i • dUnit k (c.x n i) := by
    intro n j
    induction j with
    | zero => exact id
    | succ j ih =>
      intro h
      refine ih ?_
      rw [← hu, ← hres]
      exact congrArg (cotMap (G.res (n + j))) h
  refine ⟨w, fun n => hdown n n0 (by rw [Nat.add_comm]; exact hup n), fun w' hw' => ?_⟩
  exact hind 0 w' w ((hw' n0).symm.trans (hup 0))

end GlobalTheory.OmegaCoord
