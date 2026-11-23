import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasAlgebraicChartsOfIsStandardSmooth

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
open scoped Topology

namespace GlobalTheory.LatJet.An.HolLiftProof

theorem ker_nil (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n) : IsNilpotent (RingHom.ker J.π) := by
  classical
  haveI : Finite (Idx I n) := by
    refine Finite.of_injective (fun ν : Idx I n ↦ fun i ↦ (⟨ν.1 i, Nat.lt_succ_of_le (le_trans
      (Finset.single_le_sum (fun l _ ↦ Nat.zero_le (ν.1 l)) (Finset.mem_univ i)) ν.2)⟩ : Fin (n + 2))) ?_
    intro a b h
    exact Subtype.ext (funext fun i ↦ by simpa using congrFun h i)
  haveI : Module.Finite ℂ J.B := Module.Finite.of_basis J.b
  haveI : IsNoetherian ℂ J.B := IsNoetherian.iff_fg.2 inferInstance
  haveI : IsNoetherianRing J.B := isNoetherian_of_tower ℂ inferInstance
  rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian (RingHom.ker J.π))]
  intro x hx
  obtain ⟨N, hN⟩ := J.nil
  refine mem_nilradical.2 ⟨N, ?_⟩
  have := hN (List.replicate N (1, x)) (fun p hp ↦ by rw [List.eq_of_mem_replicate hp]; exact hx) (by simp)
  simpa [List.map_replicate, J.κ.dpow_one hx] using this

theorem adjoin_top (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n) :
    Algebra.adjoin ℂ (Set.range J.t) = ⊤ := by
  classical
  set A := Algebra.adjoin ℂ (Set.range J.t)
  have key : ∀ k, ∀ ν : Idx I n, ∑ i, ν.1 i = k → J.b ν ∈ A := by
    intro k
    induction k with
    | zero =>
      intro ν hν
      have : ν = ⟨0, by simp⟩ :=
        Subtype.ext (funext fun i ↦ (Finset.sum_eq_zero_iff.1 hν) i (Finset.mem_univ i))
      rw [this, J.one]; exact A.one_mem
    | succ k ih =>
      intro ν hν
      obtain ⟨i, hi⟩ : ∃ i, ν.1 i ≠ 0 := by
        by_contra h; push_neg at h; simp [h] at hν
      let ν' : Idx I n := ⟨ν.1 - Pi.single i 1,
        le_trans (Finset.sum_le_sum fun l _ ↦ Nat.sub_le (ν.1 l) _) ν.2⟩
      have hsum : ν.1 = Pi.single i 1 + ν'.1 := by
        funext l
        by_cases hl : l = i
        · subst hl; simp [ν']; omega
        · simp [ν', hl]
      have hν' : ∑ l, ν'.1 l = k := by
        have : ∑ l, ν.1 l = ∑ l, (Pi.single i 1 : I → ℕ) l + ∑ l, ν'.1 l := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun l _ ↦ congrFun hsum l
        simp at this; omega
      have hmul := J.mul ⟨Pi.single i 1, by simp⟩ ν'
      have hle : ∑ l, ((Pi.single i 1 : I → ℕ) + ν'.1) l ≤ n + 1 := by rw [← hsum]; exact ν.2
      rw [dif_pos hle] at hmul
      have hprod : ∏ l, (((Pi.single i 1 : I → ℕ) l + ν'.1 l).choose ((Pi.single i 1 : I → ℕ) l)) = ν.1 i := by
        rw [Finset.prod_eq_single i]
        · simp [ν']; omega
        · intro l _ hl; simp [hl]
        · simp
      have hb : J.b ⟨(Pi.single i 1 : I → ℕ) + ν'.1, hle⟩ = J.b ν := congrArg J.b (Subtype.ext hsum.symm)
      simp only [Pi.add_apply] at hmul
      rw [hprod, hb] at hmul
      have hne : (ν.1 i : ℂ) ≠ 0 := by exact_mod_cast hi
      have : J.b ν = (ν.1 i : ℂ)⁻¹ • (J.t i * J.b ν') := by
        rw [JetRing.t, hmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact A.smul_mem (A.mul_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (ih ν' hν')) _
  rw [eq_top_iff]
  intro x _
  have hle : Submodule.span ℂ (Set.range J.b) ≤ Subalgebra.toSubmodule A :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun ν ↦ key _ ν rfl)
  exact hle (J.b.mem_span x)

theorem analyticAt_eval {I : Type} [Fintype I] (Q : MvPolynomial I ℂ) (x : I → ℂ) :
    AnalyticAt ℂ (fun z ↦ MvPolynomial.eval z Q) x := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => exact (hp.add hq).congr (Filter.Eventually.of_forall fun z ↦ by simp)
  | mul_X p i hp =>
    exact (hp.mul ((ContinuousLinearMap.proj i : (I → ℂ) →L[ℂ] ℂ).analyticAt x)).congr
      (Filter.Eventually.of_forall fun z ↦ by simp)

variable {I : Type} [Fintype I] {n : ℕ}

theorem pi_jet (hC : JetCalc) (J : JetRing ℂ I n) (f : (I → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    J.π (jet J f) = f 0 := by
  rw [J.π_eq]
  exact (hC I n J).1 f hf ⟨0, by simp⟩ [] (by simp)

theorem jet_eval (hC : JetCalc) (J : JetRing ℂ I n) (Q : MvPolynomial I ℂ) :
    jet J (fun z ↦ MvPolynomial.eval z Q) = MvPolynomial.aeval J.t Q := by
  obtain ⟨-, h2, -, h4, h5, -⟩ := hC I n J
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, ← h4 a]
    congr 1; funext z; simp
  | add p q hp hq =>
    rw [map_add, ← hp, ← hq, ← (h2 _ _ (analyticAt_eval p 0) (analyticAt_eval q 0)).2]
    congr 1; funext z; simp
  | mul_X p i hp =>
    rw [map_mul, ← hp, MvPolynomial.aeval_X, ← h5 i,
      ← (h2 _ (fun z ↦ z i) (analyticAt_eval p 0)
        ((ContinuousLinearMap.proj i : (I → ℂ) →L[ℂ] ℂ).analyticAt 0)).1]
    congr 1; funext z; simp

def piAlg (hC : JetCalc) (J : JetRing ℂ I n) : J.B →ₐ[ℂ] ℂ :=
  { J.π with
    commutes' := fun a ↦ by
      show J.π (algebraMap ℂ J.B a) = a
      rw [← (hC I n J).2.2.2.1 a]
      exact pi_jet hC J _ analyticAt_const }

end GlobalTheory.LatJet.An.HolLiftProof

namespace GlobalTheory.LatJet.An.HolLiftProof

open GlobalTheory.AffinePoints

variable {I : Type} [Fintype I] {n : ℕ}

theorem isUnit_of_pi_ne_zero (J : JetRing ℂ I n) (x : J.B) (hx : J.π x ≠ 0) : IsUnit x := by
  obtain ⟨N, hN⟩ := ker_nil I n J
  set a := J.π x
  have hr : algebraMap ℂ J.B a⁻¹ * x - 1 ∈ RingHom.ker J.π := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one]
    have : J.π (algebraMap ℂ J.B a⁻¹) = a⁻¹ := by
      rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, J.b.repr_self]
      simp
    rw [this, inv_mul_cancel₀ hx, sub_self]
  have hnil : IsNilpotent (algebraMap ℂ J.B a⁻¹ * x - 1) := by
    refine ⟨N, ?_⟩
    have := Ideal.pow_mem_pow hr N
    rw [hN] at this
    simpa using this
  have hx' : x = algebraMap ℂ J.B a * (1 + (algebraMap ℂ J.B a⁻¹ * x - 1)) := by
    rw [add_sub_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul]
  rw [hx']
  exact ((IsUnit.mk0 a hx).map (algebraMap ℂ J.B)).mul hnil.isUnit_one_add

theorem holLift_std (hC : JetCalc) (B : Type) [CommRing B] [Algebra ℂ B] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d ℂ B] (J : JetRing ℂ I n) (j : B →ₐ[ℂ] J.B) :
    ∃ (U : Set (I → ℂ)) (y : (I → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen U ∧ 0 ∈ U ∧
      (∀ b, DifferentiableOn ℂ (fun z ↦ y z b) U) ∧ ∀ b, j b = jet J fun z ↦ y z b := by
  classical
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d ℂ B
  let p : B →ₐ[ℂ] ℂ := (piAlg hC J).comp j
  obtain ⟨e, hp, he, han⟩ := GlobalTheory.AffinePoints.exists_chart_of_etale g hg p
  have hsurj : ∀ c : J.B, ∃ Q : MvPolynomial I ℂ, MvPolynomial.aeval J.t Q = c := fun c ↦ by
    have : c ∈ Algebra.adjoin ℂ (Set.range J.t) := by rw [adjoin_top]; trivial
    rw [Algebra.adjoin_range_eq_range_aeval] at this
    exact this
  choose Q hQ using fun k : Fin d ↦ hsurj (j (g (MvPolynomial.X k)))
  let w : (I → ℂ) → Fin d → ℂ := fun z k ↦ MvPolynomial.eval z (Q k)
  have hwan : ∀ x, AnalyticAt ℂ w x := fun x ↦ analyticAt_pi_iff.2 fun k ↦ analyticAt_eval (Q k) x
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun x ↦ (hwan x).continuousAt
  have hw0 : w 0 = e p := by
    funext k
    rw [he, GlobalTheory.AffinePoints.coords_apply]
    show MvPolynomial.eval 0 (Q k) = J.π (j (g (MvPolynomial.X k)))
    rw [← hQ k, ← jet_eval hC J, pi_jet hC J _ (analyticAt_eval _ 0)]
  let U : Set (I → ℂ) := w ⁻¹' e.target
  have hU : IsOpen U := e.open_target.preimage hwc
  have h0U : (0 : I → ℂ) ∈ U := by
    show w 0 ∈ e.target
    rw [hw0]; exact e.map_source hp
  let y : (I → ℂ) → (B →ₐ[ℂ] ℂ) := fun z ↦ e.symm (w z)
  have hyan : ∀ b, ∀ z ∈ U, AnalyticAt ℂ (fun z ↦ y z b) z := fun b z hz ↦
    (han b (w z) hz).comp (hwan z)
  obtain ⟨-, hmul, hloc, hconst, -⟩ := hC I n J
  let ψ : B →ₐ[ℂ] J.B :=
    { toFun := fun b ↦ jet J fun z ↦ y z b
      map_one' := by
        show (jet J fun z ↦ y z 1) = 1
        rw [show (fun z ↦ y z 1) = fun _ ↦ (1 : ℂ) from funext fun z ↦ map_one _, hconst, map_one]
      map_mul' := fun a b ↦ by
        show (jet J fun z ↦ y z (a * b)) = (jet J fun z ↦ y z a) * jet J fun z ↦ y z b
        rw [show (fun z ↦ y z (a * b)) = (fun z ↦ y z a) * (fun z ↦ y z b) from
          funext fun z ↦ map_mul _ _ _]
        exact (hmul _ _ (hyan a 0 h0U) (hyan b 0 h0U)).1
      map_zero' := by
        show (jet J fun z ↦ y z 0) = 0
        rw [show (fun z ↦ y z 0) = fun _ ↦ (0 : ℂ) from funext fun z ↦ map_zero _, hconst, map_zero]
      map_add' := fun a b ↦ by
        show (jet J fun z ↦ y z (a + b)) = (jet J fun z ↦ y z a) + jet J fun z ↦ y z b
        rw [show (fun z ↦ y z (a + b)) = (fun z ↦ y z a) + (fun z ↦ y z b) from
          funext fun z ↦ map_add _ _ _]
        exact (hmul _ _ (hyan a 0 h0U) (hyan b 0 h0U)).2
      commutes' := fun c ↦ by
        show (jet J fun z ↦ y z (algebraMap ℂ B c)) = algebraMap ℂ J.B c
        rw [show (fun z ↦ y z (algebraMap ℂ B c)) = fun _ ↦ c from
          funext fun z ↦ AlgHom.commutes _ _, hconst] }
  have hψ : ∀ b, ψ b = jet J fun z ↦ y z b := fun b ↦ rfl
  have hcoord : ψ.comp g = j.comp g := by
    apply MvPolynomial.algHom_ext
    intro k
    show (jet J fun z ↦ y z (g (MvPolynomial.X k))) = j (g (MvPolynomial.X k))
    rw [← hQ k, ← jet_eval hC J]
    apply hloc
    filter_upwards [hU.mem_nhds h0U] with z hz
    have := congrFun (e.right_inv hz) k
    rw [he, GlobalTheory.AffinePoints.coords_apply] at this
    exact this
  have hres : ∀ b, J.π (j b) = J.π (ψ b) := fun b ↦ by
    rw [hψ, pi_jet hC J _ (hyan b 0 h0U)]
    show J.π (j b) = e.symm (w 0) b
    rw [hw0, e.left_inv hp]
    rfl
  letI : Algebra (MvPolynomial (Fin d) ℂ) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) ℂ) B := hg
  letI : Algebra (MvPolynomial (Fin d) ℂ) J.B := (j.comp g).toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin d) ℂ] J.B := { j.toRingHom with commutes' := fun _ ↦ rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin d) ℂ] J.B :=
    { ψ.toRingHom with commutes' := fun q ↦ AlgHom.congr_fun hcoord q }
  have h12 : ψ₁ = ψ₂ := Algebra.FormallyUnramified.ext' J.π (ker_nil I n J) ψ₁ ψ₂ hres
  refine ⟨U, y, hU, h0U, fun b z hz ↦ (hyan b z hz).differentiableAt.differentiableWithinAt, fun b ↦ ?_⟩
  exact AlgHom.congr_fun h12 b

theorem holLift (hC : JetCalc) : HolLift := by
  intro B _ _ _ I _ n J j
  classical
  let p : B →ₐ[ℂ] ℂ := (piAlg hC J).comp j
  haveI := RingHom.ker_isPrime p
  obtain ⟨s, hs, ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth ℂ (RingHom.ker p)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension ℂ (Localization.Away s) :=
    P.isStandardSmoothOfRelativeDimension rfl
  have hu : IsUnit (j s) := isUnit_of_pi_ne_zero J _ hs
  let j' : Localization.Away s →ₐ[ℂ] J.B := IsLocalization.Away.liftAlgHom s hu
  obtain ⟨U, y', hU, h0U, hd, hj⟩ := holLift_std hC (Localization.Away s) P.dimension J j'
  refine ⟨U, fun z ↦ (y' z).comp (IsScalarTower.toAlgHom ℂ B (Localization.Away s)), hU, h0U,
    fun b ↦ hd _, fun b ↦ ?_⟩
  show j b = jet J fun z ↦ y' z (algebraMap B (Localization.Away s) b)
  rw [← hj]
  simp [j']

end GlobalTheory.LatJet.An.HolLiftProof

theorem GlobalTheory.LatJet.An.holLift_of_jetCalc : JetCalc → HolLift := GlobalTheory.LatJet.An.HolLiftProof.holLift
