import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDivPushMultComplex
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure ConeBranch (P : Ideal (MRing ι)) (d : ℕ) (p : (Σ k, ι k) → ℂ) where

  radius : ℝ
  radius_pos : 0 < radius

  toFun : (Fin d → ℂ) → (Σ k, ι k) → ℂ
  differentiableOn : DifferentiableOn ℂ toFun (Metric.ball 0 radius)
  continuousOn : ContinuousOn toFun (Metric.closedBall 0 radius)
  injOn : Set.InjOn toFun (Metric.closedBall 0 radius)
  map_zero : toFun 0 = p
  mapsTo : Set.MapsTo toFun (Metric.closedBall 0 radius) (mcPts P)

def ConeBranch.image {P : Ideal (MRing ι)} {d : ℕ} {p : (Σ k, ι k) → ℂ} (γ : ConeBranch P d p) :
    Set ((Σ k, ι k) → ℂ) :=
  γ.toFun '' Metric.ball 0 γ.radius

def ConeBranch.slice {P : Ideal (MRing ι)} {d : ℕ} {p : (Σ k, ι k) → ℂ} (γ : ConeBranch P (d + 1) p) :
    Set ((Σ k, ι k) → ℂ) :=
  γ.toFun '' (Metric.ball 0 γ.radius ∩ {t | t 0 = 0})

def ConeBranchesAt (P : Ideal (MRing ι)) (s : MRing ι) (Wa : Ideal (MRingOver ℂ ι)) {d : ℕ}
    (p : (Σ k, ι k) → ℂ) {b : ℕ} (γ : Fin b → ConeBranch P (d + 1) p) (ord : Fin b → ℕ) : Prop :=
  (∀ k, ∃ i, p ⟨k, i⟩ ≠ 0) ∧ (∀ f ∈ Wa, eval p f = 0) ∧
    (∃ N ∈ 𝓝 p, mcPts P ∩ N ⊆ ⋃ j, (γ j).image) ∧
    (∀ j j', j ≠ j' → (γ j).image ∩ (γ j').image ⊆ {v | eval v (map (Int.castRingHom ℂ) s) = 0}) ∧
    (∃ N ∈ 𝓝 p, ∀ j, {v | ∀ f ∈ Wa, eval v f = 0} ∩ N ⊆ (γ j).slice) ∧
    ∀ j, ∃ H : (Fin (d + 1) → ℂ) → ℂ, DifferentiableOn ℂ H (Metric.ball 0 (γ j).radius) ∧
      (∀ t ∈ Metric.ball 0 (γ j).radius, H t ≠ 0) ∧
      ∀ t ∈ Metric.ball 0 (γ j).radius, eval ((γ j).toFun t) (map (Int.castRingHom ℂ) s) = t 0 ^ ord j * H t

end Objects

def ConeBranchLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (s : MRing ι) (a : K → ℕ) (W' : Ideal (MRing ι)) (Wa : Ideal (MRingOver ℂ ι))
    (p : (Σ k, ι k) → ℂ) (b : ℕ) (γ : Fin b → ConeBranch P (n + Fintype.card K + 1) p)
    (ord : Fin b → ℕ),
    IsArithVar P (n + 2) → IsMultiHomog s a → s ∉ P → W' ∈ divSupp P s → IsHorizontal W' →
    Wa ∈ (W'.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
    ConeBranchesAt P s Wa p γ ord →
      multAt ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))) Wa = ∑ j, ord j

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

def ptZeroOne : (Σ k : Unit, PBlk 2 k) → ℂ := fun q => if q.2 = 0 then 0 else 1

def lineFun (t : Fin 2 → ℂ) : (Σ k : Unit, PBlk 2 k) → ℂ := fun q => if q.2 = 0 then t 0 else 1 + t 1

theorem differentiable_lineFun : Differentiable ℂ lineFun := by
  refine differentiable_pi.2 fun q => ?_
  by_cases h : q.2 = 0
  · simp only [lineFun, h, if_true]
    exact differentiable_apply 0
  · simp only [lineFun, h, if_false]
    exact (differentiable_const 1).add (differentiable_apply 1)

theorem lineFun_cover (v : (Σ k : Unit, PBlk 2 k) → ℂ) (hv : v ∈ Metric.ball ptZeroOne (1 / 2)) :
    ∃ t ∈ Metric.ball (0 : Fin 2 → ℂ) (1 / 2), lineFun t = v ∧ t 0 = v ⟨(), 0⟩ := by
  rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num)] at hv
  have h0 := hv ⟨(), 0⟩
  have h1 := hv ⟨(), 1⟩
  simp only [ptZeroOne, dist_eq_norm] at h0 h1
  refine ⟨![v ⟨(), 0⟩, v ⟨(), 1⟩ - 1], ?_, ?_, rfl⟩
  · rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)]
    intro i
    fin_cases i
    · simpa using h0
    · simpa using h1
  · funext q
    obtain ⟨⟨⟩, i⟩ := q
    fin_cases i <;> simp [lineFun]

def lineBranch : ConeBranch (⊥ : Ideal (MRing (PBlk 2))) 2 ptZeroOne where
  radius := 1 / 2
  radius_pos := by norm_num
  toFun := lineFun
  differentiableOn := differentiable_lineFun.differentiableOn
  continuousOn := differentiable_lineFun.continuous.continuousOn
  injOn := by
    intro t _ t' _ h
    funext i
    fin_cases i
    · have := congrFun h ⟨(), 0⟩
      simpa [lineFun] using this
    · have := congrFun h ⟨(), 1⟩
      simpa [lineFun] using this
  map_zero := by
    funext q
    simp only [lineFun, ptZeroOne]
    split_ifs <;> simp
  mapsTo := by
    intro t ht
    refine ⟨fun _ => ⟨1, ?_⟩, fun f hf => ?_⟩
    · show (if (1 : Fin 2) = 0 then t 0 else 1 + t 1) ≠ 0
      rw [if_neg (by decide)]
      have h1 : ‖t 1‖ ≤ 1 / 2 := (norm_le_pi_norm t 1).trans (mem_closedBall_zero_iff.mp ht)
      intro h
      have h2 : t 1 = -1 := by linear_combination h
      rw [h2, norm_neg, norm_one] at h1
      norm_num at h1
    · rw [Submodule.mem_bot] at hf
      simp [hf]

theorem span_Xc_mem_divSupp :
    (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∈ divSupp (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) := by
  refine ⟨?_, fun k => ⟨1, ?_⟩⟩
  · rw [bot_sup_eq]
    have : (Ideal.span {(Xc 2 0 : MRing (PBlk 2))}).IsPrime :=
      (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  · obtain ⟨⟩ := k
    intro h
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp h
    have := congrArg (MvPolynomial.eval (fun q : Σ k : Unit, PBlk 2 k => if q.2 = 0 then (0 : ℤ) else 1)) hg
    simp [Xc] at this

theorem lineBranch_branchesAt :
    ConeBranchesAt (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) (Ideal.span {X ⟨(), 0⟩}) (d := 1) ptZeroOne
      (fun _ : Fin 1 => lineBranch) (fun _ => 1) := by
  refine ⟨fun _ => ⟨1, by simp [ptZeroOne]⟩, ?_,
    ⟨Metric.ball ptZeroOne (1 / 2), Metric.ball_mem_nhds _ (by norm_num), ?_⟩,
    fun j j' h => absurd (Subsingleton.elim j j') h,
    ⟨Metric.ball ptZeroOne (1 / 2), Metric.ball_mem_nhds _ (by norm_num), ?_⟩,
    fun _ => ⟨fun _ => 1, differentiableOn_const _, fun _ _ => one_ne_zero, fun t _ => ?_⟩⟩
  · intro f hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
    simp [ptZeroOne]
  · rintro v ⟨-, hv⟩
    obtain ⟨t, ht, htv, -⟩ := lineFun_cover v hv
    exact Set.mem_iUnion.mpr ⟨0, t, ht, htv⟩
  · rintro _ v ⟨hv0, hv⟩
    obtain ⟨t, ht, htv, ht0⟩ := lineFun_cover v hv
    have h0 : v ⟨(), 0⟩ = 0 := by
      simpa using hv0 _ (Ideal.subset_span (Set.mem_singleton _))
    exact ⟨t, ⟨ht, by simp [ht0, h0]⟩, htv⟩
  · simp [lineBranch, lineFun, Xc]

theorem ConeBranchLength.hyps_inhabited :
    ∃ (b : ℕ) (γ : Fin b → ConeBranch (⊥ : Ideal (MRing (PBlk 2))) (0 + Fintype.card Unit + 1) ptZeroOne)
      (ord : Fin b → ℕ),
      IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (0 + 2) ∧ IsMultiHomog (Xc 2 0) (fun _ => 1) ∧
      Xc 2 0 ∉ (⊥ : Ideal (MRing (PBlk 2))) ∧
      (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∈ divSupp ⊥ (Xc 2 0) ∧
      IsHorizontal (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∧
      (Ideal.span {X ⟨(), 0⟩} : Ideal (MRingOver ℂ (PBlk 2))) ∈
        ((Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))).map
          (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes ∧
      ConeBranchesAt ⊥ (Xc 2 0) (Ideal.span {X ⟨(), 0⟩}) ptZeroOne γ ord :=
  ⟨1, fun _ => lineBranch, fun _ => 1, isArithVar_projLine, isMultiHomog_Xc 2 0,
    by rw [Submodule.mem_bot]; exact X_ne_zero _, span_Xc_mem_divSupp,
    DivPushMultComplex.hyps_inhabited.2.1, DivPushMultComplex.hyps_inhabited.2.2, lineBranch_branchesAt⟩

end Inhabitants

end GroundTheory.Heights₂.Heights.Targets
