import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

noncomputable section

namespace GlobalTheory.ColNorms.CplCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder Matrix

theorem diag_sum_le {V ι : Type} [AddCommGroup V] (B : V →+ V →+ ℝ) (hB : ∀ x, 0 ≤ B x x) (s : Finset ι) (x : ι → V) :
    B (∑ i ∈ s, x i) (∑ i ∈ s, x i) ≤ s.card * ∑ i ∈ s, B (x i) (x i) := by
  have h1 : ∀ a b, B a b + B b a ≤ B a a + B b b := by
    intro a b
    have := hB (a - b)
    simp only [map_sub, AddMonoidHom.sub_apply] at this
    linarith
  have e : B (∑ i ∈ s, x i) (∑ i ∈ s, x i) = ∑ i ∈ s, ∑ j ∈ s, B (x i) (x j) := by
    rw [map_sum B x s, AddMonoidHom.finset_sum_apply]
    exact Finset.sum_congr rfl fun i _ => map_sum _ _ _
  have e' : ∑ i ∈ s, ∑ j ∈ s, B (x j) (x i) = ∑ i ∈ s, ∑ j ∈ s, B (x i) (x j) := Finset.sum_comm
  have h2 : ∑ i ∈ s, ∑ j ∈ s, (B (x i) (x j) + B (x j) (x i)) ≤ ∑ i ∈ s, ∑ j ∈ s, (B (x i) (x i) + B (x j) (x j)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 _ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h2
  rw [e]
  linarith

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def reForm (S : GSD K) (v : InfinitePlace K) : S.V →+ S.V →+ ℝ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => (S.pairAt v x y).re) (by
      intro y z
      simp only [GSD.pairAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]))
    (by
      intro x y
      ext z
      simp only [GSD.pairAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re,
        AddMonoidHom.mk'_apply, AddMonoidHom.add_apply])

theorem sq_nonneg' {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) (x : S.V) : 0 ≤ (S.pairAt v x x).re := by
  have e : S.pairAt v x x = star (fun i => v.embedding (S.bV.repr x i)) ⬝ᵥ
      S.gramV.map v.embedding *ᵥ fun i => v.embedding (S.bV.repr x i) := by
    simp only [GSD.pairAt, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, starRingEnd_apply,
      mul_assoc]
  rw [e]
  exact (Complex.nonneg_iff.1 (Matrix.PosSemidef.dotProduct_mulVec_nonneg h _)).1

theorem sq_sum_le {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) {ι : Type} (s : Finset ι) (x : ι → S.V) {m : ℝ}
    (hm : (s.card : ℝ) ≤ m) :
    (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re ≤ m * ∑ i ∈ s, (S.pairAt v (x i) (x i)).re :=
  (diag_sum_le (reForm S v) (sq_nonneg' h) s x).trans
    (mul_le_mul_of_nonneg_right hm (Finset.sum_nonneg fun _ _ => sq_nonneg' h _))

theorem inv_nat_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := Nat.cast_inv_le_one n

theorem sq_smul_le {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) (n : ℕ) (x : S.V) :
    (S.pairAt v ((n : K)⁻¹ • x) ((n : K)⁻¹ • x)).re ≤ (n : ℝ)⁻¹ * (S.pairAt v x x).re := by
  have e : S.pairAt v ((n : K)⁻¹ • x) ((n : K)⁻¹ • x) = (((n : ℝ)⁻¹ * (n : ℝ)⁻¹ : ℝ) : ℂ) * S.pairAt v x x := by
    simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, mul_assoc]
  have h0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ * (S.pairAt v x x).re := mul_nonneg (by positivity) (sq_nonneg' h x)
  exact mul_le_of_le_one_left h0 (inv_nat_le_one n)

theorem ipAt_re (S : GSD K) (h : S.Ok) (v : InfinitePlace K) (φ : S.D → S.V) :
    (S.ipAt h v φ φ).re = letI := h.fintypeCl
      ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re := by
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.re_ofReal_mul]
  push_cast
  rfl

theorem comp_opLe {S₀ S S₁ : GSD K} {Y : Cpl S} (A : CplKer S₀ S S₁ Y) (hS : S.Ok) (v : InfinitePlace K)
    {t₁ t₂ h ny : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hh : 0 ≤ h) (hny : 0 ≤ ny) (p₀ : PosAt S₀ v) (p₁ : PosAt S₁ v)
    (hc : (Nat.card S.Cl : ℝ) ≤ h) (hy : ∀ d, ((Y.ys d).ncard : ℝ) ≤ ny)
    (h1 : ∀ d₀ d, ∀ y ∈ Y.ys d, OpLe S₀ S v (A.k1 d₀ d y) t₁) (h2 : ∀ d d₁, ∀ y ∈ Y.ys d, OpLe S S₁ v (A.k2 d y d₁) t₂)
    (d₀ : S₀.D) (d₁ : S₁.D) : OpLe S₀ S₁ v ((A.comp hS S.outSec).k d₀ d₁) (h ^ 2 * ny ^ 2 * t₁ * t₂) := by
  intro x
  letI := hS.fintypeCl
  have hc' : ((Finset.univ : Finset S.Cl).card : ℝ) ≤ h := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  have hx := sq_nonneg' p₀ x
  have e : (A.comp hS S.outSec).k d₀ d₁ x = ∑ c : S.Cl, (((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x) := by
    simp only [CplKer.comp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [e]
  refine (sq_sum_le p₁ _ _ hc').trans ?_
  have key : ∀ c : S.Cl, (S₁.pairAt v ((((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x))
      ((((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x))).re ≤
      ny * (ny * (t₂ * (t₁ * (S₀.pairAt v x x).re))) := by
    intro c
    have hy' : (((Y.fin (S.outSec.rep c)).toFinset.card : ℕ) : ℝ) ≤ ny := by
      rw [← Set.ncard_eq_toFinset_card _ (Y.fin _)]
      exact hy _
    refine (sq_smul_le p₁ _ _).trans ((mul_le_of_le_one_left (sq_nonneg' p₁ _) (inv_nat_le_one _)).trans ?_)
    refine (sq_sum_le p₁ _ _ hy').trans (mul_le_mul_of_nonneg_left ?_ hny)
    refine (Finset.sum_le_card_nsmul _ _ (t₂ * (t₁ * (S₀.pairAt v x x).re)) fun y hy => ?_).trans ?_
    · have hy0 : y ∈ Y.ys (S.outSec.rep c) := (Set.Finite.mem_toFinset _).1 hy
      exact (h2 _ _ y hy0 _).trans (mul_le_mul_of_nonneg_left (h1 _ _ y hy0 _) ht₂)
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hy' (by positivity)
  have h3 := Finset.sum_le_card_nsmul Finset.univ _ _ fun c _ => key c
  rw [nsmul_eq_mul] at h3
  calc _ ≤ h * (h * (ny * (ny * (t₂ * (t₁ * (S₀.pairAt v x x).re))))) :=
        mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right hc' (by positivity))) hh
    _ = _ := by ring

theorem appOf_le {S S' : GSD K} (A : ClsKer S S') (hS : S.Ok) (v : InfinitePlace K) {t h : ℝ} (hh : 0 ≤ h)
    (p' : PosAt S' v) (hc : (Nat.card S.Cl : ℝ) ≤ h) (hA : ∀ d d', OpLe S S' v (A.k d d') t) (φ : S.D → S.V) (d' : S'.D) :
    (S'.pairAt v (A.appOf hS S.outSec φ d') (A.appOf hS S.outSec φ d')).re ≤ h * (t * (S.ipAt hS v φ φ).re) := by
  letI := hS.fintypeCl
  have hc' : ((Finset.univ : Finset S.Cl).card : ℝ) ≤ h := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  unfold ClsKer.appOf
  refine (sq_sum_le p' _ _ hc').trans (mul_le_mul_of_nonneg_left ?_ hh)
  rw [ipAt_re, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => (sq_smul_le p' _ _).trans ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hA _ _ _) (by positivity)

theorem cpl_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (v : InfinitePlace K) (t₁ t₂ h₀ h h₁ ny : ℝ), 0 ≤ t₁ → 0 ≤ t₂ → 0 ≤ h₀ → 0 ≤ h → 0 ≤ h₁ → 0 ≤ ny → (∀ b, PosAt ((Q.F Q.n).mem b) v) → PosAt Q.S v → PosAt Q.S₁ v → (∀ b, (Nat.card ((Q.F Q.n).mem b).Cl : ℝ) ≤ h₀) → (Nat.card Q.S.Cl : ℝ) ≤ h → (Nat.card Q.S₁.Cl : ℝ) ≤ h₁ → (∀ d, ((Q.Y.ys d).ncard : ℝ) ≤ ny) → (∀ b d₀ d, ∀ y ∈ Q.Y.ys d, OpLe ((Q.F Q.n).mem b) Q.S v ((Q.cp b).k1 d₀ d y) t₁) → (∀ b d d₁, ∀ y ∈ Q.Y.ys d, OpLe Q.S Q.S₁ v ((Q.cp b).k2 d y d₁) t₂) → ∀ φ : (Q.F Q.n).Forms, (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤ (Fintype.card (Q.F Q.n).β : ℝ) * h₀ * h ^ 2 * h₁ * ny ^ 2 * t₁ * t₂ * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
  intro K _ _ _ Q v t₁ t₂ h₀ h h₁ ny ht₁ ht₂ hh₀ hh hh₁ hny p₀ _ p₁ c₀ c c₁ hy k1 k2 φ
  letI := Q.hS₁.fintypeCl
  have hc' : ((Finset.univ : Finset Q.S₁.Cl).card : ℝ) ≤ h₁ := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  set M : ℝ := (Fintype.card (Q.F Q.n).β : ℝ) * (h₀ * (h ^ 2 * ny ^ 2 * t₁ * t₂ *
    (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re)) with hM
  have key : ∀ d : Q.S₁.D, (Q.S₁.pairAt v ((Q.cpl φ : Q.S₁.D → Q.S₁.V) d) ((Q.cpl φ : Q.S₁.D → Q.S₁.V) d)).re ≤ M := by
    intro d
    have e : (Q.cpl φ : Q.S₁.D → Q.S₁.V) d = ∑ b : (Q.F Q.n).β,
        ((Q.cp b).comp Q.hS Q.S.outSec).appOf (Q.hF Q.n b) ((Q.F Q.n).mem b).outSec (φ b) d := by
      simp only [KerChain.cpl, LinearMap.sum_apply, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
      rfl
    rw [e]
    refine (sq_sum_le p₁ _ _ (le_of_eq (by rw [Finset.card_univ]))).trans
      (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    unfold famIpAt
    rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => appOf_le _ _ v hh₀ p₁ (c₀ b)
      (comp_opLe (Q.cp b) Q.hS v ht₁ ht₂ hh hny (p₀ b) p₁ c hy (k1 b) (k2 b)) _ _
  have hF : 0 ≤ (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
    unfold famIpAt
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun b _ => ?_
    rw [ipAt_re]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sq_nonneg' (p₀ b) _)
  have hM0 : 0 ≤ M := by positivity
  rw [ipAt_re]
  refine (Finset.sum_le_card_nsmul _ _ M fun c _ =>
    (mul_le_of_le_one_left (sq_nonneg' p₁ _) (inv_nat_le_one _)).trans (key _)).trans ?_
  rw [nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right hc' hM0).trans (le_of_eq ?_)
  rw [hM]
  ring

end GlobalTheory.ColNorms.CplCS
