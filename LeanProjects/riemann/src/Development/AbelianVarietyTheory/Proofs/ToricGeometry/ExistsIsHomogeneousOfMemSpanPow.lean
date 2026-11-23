import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

namespace ThetaGen

section Abstract

variable {X : Type}

def homog (d : ℕ) (f : X → ℂ) : ℂ × X → ℂ := fun p => p.1 ^ d * f p.2

theorem homog_mul (a b : ℕ) (f h : X → ℂ) :
    homog a f * homog b h = homog (a + b) (f * h) := by
  funext p; simp only [homog, Pi.mul_apply]; ring

def homogL (d : ℕ) : (X → ℂ) →ₗ[ℂ] (ℂ × X → ℂ) where
  toFun := homog d
  map_add' f h := by funext p; simp only [homog, Pi.add_apply]; ring
  map_smul' c f := by funext p; simp only [homog, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mem_of_homog_mem_iSup (T : ℕ → Submodule ℂ (X → ℂ)) (d : ℕ) (f : X → ℂ)
    (h : homog d f ∈ ⨆ k, (T k).map (homogL k)) : f ∈ T d := by
  have key : ∀ F ∈ ⨆ k, (T k).map (homogL (X := X) k),
      ∃ u : Polynomial (X → ℂ), (∀ k, u.coeff k ∈ T k) ∧
        ∀ t x, F (t, x) = (u.map (Pi.evalRingHom (fun _ : X => ℂ) x)).eval t := by
    intro F hF
    induction hF using Submodule.iSup_induction' with
    | mem k F hF =>
      obtain ⟨v, hv, rfl⟩ := hF
      refine ⟨Polynomial.monomial k v, fun j => ?_, fun t x => ?_⟩
      · rw [Polynomial.coeff_monomial]
        split_ifs with hj
        · exact hj ▸ hv
        · exact zero_mem _
      · simp [homogL, homog, mul_comm]
    | zero => exact ⟨0, fun k => by simp, fun t x => by simp⟩
    | add F G _ _ hF hG =>
      obtain ⟨u, hu, hu'⟩ := hF
      obtain ⟨v, hv, hv'⟩ := hG
      exact ⟨u + v, fun k => by rw [Polynomial.coeff_add]; exact add_mem (hu k) (hv k),
        fun t x => by simp [hu', hv']⟩
  obtain ⟨u, hu, hu'⟩ := key _ h
  have : f = u.coeff d := by
    funext x
    have h1 : u.map (Pi.evalRingHom (fun _ : X => ℂ) x) = Polynomial.monomial d (f x) := by
      apply Polynomial.funext
      intro t
      rw [← hu']
      simp [homog, mul_comm]
    have h2 := congrArg (fun q => Polynomial.coeff q d) h1
    simpa using h2.symm
  exact this ▸ hu d

variable (R : ℕ → Submodule ℂ (X → ℂ))

def gradedRing : Subalgebra ℂ (ℂ × X → ℂ) :=
  Algebra.adjoin ℂ {F | ∃ d, ∃ f ∈ R d, F = homog d f}

theorem gradedRing_le_iSup (h1 : (1 : X → ℂ) ∈ R 0)
    (hmul : ∀ a b, R a * R b ≤ R (a + b)) {F : ℂ × X → ℂ} (hF : F ∈ gradedRing R) :
    F ∈ Submodule.span ℂ {F | ∃ d, ∃ f ∈ R d, F = homog d f} := by
  have : Subalgebra.toSubmodule (gradedRing R) =
      Submodule.span ℂ {F | ∃ d, ∃ f ∈ R d, F = homog d f} := by
    unfold gradedRing
    rw [Algebra.adjoin_eq_span]
    apply le_antisymm
    · apply Submodule.span_mono
      intro G hG
      induction hG using Submonoid.closure_induction with
      | mem x hx => exact hx
      | one => exact ⟨0, 1, h1, by funext p; simp [homog]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, f, hf, rfl⟩ := hx
        obtain ⟨b, h, hh, rfl⟩ := hy
        exact ⟨a + b, f * h, hmul a b (Submodule.mul_mem_mul hf hh), homog_mul _ _ _ _⟩
    · exact Submodule.span_mono Submonoid.subset_closure
  rw [← this]; exact hF

theorem exists_succ_le_mul (h1 : (1 : X → ℂ) ∈ R 0)
    (hmul : ∀ a b, R a * R b ≤ R (a + b)) (A : Subalgebra ℂ (ℂ × X → ℂ))
    (hA : A ≤ Algebra.adjoin ℂ {F | ∃ f ∈ R 1, F = homog 1 f})
    (M : Submodule A (ℂ × X → ℂ)) (hM : M.FG) (hMR : ∀ F, F ∈ M ↔ F ∈ gradedRing R) :
    ∃ e, ∀ d, e ≤ d → R (d + 1) ≤ R 1 * R d := by
  let N : ℕ →o Submodule A (ℂ × X → ℂ) :=
    ⟨fun e => Submodule.span A {F | ∃ d ≤ e, ∃ f ∈ R d, F = homog d f}, fun a b hab =>
      Submodule.span_mono (by
        rintro _ ⟨d, hd, h⟩
        exact ⟨d, hd.trans hab, h⟩)⟩
  have hN : ⨆ e, N e = M := by
    apply le_antisymm
    · refine iSup_le fun e => Submodule.span_le.2 ?_
      rintro _ ⟨d, -, f, hf, rfl⟩
      exact (hMR _).2 (Algebra.subset_adjoin ⟨d, f, hf, rfl⟩)
    · intro F hF
      have := gradedRing_le_iSup R h1 hmul ((hMR F).1 hF)
      clear hF
      induction this using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨d, f, hf, rfl⟩ := hx
        exact Submodule.mem_iSup_of_mem d (Submodule.subset_span ⟨d, le_rfl, f, hf, rfl⟩)
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul c x _ hx => exact Submodule.smul_of_tower_mem _ c hx
  obtain ⟨e, he⟩ := hM.stabilizes_of_iSup_eq N hN
  refine ⟨e, fun d hd f hf => ?_⟩
  let T : ℕ → Submodule ℂ (X → ℂ) := fun k => if k ≤ e then R k else R 1 * R (k - 1)
  have hTR : ∀ k, T k ≤ R k := by
    intro k
    simp only [T]
    split_ifs with hk
    · exact le_rfl
    · have := hmul 1 (k - 1)
      rwa [show 1 + (k - 1) = k by omega] at this
  have hRT : ∀ k, R 1 * R k ≤ T (1 + k) := by
    intro k
    simp only [T]
    split_ifs with hk
    · exact hmul 1 k
    · simp
  let W : Submodule ℂ (ℂ × X → ℂ) := ⨆ k, (T k).map (homogL k)
  have hAW : ∀ a ∈ Algebra.adjoin ℂ {F | ∃ f ∈ R 1, F = homog 1 f}, ∀ w ∈ W, a * w ∈ W := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      intro w hw
      induction hw using Submodule.iSup_induction' with
      | mem k F hF =>
        obtain ⟨v, hv, rfl⟩ := hF
        refine Submodule.mem_iSup_of_mem (1 + k) ⟨s * v, hRT k (Submodule.mul_mem_mul hs (hTR k hv)), ?_⟩
        exact (homog_mul _ _ _ _).symm
      | zero => simp
      | add F G _ _ hF hG => rw [mul_add]; exact add_mem hF hG
    | algebraMap c => intro w hw; rw [← Algebra.smul_def]; exact W.smul_mem c hw
    | add x y _ _ hx hy => intro w hw; rw [add_mul]; exact add_mem (hx w hw) (hy w hw)
    | mul x y _ _ hx hy => intro w hw; rw [mul_assoc]; exact hx _ (hy w hw)
  have hNW : ∀ F ∈ N e, F ∈ W := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, v, hv, rfl⟩ := hx
      exact Submodule.mem_iSup_of_mem k ⟨v, by simpa [T, hk] using hv, rfl⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact hAW a (hA a.2) x hx
  have hmem : homog (d + 1) f ∈ N e := by
    rw [← he, hMR]
    exact Algebra.subset_adjoin ⟨d + 1, f, hf, rfl⟩
  have := mem_of_homog_mem_iSup T (d + 1) f (hNW _ hmem)
  simpa [T, show ¬ (d + 1 ≤ e) by omega] using this

theorem le_pow_of_succ_le_mul (hmul : ∀ a b, R a * R b ≤ R (a + b)) {e : ℕ} (h1e : 1 ≤ e)
    (he : ∀ d, e ≤ d → R (d + 1) ≤ R 1 * R d) (j : ℕ) : R (e * (j + 1)) ≤ R e ^ (j + 1) := by
  have h : ∀ d, e ≤ d → ∀ k, R (d + (k + 1)) ≤ R (k + 1) * R d := by
    intro d hd k
    induction k with
    | zero => exact he d hd
    | succ k ih =>
      calc R (d + (k + 1 + 1)) ≤ R 1 * R (d + (k + 1)) := he (d + (k + 1)) (by omega)
        _ ≤ R 1 * (R (k + 1) * R d) := by gcongr
        _ = (R 1 * R (k + 1)) * R d := (mul_assoc _ _ _).symm
        _ ≤ R (k + 1 + 1) * R d := by
          have := hmul 1 (k + 1)
          rw [add_comm 1] at this
          gcongr
  induction j with
  | zero => simp
  | succ j ih =>
    rcases e with _ | k
    · omega
    · have := h ((k + 1) * (j + 1)) (Nat.le_mul_of_pos_right _ (by omega)) k
      calc R ((k + 1) * (j + 1 + 1)) = R ((k + 1) * (j + 1) + (k + 1)) := by rw [mul_add_one]
        _ ≤ R (k + 1) * R ((k + 1) * (j + 1)) := this
        _ ≤ R (k + 1) * R (k + 1) ^ (j + 1) := by gcongr
        _ = _ := by rw [← pow_succ']

end Abstract

section Entire

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem entire_mul_eq_zero {f h : E → ℂ} (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (hfh : f * h = 0) : f = 0 ∨ h = 0 := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne.1
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne.2
  have hl : Differentiable ℂ (fun t : ℂ => x + t • (y - x)) := by fun_prop
  have h1 : AnalyticOnNhd ℂ (fun t : ℂ => f (x + t • (y - x))) Set.univ :=
    fun t _ => (hf.comp hl).analyticAt t
  have h2 : AnalyticOnNhd ℂ (fun t : ℂ => h (x + t • (y - x))) Set.univ :=
    fun t _ => (hh.comp hl).analyticAt t
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero h1 h2
    (fun t _ => congrFun hfh _) isPreconnected_univ with h3 | h3
  · exact hx (by simpa using h3 0 trivial)
  · exact hy (by simpa using h3 1 trivial)

theorem differentiable_of_mem_adjoin {S : Set (E → ℂ)} (hS : ∀ F ∈ S, Differentiable ℂ F)
    {F : E → ℂ} (hF : F ∈ Algebra.adjoin ℂ S) : Differentiable ℂ F := by
  induction hF using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap c => exact differentiable_const _
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

theorem const_of_isIntegral {ι : Type} (θ : ι → E → ℂ) {f : E → ℂ} (hf : Differentiable ℂ f)
    (hint : IsIntegral (Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2))
      (fun p : ℂ × E => p.1 ^ 0 * f p.2)) (z : E) : f z = f 0 := by
  set A := Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2) with hA
  have hc : ∀ a ∈ A, ∀ x, a (0, x) = a (0, 0) := by
    intro a ha x
    induction ha using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; simp
    | algebraMap c => rfl
    | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]
    | mul x y _ _ hx hy => simp only [Pi.mul_apply, hx, hy]
  obtain ⟨P, hP, hP0⟩ := hint
  let φ : A →+* ℂ := (Pi.evalRingHom (fun _ : ℂ × E => ℂ) (0, 0)).comp (algebraMap A _)
  have hroot : ∀ x, (P.map φ).IsRoot (f x) := by
    intro x
    have h1 : (Pi.evalRingHom (fun _ : ℂ × E => ℂ) (0, x)).comp (algebraMap A _) = φ :=
      RingHom.ext fun a => hc a a.2 x
    have h2 := congrArg (Pi.evalRingHom (fun _ : ℂ × E => ℂ) (0, x)) hP0
    rw [Polynomial.hom_eval₂, h1] at h2
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    simpa using h2
  refine hf.apply_eq_apply_of_bounded (Set.Finite.isBounded ?_) z 0
  refine (Polynomial.finite_setOf_isRoot (hP.map φ).ne_zero).subset ?_
  rintro _ ⟨x, rfl⟩
  exact hroot x

theorem exists_succ_le_mul_of_integral {ι : Type} [Finite ι] (R : ℕ → Submodule ℂ (E → ℂ))
    (h1 : (1 : E → ℂ) ∈ R 0) (hmul : ∀ a b, R a * R b ≤ R (a + b))
    (hdiff : ∀ d, ∀ f ∈ R d, Differentiable ℂ f) (θ : ι → E → ℂ) (hθ : ∀ c, θ c ∈ R 1)
    (hint : ∀ d, ∀ f ∈ R d,
      IsIntegral (Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2))
        (fun p : ℂ × E => p.1 ^ d * f p.2) ∧
      ∃ a ∈ Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2),
        ∃ b ∈ Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2),
          b ≠ 0 ∧ b * (fun p : ℂ × E => p.1 ^ d * f p.2) = a)
    (hfin : ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A]
      [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B],
      (∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) →
        Module.Finite A B) :
    ∃ e, ∀ d, e ≤ d → R (d + 1) ≤ R 1 * R d := by
  set A := Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2) with hA
  have hA1 : A ≤ Algebra.adjoin ℂ {F | ∃ f ∈ R 1, F = homog 1 f} := by
    apply Algebra.adjoin_mono
    rintro _ ⟨c, rfl⟩
    exact ⟨θ c, hθ c, by funext p; simp [homog]⟩
  have hAR : A ≤ gradedRing R := hA1.trans (Algebra.adjoin_mono (by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨1, f, hf, rfl⟩))
  let B : Subalgebra A (ℂ × E → ℂ) := Algebra.adjoin A {F | ∃ d, ∃ f ∈ R d, F = homog d f}
  have hB : ∀ F, F ∈ B ↔ F ∈ gradedRing R := by
    intro F
    constructor
    · intro hF
      induction hF using Algebra.adjoin_induction with
      | mem x hx => exact Algebra.subset_adjoin hx
      | algebraMap c => exact hAR c.2
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy
    · intro hF
      induction hF using Algebra.adjoin_induction with
      | mem x hx => exact Algebra.subset_adjoin hx
      | algebraMap c => exact B.algebraMap_mem (algebraMap ℂ A c)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy
  have hd : ∀ F ∈ gradedRing R, Differentiable ℂ F := by
    intro F hF
    refine differentiable_of_mem_adjoin ?_ hF
    rintro _ ⟨d, f, hf, rfl⟩
    have := hdiff d f hf
    unfold homog
    fun_prop
  haveI : NoZeroDivisors A := ⟨fun {a b} hab =>
    (entire_mul_eq_zero (hd _ (hAR a.2)) (hd _ (hAR b.2)) (congrArg Subtype.val hab)).imp
      Subtype.ext Subtype.ext⟩
  haveI : NoZeroDivisors B := ⟨fun {a b} hab =>
    (entire_mul_eq_zero (hd _ ((hB _).1 a.2)) (hd _ ((hB _).1 b.2))
      (congrArg Subtype.val hab)).imp Subtype.ext Subtype.ext⟩
  haveI : IsDomain A := NoZeroDivisors.to_isDomain _
  haveI : Nontrivial B := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  haveI : IsDomain B := NoZeroDivisors.to_isDomain _
  haveI : Algebra.FiniteType ℂ A :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2
    fun a b hab => Subtype.ext (congrArg (Subtype.val : B → (ℂ × E → ℂ)) hab)
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.adjoin (by
    rintro _ ⟨d, f, hf, rfl⟩
    exact (hint d f hf).1)
  have hfrac : ∀ F ∈ B, ∃ a a' : A, a' ≠ 0 ∧ (a' : ℂ × E → ℂ) * F = a := by
    intro F hF
    induction hF using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨d, f, hf, rfl⟩ := hx
      obtain ⟨a, ha, b, hb, hb0, h⟩ := (hint d f hf).2
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h0 => hb0 (congrArg Subtype.val h0), h⟩
    | algebraMap c => exact ⟨c, 1, one_ne_zero, one_mul _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, a', ha, h⟩ := hx
      obtain ⟨b, b', hb, h'⟩ := hy
      refine ⟨b' * a + a' * b, a' * b', mul_ne_zero ha hb, ?_⟩
      push_cast
      rw [← h, ← h']; ring
    | mul x y _ _ hx hy =>
      obtain ⟨a, a', ha, h⟩ := hx
      obtain ⟨b, b', hb, h'⟩ := hy
      refine ⟨a * b, a' * b', mul_ne_zero ha hb, ?_⟩
      push_cast
      rw [← h, ← h']; ring
  have hF : Module.Finite A B := hfin A B fun b => by
    obtain ⟨a, a', ha, h⟩ := hfrac b b.2
    exact ⟨a, a', ha, Subtype.ext h⟩
  exact exists_succ_le_mul R h1 hmul A hA1 (Subalgebra.toSubmodule B)
    (Module.Finite.iff_fg.1 hF) hB

end Entire

theorem exists_isHomogeneous_of_mem_span_pow {X ι : Type} (θ : ι → X → ℂ) (d : ℕ) {f : X → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range θ) ^ d) :
    ∃ F : MvPolynomial ι ℂ, F.IsHomogeneous d ∧
      ∀ z, f z = MvPolynomial.eval (fun c => θ c z) F := by
  have h : Submodule.span ℂ (Set.range θ) ^ d =
      Submodule.map (MvPolynomial.aeval θ).toLinearMap
        (MvPolynomial.homogeneousSubmodule ι ℂ d) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow]
    simp [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
      Function.comp_def]
  rw [h] at hf
  obtain ⟨F, hF, rfl⟩ := hf
  refine ⟨F, hF, fun z => ?_⟩
  have := MvPolynomial.comp_aeval_apply θ (Pi.evalAlgHom ℂ (fun _ : X => ℂ) z) F
  simpa using this

def level {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) : Submodule ℂ ((Fin g → ℂ) → ℂ) where
  carrier := {f | Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z,
    f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun n n' z => by
    simp only [Pi.add_apply, ha.2, hb.2, mul_add]⟩
  zero_mem' := ⟨differentiable_const _, fun n n' z => by simp⟩
  smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun n n' z => by
    simp only [Pi.smul_apply, ha.2, smul_eq_mul]; ring⟩

theorem level_mul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : ℕ) :
    level τ a * level τ b ≤ level τ (a + b) := by
  refine Submodule.mul_le.2 fun f hf h hh => ⟨hf.1.mul hh.1, fun n n' z => ?_⟩
  simp only [Pi.mul_apply, hf.2, hh.2]
  rw [Nat.cast_add, neg_add, add_mul, eC_add]
  ring

theorem one_mem_level {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) :
    (1 : (Fin g → ℂ) → ℂ) ∈ level τ 0 :=
  ⟨differentiable_const _, fun n n' z => by simp [eC_zero]⟩

end ThetaGen

open ThetaGen in

theorem theta_ring_generated_in_degree_one :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → IsIntegral (Algebra.adjoin ℂ (Set.range fun (c : Fin g → Fin N) (p : ℂ × (Fin g → ℂ)) => p.1 * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • p.2) ((N : ℂ) • τ))) (fun p : ℂ × (Fin g → ℂ) => p.1 ^ d * f p.2) ∧ ∃ a ∈ (Algebra.adjoin ℂ (Set.range fun (c : Fin g → Fin N) (p : ℂ × (Fin g → ℂ)) => p.1 * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • p.2) ((N : ℂ) • τ))), ∃ b ∈ (Algebra.adjoin ℂ (Set.range fun (c : Fin g → Fin N) (p : ℂ × (Fin g → ℂ)) => p.1 * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • p.2) ((N : ℂ) • τ))), b ≠ 0 ∧ b * (fun p : ℂ × (Fin g → ℂ) => p.1 ^ d * f p.2) = a) → (∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B], (∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) → Module.Finite A B) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ ∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F) := by
  intro hbasis hspan hint hfin g τ hτ
  let R : ℕ → Submodule ℂ ((Fin g → ℂ) → ℂ) := fun d => level τ (3 * d)
  have hmul : ∀ a b, R a * R b ≤ R (a + b) := fun a b => by
    simp only [R, mul_add]; exact level_mul τ _ _
  let θ : (Fin g → Fin 3) → (Fin g → ℂ) → ℂ := fun c z =>
    theta (fun i => ((c i : ℕ) : ℝ) / (3 : ℕ)) 0 (((3 : ℕ) : ℂ) • z) (((3 : ℕ) : ℂ) • τ)
  obtain ⟨e, he⟩ := exists_succ_le_mul_of_integral R (one_mem_level τ) hmul
    (fun d f hf => hf.1) θ (fun c => (hbasis g τ hτ 3 (by norm_num)).1 c)
    (fun d f hf => hint g τ hτ 3 le_rfl d f hf) hfin
  have hpow := le_pow_of_succ_le_mul R hmul (e := e + 1) (by omega)
    (fun d hd => he d (by omega))
  refine ⟨3 * (e + 1), by omega, fun d f hf => ?_⟩
  rcases d with _ | j
  · have hc := const_of_isIntegral θ hf.1 (hint g τ hτ 3 le_rfl 0 f hf).1
    exact ⟨MvPolynomial.C (f 0), MvPolynomial.isHomogeneous_C _ _, fun z => by simp [hc z]⟩
  · have h1 : f ∈ R ((e + 1) * (j + 1)) := by
      simp only [R, ← mul_assoc]; exact hf
    refine exists_isHomogeneous_of_mem_span_pow (fun (c : Fin g → Fin (3 * (e + 1))) z =>
      theta (fun i => ((c i : ℕ) : ℝ) / (3 * (e + 1) : ℕ)) 0 (((3 * (e + 1) : ℕ) : ℂ) • z)
        (((3 * (e + 1) : ℕ) : ℂ) • τ)) (j + 1) ?_
    refine SetLike.le_def.1 (pow_le_pow_left' ?_ (j + 1)) (hpow j h1)
    exact fun u hu => hspan g τ hτ (3 * (e + 1)) (by omega) u hu

end GlobalTheory
