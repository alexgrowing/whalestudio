import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem det_mat_ne_zero {n : ℕ} (g : GU σ n) : (mat g).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n) L).isUnit).ne_zero

theorem constTerm (hF : FracExists) (hP : Pointwise) (hC : Count) (hS : SmallCorner) (hG : GenFun)
    (hU : IsUnramInv ϖ σ q) {a : ℤ} {g₀ : GU σ N} {m : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m) (X : ℂ)
    (hX : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun c : RadQuot σ N => X ^ len (mat (m * (c.out : radQ σ N).1)))
      ((q : ℂ) ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * X ^ (a.natAbs + len (mat g₀)) * jFac q N X) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hq : 1 ≤ q := le_trans (by norm_num) hU.2.2.2.2.2.1
  obtain ⟨U, V, C, hfr, hdet⟩ := hF L ϖ N hv (mat g₀) (det_mat_ne_zero g₀)
  have hPt := hP L ϖ σ q N hU a g₀ m hm U V C (len (mat g₀)) hfr hdet
  have hcard : ∀ j : ℕ, Nat.card {c : RadQuot σ N //
      len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j} =
      q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * q ^ (2 * N * (j / 2) + j) := by
    intro j
    have hiff : ∀ c : RadQuot σ N, len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j ↔
        Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) (c.out : radQ σ N).1 :=
      fun c => (hPt _ (c.out : radQ σ N).2).2 j
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    rw [hC L ϖ σ q N hU C (C * V * mat g₀) (len (mat g₀)) (a.toNat + j / 2) (2 * a.toNat + j) hfr.2.2.1 hdet
      (fun r hr => hS L ϖ σ q N hU g₀ U V C hfr _ _ r (by omega) hr) ?_]
    · rw [← pow_add]; congr 1; generalize j / 2 = t; ring
    · intro u hu k hk hkK hsm
      have hlen : len (mat (m * (u * k))) = len (mat (m * u)) := by
        have h := len_mat_mul (KU σ (N + 2)).one_mem hkK (m * u)
        rwa [one_mul, mul_assoc] at h
      refine ((hPt _ (mul_mem hu hk)).2 j).mp ?_
      rw [hlen]
      exact ((hPt u hu).2 j).mpr hsm
  have key := hG (RadQuot σ N) (fun c => len (mat (m * (c.out : radQ σ N).1))) (a.natAbs + len (mat g₀))
    (q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat)) q N X (Nat.one_le_pow _ _ hq) hq
    (fun c => (hPt _ (c.out : radQ σ N).2).1) hcard hX
  push_cast at key
  exact key

theorem bijective_cells (hS : CosetSurj) (hI : CosetInj) (hU : IsUnramInv ϖ σ q)
    (m : ℤ → GU σ N ⧸ KU σ N → GU σ (N + 2)) (hm : ∀ a y, IsLeviElt ϖ a y.out (m a y)) :
    Function.Bijective fun p : (ℤ × (GU σ N ⧸ KU σ N)) × RadQuot σ N =>
      (QuotientGroup.mk (m p.1.1 p.1.2 * (p.2.out : radQ σ N).1) : GU σ (N + 2) ⧸ KU σ (N + 2)) := by
  constructor
  · rintro ⟨⟨a, y⟩, c⟩ ⟨⟨a', y'⟩, c'⟩ h
    have h' := QuotientGroup.eq.mp h
    obtain ⟨rfl, hy⟩ := hI L ϖ σ q N hU a a' y.out y'.out (m a y) (m a' y') (hm a y) (hm a' y')
      _ (c.out : radQ σ N).2 _ (c'.out : radQ σ N).2 h'
    have hyy : y = y' := by
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      exact QuotientGroup.eq.mpr hy
    subst hyy
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using h'
    rw [hc]
  · intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨a, y, hay⟩ := hS L ϖ σ q N hU g
    obtain ⟨u, hu, k, hk, rfl⟩ := hay (m a y) (hm a y)
    refine ⟨((a, y), (QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N)), ?_⟩
    dsimp only
    apply QuotientGroup.eq.mpr
    have h1 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N))
    rw [Subgroup.mem_subgroupOf] at h1
    have e : (m a y * ((QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N).out : radQ σ N).1)⁻¹ * (m a y * u * k) =
        (((QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N).out)⁻¹ * ⟨u, hu⟩ : radQ σ N).1 * k := by
      simp [mul_assoc]
    rw [e]
    exact mul_mem h1 hk

theorem zVal_succ (q N : ℕ) (X y : ℂ) {r : ℕ} (α : Fin (r + 1) → ℂ) :
    zVal q (N + 2) X y α = (1 - X) * (1 + q * X) * ((1 - y * α 0)⁻¹ * (1 - y / α 0)⁻¹) *
      zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α) := by
  have hp : ∏ j ∈ Finset.range (N + 2), (1 - (-(q : ℂ)) ^ j * X) =
      (1 - X) * (1 + q * X) * ∏ j ∈ Finset.range N, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X)) := by
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    have h : ∀ j ∈ Finset.range N,
        (1 - (-(q : ℂ)) ^ (j + 1 + 1) * X) = (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X)) := by
      intro j _; ring
    rw [Finset.prod_congr rfl h]; ring
  have ho : Odd (N + 2) ↔ Odd N := by rw [Nat.odd_add]; simp
  unfold zVal
  rw [hp, Fin.prod_univ_succ, if_congr ho rfl rfl]
  simp only [Fin.tail]
  ring

theorem hasSum_small (hR : SmallRank) (hU : IsUnramInv ϖ σ q) {n : ℕ} (hn : n ≤ 1) (F : GU σ n → ℂ)
    (hF : ∀ k ∈ KU σ n, F k = 1) : HasSum (fun x : GU σ n ⧸ KU σ n => F x.out) 1 := by
  have hK : ∀ g : GU σ n, g ∈ KU σ n := fun g => hR L ϖ σ q n hU hn g
  have h1 : (fun x : GU σ n ⧸ KU σ n => F x.out) = fun _ => 1 := funext fun x => hF _ (hK _)
  rw [h1]
  refine hasSum_single (f := fun _ : GU σ n ⧸ KU σ n => (1 : ℂ)) (QuotientGroup.mk 1) fun b hb => ?_
  exfalso; apply hb
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
  exact QuotientGroup.eq.mpr (hK _)

theorem len_of_mem {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) : len (mat k) = 0 := by
  apply HasLen.len_eq
  apply hasLen_of_isInt
  intro i j
  rw [KU, Subgroup.mem_subgroupOf] at hk
  unfold intPts at hk
  obtain ⟨A, hA⟩ := (Subgroup.mem_inf.mp hk).2
  show (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intL L
  rw [← hA]
  exact ((A : Matrix (Fin n) (Fin n) (intL L)) i j).2

private lemma ordL_one_twisted_operators : ordL (1 : L) = 0 := by
  have h : Valued.v (1 : L) ≠ 0 := by simp
  have hu : WithZero.unzero h = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  unfold ordL
  rw [dif_neg h, hu]
  simp

private lemma chiDeltaU_one' {n m : ℕ} (α : Fin m → ℂ) : chiDeltaU (σ := σ) (n := n) q α 1 = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · simp [ordL_one_twisted_operators]
  · rfl

private lemma isBorelU_one' {n : ℕ} : IsBorelU (1 : GU σ n) := by
  intro i j h
  simp [Matrix.one_apply_ne h.ne']

private lemma isSphericalU_apply_mul_of_mem_KU {n m : ℕ} {α : Fin m → ℂ} {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) (g k : GU σ n)
    (hk : k ∈ KU σ n) : φ (g * k) = φ g := by
  have h := hφ 1 g k isBorelU_one' hk
  rwa [one_mul, chiDeltaU_one', one_mul] at h

private lemma exists_mem_KU_out_mk_eq_mul {n : ℕ} (g : GU σ n) :
    ∃ k ∈ KU σ n, (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out = g * k := by
  refine ⟨g⁻¹ * (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out, ?_, (mul_inv_cancel_left _ _).symm⟩
  have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : GU σ n ⧸ KU σ n))
  simpa [_root_.mul_inv_rev] using inv_mem h

theorem hasSum_spherical [CompleteSpace L] (hF : FracExists) (hP : Pointwise) (hC : Count) (hS : SmallCorner)
    (hG : GenFun) (hSu : CosetSurj) (hI : CosetInj) (hL : LeviExists) (hT : SphTrans) (hR : SmallRank) (hSt : Step)
    (hU : IsUnramInv ϖ σ q) (r : ℕ) : ∀ (n : ℕ), 2 * r ≤ n → n ≤ 2 * r + 1 → ∀ (α : Fin r → ℂ) (X y : ℂ)
      (φ : GU σ n → ℂ), (∀ i, α i ≠ 0) → y * q = X * (q : ℂ) ^ n → ‖y‖ < 1 →
      (∀ i, ‖y‖ * ‖α i‖ < 1 ∧ ‖y‖ * ‖α i‖⁻¹ < 1) → IsSphericalU q α φ → φ 1 = 1 →
      HasSum (fun x : GU σ n ⧸ KU σ n => X ^ len (mat x.out) * φ x.out) (zVal q n X y α) := by
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  induction r with
  | zero =>
    intro n hn0 hn1 α X y φ _ hyX hy _ hφ h1
    have hn : n ≤ 1 := by omega
    have hK : ∀ g : GU σ n, g ∈ KU σ n := fun g => hR L ϖ σ q n hU hn g
    have hφk : ∀ g : GU σ n, φ g = 1 := by
      intro g
      have h := isSphericalU_apply_mul_of_mem_KU hφ 1 g (hK g)
      rwa [one_mul, h1] at h
    have hsum := hasSum_small hR hU hn (fun g => X ^ len (mat g) * φ g)
      (fun k hk => by rw [len_of_mem hk, hφk, pow_zero, one_mul])
    convert hsum using 1
    interval_cases n
    · simp [zVal]
    · have hyx : y = X := by
        apply mul_right_cancel₀ hq0
        rw [hyX]; ring
      subst hyx
      have hy1 : (1 : ℂ) - y ≠ 0 := by
        intro h
        have h' : y = 1 := by linear_combination -h
        rw [h'] at hy; simp at hy
      simp [zVal, hy1]
  | succ r ih =>
    intro n hn0 hn1 α X y φ hα hyX hy hαy hφ h1
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
    obtain ⟨φ₀, hφ₀, hφ₀1, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q N r hU (by omega) (by omega)
      (Fin.tail α) (fun i => hα _)
    have hZ := ih N (by omega) (by omega) (Fin.tail α) ((q : ℂ) ^ 2 * X) y φ₀ (fun i => hα _)
      (by rw [hyX]; ring) hy (fun i => hαy _) hφ₀ hφ₀1
    have hy' : y = (q : ℂ) ^ (N + 1) * X := by
      apply mul_right_cancel₀ hq0
      rw [hyX]; ring
    choose m hm using fun (a : ℤ) (b : GU σ N ⧸ KU σ N) => hL L ϖ σ q N hU a b.out
    have hstep := hSt (GU σ N ⧸ KU σ N) (RadQuot σ N) q N
      (fun a b c => len (mat (m a b * (c.out : radQ σ N).1))) (fun b => len (mat b.out)) (fun b => φ₀ b.out)
      (α 0) X y (zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α))
      (by omega) (hα 0) hy' hy (hαy 0).1 (hαy 0).2
      (fun X' hX' a b => constTerm hF hP hC hS hG hU (hm a b) X' hX') hZ
    rw [zVal_succ, ← (Equiv.ofBijective _ (bijective_cells hSu hI hU m hm)).hasSum_iff]
    convert hstep using 1
    funext p
    obtain ⟨⟨a, b⟩, c⟩ := p
    simp only [Function.comp_apply, Equiv.ofBijective_apply]
    obtain ⟨k, hk, hout⟩ := exists_mem_KU_out_mk_eq_mul (m a b * (c.out : radQ σ N).1)
    have hlen := len_mat_mul (KU σ (N + 2)).one_mem hk (m a b * (c.out : radQ σ N).1)
    rw [one_mul] at hlen
    rw [hout, isSphericalU_apply_mul_of_mem_KU hφ _ _ hk, hlen,
      hT L ϖ σ q N r hU (by omega) α φ φ₀ hα hφ h1 hφ₀ hφ₀1 a b.out (m a b) (hm a b) _ (c.out : radQ σ N).2]

end GlobalTheory.InertZeta

end
