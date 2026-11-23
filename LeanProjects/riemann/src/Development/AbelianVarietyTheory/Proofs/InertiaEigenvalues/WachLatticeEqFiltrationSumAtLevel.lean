import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachImageDeRhamPlusComponentLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesEvaluation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibilityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeGradedOfLevelLe

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.LatFil

section Abstract

variable {LL M R K : Type} [Field LL] [AddCommGroup M] [Module LL M] [CommRing R] [Ring K] [Module K R]

theorem conv_eq_sum (e : PowerSeries LL) (f : ℤ → M) (a : ℕ) (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (q : ℕ) :
    conv e f ((q : ℤ) - a) =
      ∑ j ∈ Finset.range (q + 1), PowerSeries.coeff j e • f (((q - j : ℕ) : ℤ) - a) := by
  unfold conv
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (q + 1))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have : j ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    congr 2
    push_cast [this]
    ring
  · intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    apply hj
    simp only
    rw [hf _ (by omega), smul_zero]

theorem conv_vanish (e : PowerSeries LL) (f : ℤ → M) (a : ℤ) (hf : ∀ r : ℤ, r < a → f r = 0) :
    ∀ r : ℤ, r < a → conv e f r = 0 := by
  intro r hr
  unfold conv
  exact finsum_eq_zero_of_forall_eq_zero fun j => by rw [hf _ (by omega), smul_zero]

theorem conv_mem (D : Submodule LL M) (e : PowerSeries LL) (f : ℤ → M) (hf : ∀ r, f r ∈ D) (k : ℤ) :
    conv e f k ∈ D := by
  unfold conv
  exact finsum_induction (fun x => x ∈ D) D.zero_mem (fun _ _ => D.add_mem) fun j => D.smul_mem _ (hf _)

theorem conv_X_mul (e : PowerSeries LL) (f : ℤ → M) (a : ℕ) (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (k : ℤ) :
    conv (PowerSeries.X * e) f (k + 1) = conv e f k := by
  by_cases hk : k < -(a : ℤ)
  · rw [conv_vanish e f _ hf k hk]
    by_cases hk' : k + 1 < -(a : ℤ)
    · exact conv_vanish _ f _ hf _ hk'
    · have : k + 1 = ((0 : ℕ) : ℤ) - a := by omega
      rw [this, conv_eq_sum _ f a hf]
      simp
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, k = (q : ℤ) - a := ⟨(k + a).toNat, by omega⟩
    have : k + 1 = ((q + 1 : ℕ) : ℤ) - a := by omega
    rw [this, hq, conv_eq_sum _ f a hf, conv_eq_sum _ f a hf, Finset.sum_range_succ']
    simp [PowerSeries.coeff_succ_X_mul]

theorem conv_X_pow_mul (m : ℕ) (e : PowerSeries LL) (f : ℤ → M) (a : ℕ)
    (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (k : ℤ) :
    conv (PowerSeries.X ^ m * e) f (k + m) = conv e f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, Nat.cast_succ, ← add_assoc, conv_X_mul _ f a hf, ih]

variable (Fil : ℤ → Submodule K R) (t : R) (p : M →+ R)

def Rep (a : ℕ) (f : ℤ → M) (y : R) : Prop :=
  ∃ c : ℤ, ∀ N : ℕ, y - ∑ r ∈ Finset.range N, t ^ r * p (f ((r : ℤ) - a)) ∈ Fil ((N : ℤ) - c)

variable {Fil t p}

theorem Rep.unique (anti : Antitone Fil) (sep : ∀ b, (∀ a, b ∈ Fil a) → b = 0) {a : ℕ} {f : ℤ → M} {y y' : R}
    (h : Rep Fil t p a f y) (h' : Rep Fil t p a f y') : y = y' := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine sub_eq_zero.1 (sep _ fun n => ?_)
  let N : ℕ := (n + c).toNat + (n + c').toNat
  have h1 := anti (show n ≤ (N : ℤ) - c by omega) (hc N)
  have h2 := anti (show n ≤ (N : ℤ) - c' by omega) (hc' N)
  simpa using sub_mem h1 h2

theorem Rep.add (anti : Antitone Fil) {a : ℕ} {f f' : ℤ → M} {y y' : R}
    (h : Rep Fil t p a f y) (h' : Rep Fil t p a f' y') : Rep Fil t p a (f + f') (y + y') := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨max c c', fun N => ?_⟩
  have h1 := anti (show (N : ℤ) - max c c' ≤ (N : ℤ) - c by omega) (hc N)
  have h2 := anti (show (N : ℤ) - max c c' ≤ (N : ℤ) - c' by omega) (hc' N)
  convert add_mem h1 h2 using 1
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  ring

theorem Rep.sum (anti : Antitone Fil) {a : ℕ} {J : Type} (S : Finset J) {f : J → ℤ → M} {y : J → R}
    (h : ∀ j, Rep Fil t p a (f j) (y j)) : Rep Fil t p a (∑ j ∈ S, f j) (∑ j ∈ S, y j) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun N => by simp⟩
  | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj]; exact (h j).add anti ih

theorem pow_mul_mem_iff (ht : ∀ a b, t * b ∈ Fil (a + 1) ↔ b ∈ Fil a) (q : ℕ) (a : ℤ) (b : R) :
    t ^ q * b ∈ Fil (a + q) ↔ b ∈ Fil a := by
  induction q with
  | zero => simp
  | succ q ih => rw [pow_succ', mul_assoc, Nat.cast_succ, ← add_assoc, ht, ih]

theorem Rep.single (anti : Antitone Fil) (exh : ∀ b, ∃ a, b ∈ Fil a)
    (ht : ∀ a b, t * b ∈ Fil (a + 1) ↔ b ∈ Fil a) (a q : ℕ) (d : M) :
    Rep Fil t p a (Pi.single ((q : ℤ) - a) d) (t ^ q * p d) := by
  obtain ⟨e, he⟩ := exh (p d)
  refine ⟨-e, fun N => ?_⟩
  have key : ∀ r : ℕ, t ^ r * p ((Pi.single ((q : ℤ) - a) d : ℤ → M) ((r : ℤ) - a)) =
      if r = q then t ^ q * p d else 0 := by
    intro r
    split_ifs with hr
    · subst hr; simp
    · rw [Pi.single_eq_of_ne (by omega)]; simp
  simp only [key, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hq
  · simp
  · rw [sub_zero]
    exact anti (by omega) ((pow_mul_mem_iff ht q e _).2 he)

theorem Rep.conv (anti : Antitone Fil) (exh : ∀ b, ∃ a, b ∈ Fil a)
    (mul : ∀ a b x y, x ∈ Fil a → y ∈ Fil b → x * y ∈ Fil (a + b))
    (ht : ∀ a b, t * b ∈ Fil (a + 1) ↔ b ∈ Fil a) (ι : LL → R) (hι : ∀ c, ι c ∈ Fil 0)
    (hp : ∀ c d, p (c • d) = ι c * p d) {e : PowerSeries LL} {ε : R}
    (he : ∀ N : ℕ, ε - ∑ k ∈ Finset.range N, ι (PowerSeries.coeff k e) * t ^ k ∈ Fil (N : ℤ))
    {a : ℕ} {f : ℤ → M} {y : R} (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0)
    (h : Rep Fil t p a f y) : Rep Fil t p a (GlobalTheory.NL.conv e f) (ε * y) := by
  obtain ⟨c, hc⟩ := h
  have hy : y ∈ Fil (-c) := by simpa using hc 0
  refine ⟨c, fun N => ?_⟩
  have h1 := mul _ _ _ _ (he N) hy
  have h2 : ∑ k ∈ Finset.range N, ι (PowerSeries.coeff k e) * (t ^ k *
      (y - ∑ r ∈ Finset.range (N - k), t ^ r * p (f ((r : ℤ) - a)))) ∈ Fil ((N : ℤ) - c) := by
    refine sum_mem fun k hk => ?_
    have hk' : k ≤ N := (Finset.mem_range.1 hk).le
    have := mul _ _ _ _ (hι (PowerSeries.coeff k e)) ((pow_mul_mem_iff ht k _ _).2 (hc (N - k)))
    refine anti (le_of_eq ?_) this
    push_cast [hk']
    ring
  have h3 : ∑ r ∈ Finset.range N, t ^ r * p (GlobalTheory.NL.conv e f ((r : ℤ) - a)) =
      ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range (N - k),
        ι (PowerSeries.coeff k e) * (t ^ k * (t ^ r * p (f ((r : ℤ) - a)))) := by
    rw [← Finset.sum_range_diag_flip]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [conv_eq_sum e f a hf, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [hp, ← mul_assoc (t ^ j), ← pow_add, Nat.add_sub_cancel' this]
    ring
  rw [← sub_eq_add_neg] at h1
  convert add_mem h1 h2 using 1
  rw [h3]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  ring

end Abstract

section Core

variable {LL M R K N : Type} [Field LL] [AddCommGroup M] [Module LL M] [CommRing R] [Ring K] [Module K R]

theorem conv_one (f : ℤ → M) : conv (1 : PowerSeries LL) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem single_mem_iff {Fil : ℤ → Submodule K R} {t : R} (anti : Antitone Fil) (exh : ∀ b, ∃ a, b ∈ Fil a)
    (sep : ∀ b, (∀ a, b ∈ Fil a) → b = 0)
    (mul : ∀ a b x y, x ∈ Fil a → y ∈ Fil b → x * y ∈ Fil (a + b))
    (ht : ∀ a b, t * b ∈ Fil (a + 1) ↔ b ∈ Fil a) (htu : IsUnit t) (ι : LL → R) (hι : ∀ c, ι c ∈ Fil 0)
    (ev : PowerSeries LL →+* R)
    (hev : ∀ (e : PowerSeries LL) (N : ℕ),
      ev e - ∑ k ∈ Finset.range N, ι (PowerSeries.coeff k e) * t ^ k ∈ Fil (N : ℤ))
    (hdiv : ∀ (e : PowerSeries LL) (N : ℕ), ev e ∈ Fil (N : ℤ) ↔ PowerSeries.X ^ N ∣ e)
    {n r : ℕ} (hr : r ≤ n) (p : Fin n → M →+ R) (hp : ∀ α c d, p α (c • d) = ι c * p α d)
    (ex : N → ℤ → M) (ψ : N → Fin n → R) (hψ : ∀ x α, ψ x α ∈ Fil 0)
    (hspan : ∀ z : Fin n → R, (∀ α, z α ∈ Fil 0) → ∃ (m : ℕ) (b : Fin m → R) (x : Fin m → N),
      (∀ j, b j ∈ Fil 0) ∧ ∀ α, z α = ∑ j, b j * ψ (x j) α)
    (hrep : ∀ (x : N) (a : ℕ), (∀ r : ℤ, r < -(a : ℤ) → ex x r = 0) →
      ∀ α, Rep Fil t (p α) a (ex x) (t ^ a * ψ x α))
    (nb : Fin r → N) (hsupp : ∀ x, ∃ m : ℤ, ∀ k < m, ex x k = 0) (Λ : Submodule LL (ℤ → M))
    (hΛ : ∀ f, f ∈ Λ ↔ ∃ e : Fin r → PowerSeries LL, f = ∑ j, conv (e j) (ex (nb j)))
    (hex : ∀ x, ex x ∈ Λ) (d : M) (m₀ : ℕ) (hfull : ∀ k : ℤ, (m₀ : ℤ) ≤ k → Pi.single k d ∈ Λ) (k : ℤ) :
    Pi.single k d ∈ Λ ↔ ∀ α, p α d ∈ Fil (-k) := by
  have hev0 : ∀ e, ev e ∈ Fil 0 := fun e => by simpa using (hdiv e 0).2 (by simp)
  haveI : Nontrivial R := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    have h1 : ev 1 ∈ Fil ((1 : ℕ) : ℤ) := by rw [Subsingleton.elim (ev 1) 0]; exact zero_mem _
    have := (hdiv 1 1).1 h1
    rw [pow_one, PowerSeries.X_dvd_iff] at this
    simp at this
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℕ, ∀ j, ∀ r : ℤ, r < -(a₀ : ℤ) → ex (nb j) r = 0 := by
    choose m hm using hsupp
    refine ⟨∑ j, (-m (nb j)).toNat, fun j r hr => hm _ _ ?_⟩
    have := Finset.single_le_sum (f := fun j => (-m (nb j)).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have key : ∀ (e : Fin r → PowerSeries LL) (a : ℕ), a₀ ≤ a → ∀ α,
      Rep Fil t (p α) a (∑ j, conv (e j) (ex (nb j))) (t ^ a * ∑ j, ev (e j) * ψ (nb j) α) := by
    intro e a ha α
    have hv : ∀ j, ∀ r : ℤ, r < -(a : ℤ) → ex (nb j) r = 0 := fun j r hr => ha₀ j r (by omega)
    have := Rep.sum anti Finset.univ fun j =>
      Rep.conv anti exh mul ht ι hι (hp α) (hev (e j)) (hv j) (hrep (nb j) a (hv j) α)
    convert this using 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hA : ∀ x, ∃ e : Fin r → PowerSeries LL, ∀ α, ψ x α = ∑ j, ev (e j) * ψ (nb j) α := by
    intro x
    obtain ⟨e, he⟩ := (hΛ _).1 (hex x)
    refine ⟨e, fun α => ?_⟩
    have hv : ∀ r : ℤ, r < -(a₀ : ℤ) → ex x r = 0 := fun r hr => by
      rw [he, Finset.sum_apply]
      exact Finset.sum_eq_zero fun j _ => conv_vanish _ _ _ (ha₀ j) r hr
    have h1 := hrep x a₀ hv α
    rw [he] at h1
    exact (htu.pow a₀).mul_left_cancel (h1.unique anti sep (key e a₀ le_rfl α))
  have hspan' : ∀ z : Fin n → R, (∀ α, z α ∈ Fil 0) → ∃ b : Fin r → R,
      (∀ j, b j ∈ Fil 0) ∧ ∀ α, z α = ∑ j, b j * ψ (nb j) α := by
    intro z hz
    obtain ⟨m, b, x, hb, hx⟩ := hspan z hz
    choose e he using hA
    refine ⟨fun j => ∑ u, b u * ev (e (x u) j), fun j => sum_mem fun u _ => ?_, fun α => ?_⟩
    · simpa using mul _ _ _ _ (hb u) (hev0 _)
    · rw [hx α]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [he (x u) α, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hB : ∀ (e : Fin r → PowerSeries LL) (a q : ℕ), a₀ ≤ a →
      Pi.single ((q : ℤ) - a) d = ∑ j, conv (e j) (ex (nb j)) →
      ∀ α, t ^ q * p α d = t ^ a * ∑ j, ev (e j) * ψ (nb j) α := by
    intro e a q ha he α
    have h1 := Rep.single (p := p α) anti exh ht a q d
    rw [he] at h1
    exact h1.unique anti sep (key e a ha α)
  have hli : LinearIndependent R fun j => ψ (nb j) := by
    refine linearIndependent_of_top_le_span_of_card_le_finrank (fun z _ => ?_) (by simpa using hr)
    choose c hc using fun α => exh (z α)
    let q : ℕ := ∑ α, (-c α).toNat
    have hq : ∀ α, t ^ q * z α ∈ Fil 0 := fun α => by
      have := Finset.single_le_sum (f := fun α => (-c α).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ α)
      exact anti (by omega) ((pow_mul_mem_iff ht q _ _).2 (hc α))
    obtain ⟨b, -, hb⟩ := hspan' _ hq
    obtain ⟨u, hu⟩ := (htu.pow q).exists_left_inv
    have : z = ∑ j, (u * b j) • ψ (nb j) := by
      funext α
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, ← hb α]
      rw [← mul_assoc, hu, one_mul]
    rw [this]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨a, q, ha, rfl⟩ : ∃ a q : ℕ, a₀ ≤ a ∧ k = (q : ℤ) - a :=
    ⟨a₀ + (-k).toNat, (k + (a₀ + (-k).toNat : ℕ)).toNat, by omega, by omega⟩
  constructor
  · intro hk α
    obtain ⟨e, he⟩ := (hΛ _).1 hk
    have h1 : ∑ j, ev (e j) * ψ (nb j) α ∈ Fil 0 :=
      sum_mem fun j _ => by simpa using mul _ _ _ _ (hev0 _) (hψ _ α)
    have h2 := (pow_mul_mem_iff ht a _ _).2 h1
    rw [← hB e a q ha he α] at h2
    refine (pow_mul_mem_iff ht q _ _).1 ?_
    convert h2 using 2
    ring
  · intro hd
    obtain ⟨u, hu⟩ := (htu.pow a).exists_right_inv
    have hz : ∀ α, u * (t ^ q * p α d) ∈ Fil 0 := fun α => by
      refine (pow_mul_mem_iff ht a _ _).1 ?_
      rw [← mul_assoc, hu, one_mul]
      convert (pow_mul_mem_iff ht q _ _).2 (hd α) using 2
      ring
    obtain ⟨b, hb0, hb⟩ := hspan' _ hz
    let m : ℕ := m₀ + a
    obtain ⟨e, he⟩ := (hΛ _).1 (hfull (((q + m : ℕ) : ℤ) - a) (by omega))
    have h1 := hB e a (q + m) ha he
    have h2 : ∀ j, ev (e j) = t ^ m * b j := by
      have := Fintype.linearIndependent_iff.1 hli (fun j => ev (e j) - t ^ m * b j) (by
        funext α
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib, mul_assoc,
          ← Finset.mul_sum, ← hb α, Pi.zero_apply]
        refine (htu.pow a).mul_left_cancel ?_
        rw [mul_sub, ← h1 α]
        linear_combination (-(t ^ m * t ^ q * p α d)) * hu)
      exact fun j => sub_eq_zero.1 (this j)
    have h3 : ∀ j, ∃ e', e j = PowerSeries.X ^ m * e' := fun j => (hdiv _ m).1 (by
      rw [h2 j]
      simpa using (pow_mul_mem_iff ht m _ _).2 (hb0 j))
    choose e' he' using h3
    refine (hΛ _).2 ⟨e', funext fun r => ?_⟩
    have h4 := congrFun he (r + m)
    rw [Finset.sum_apply] at h4 ⊢
    simp only [he', conv_X_pow_mul m _ _ a₀ (ha₀ _)] at h4
    rw [← h4]
    by_cases hr : r = (q : ℤ) - a
    · have : r + m = ((q + m : ℕ) : ℤ) - a := by omega
      rw [this, hr]
      simp
    · rw [Pi.single_eq_of_ne hr, Pi.single_eq_of_ne (by omega)]

end Core

section Coord

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR)

def crd (lam : T.V →ₗ[LL] LL) : T.V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  LinearMap.mul' Qp BdR ∘ₗ TensorProduct.map (ι.toLinearMap ∘ₗ lam.restrictScalars Qp) LinearMap.id

theorem crd_tmul (lam : T.V →ₗ[LL] LL) (x : T.V) (b : BdR) : crd T ι lam (x ⊗ₜ b) = ι (lam x) * b := by
  simp [crd]

theorem mulVR_tmul (c : BdR) (x : T.V) (b : BdR) : mulVR T c (x ⊗ₜ[Qp] b) = x ⊗ₜ (c * b) := by
  simp [mulVR]

theorem crd_smul (lam : T.V →ₗ[LL] LL) (c : LL) (z : T.V ⊗[Qp] BdR) :
    crd T ι lam (c • z) = ι c * crd T ι lam z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => rw [TensorProduct.smul_tmul', crd_tmul, crd_tmul, map_smul, smul_eq_mul, map_mul, mul_assoc]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

theorem crd_mulVR (lam : T.V →ₗ[LL] LL) (c : BdR) (z : T.V ⊗[Qp] BdR) :
    crd T ι lam (mulVR T c z) = c * crd T ι lam z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => rw [mulVR_tmul, crd_tmul, crd_tmul]; ring
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, mul_add]

theorem crd_compKer (lam : T.V →ₗ[LL] LL) {z : T.V ⊗[Qp] BdR} (hz : z ∈ compKer T ι) : crd T ι lam z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, y, rfl⟩ := hz
    rw [map_sub, crd_smul, crd_mulVR, sub_self]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [crd_smul, hx, mul_zero]

theorem crd_filV (hι : ∀ c, ι c ∈ PD.Fil 0) (lam : T.V →ₗ[LL] LL) (a : ℤ) {z : T.V ⊗[Qp] BdR}
    (hz : z ∈ FilV PD (LL := LL) (V := T.V) a) : crd T ι lam z ∈ PD.Fil a := by
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    simp only [AlgebraTensorModule.map_tmul, crd_tmul]
    simpa using PD.Fil_mul _ _ _ _ (hι _) b.2
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

theorem crd_sup (hι : ∀ c, ι c ∈ PD.Fil 0) (lam : T.V →ₗ[LL] LL) (a : ℤ) {z : T.V ⊗[Qp] BdR}
    (hz : z ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) a) : crd T ι lam z ∈ PD.Fil a := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hz
  rw [map_add, crd_compKer T ι lam hx, zero_add]
  exact crd_filV PD T ι hι lam a hy

variable {n : ℕ} (bV : Module.Basis (Fin n) LL T.V)

theorem sum_tmul_mem_filV (a : ℤ) (y : Fin n → BdR) (hy : ∀ α, y α ∈ PD.Fil a) :
    ∑ α, bV α ⊗ₜ[Qp] y α ∈ FilV PD (LL := LL) (V := T.V) a :=
  sum_mem fun α _ => ⟨bV α ⊗ₜ ⟨y α, hy α⟩, rfl⟩

theorem crd_sum_tmul (y : Fin n → BdR) (α : Fin n) :
    crd T ι (bV.coord α) (∑ β, bV β ⊗ₜ[Qp] y β) = y α := by
  rw [map_sum, Finset.sum_eq_single α]
  · simp [crd_tmul]
  · intro β _ hβ
    simp [crd_tmul, hβ]
  · simp

theorem sub_sum_mem_compKer (z : T.V ⊗[Qp] BdR) :
    z - ∑ α, bV α ⊗ₜ[Qp] crd T ι (bV.coord α) z ∈ compKer T ι := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    have : x ⊗ₜ[Qp] b = ∑ α, bV.repr x α • (bV α ⊗ₜ[Qp] b) := by
      conv_lhs => rw [← bV.sum_repr x, TensorProduct.sum_tmul]
      rfl
    nth_rewrite 1 [this]
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun α _ => Submodule.subset_span ⟨bV.repr x α, bV α ⊗ₜ b, ?_⟩
    rw [mulVR_tmul, crd_tmul]
    rfl
  | add x y hx hy =>
    convert add_mem hx hy using 1
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    abel

theorem mem_sup_iff (hι : ∀ c, ι c ∈ PD.Fil 0) (a : ℤ) (z : T.V ⊗[Qp] BdR) :
    z ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) a ↔ ∀ α, crd T ι (bV.coord α) z ∈ PD.Fil a :=
  ⟨fun hz _ => crd_sup PD T ι hι _ a hz, fun hz => Submodule.mem_sup.2
    ⟨_, sub_sum_mem_compKer T ι bV z, _, sum_tmul_mem_filV PD T bV a _ hz, sub_add_cancel _ _⟩⟩

theorem finrank_le [IsFractionRing O LL] [Nontrivial O] :
    Module.finrank O ↥T.L.T ≤ Module.finrank LL T.V := by
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  let b := Module.finBasis O ↥T.L.T
  have h1 : LinearIndependent O (fun j => (b j : T.V)) :=
    b.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have h2 := (LinearIndependent.iff_fractionRing O LL).1 h1
  simpa using h2.fintype_card_le_finrank

end Coord

set_option maxHeartbeats 1600000 in

theorem lat_eq_fil : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let _W := (HW l).W K s LL h; let _E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ f : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B, f ∈ Lat C h T i ζ ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k : ℤ, f k ∈ Di (HW l) h T i ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (f k) ∈ FilAt ((D.loc l).PD K) T τ (-k) := by
  intro D HW F Cm l _ K s LL h W E C T hT i ζ τ hpt f
  obtain ⟨hprim, hτ, ι, hcomp⟩ := (@GlobalTheory.NL.Points.points D HW l _ K s LL h).2.1 i ζ τ hpt
  have hfull := GlobalTheory.T.wach_expansions_span_full_lattice D HW F Cm l K s LL h T hT i ζ hprim
  have hgr := @GlobalTheory.NL.GradedLat.graded_of_level_le D HW F Cm l _ K s LL h T hT i ζ hprim.pow_eq_one hfull
  obtain ⟨nb⟩ := @GlobalTheory.NL.N_basis D HW F l _ K s LL h T hT
  have hgen := ((GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i ζ ⟨s, hprim⟩ hfull).2 _ nb).2.1
  obtain ⟨ev, hev, hdiv, htu, ht, sep⟩ := @GlobalTheory.NL.EvdR.exists_ev_dR D l _ K LL s ι
  obtain ⟨Ψ, hΨ0, hΨs, hΨr⟩ := GlobalTheory.T.wach_image_deRham_plus_component_level D HW F Cm l K s LL h T hT i ζ τ ι hcomp
  have hfil := (GlobalTheory.T.deRhamComponent_wachLetter_basis_filtration D HW l K s LL h T hT i ζ τ ι hcomp hτ).2.1
  have anti : Antitone ((D.loc l).PD K).Fil := antitone_int_of_succ_le ((D.loc l).PD K).Fil_anti
  have hι : ∀ c, ι c ∈ ((D.loc l).PD K).Fil 0 := fun c => by
    have h1 := anti (show (0 : ℤ) ≤ ((1 : ℕ) : ℤ) by simp) (hev (PowerSeries.C c) 1)
    have h2 := (hdiv (PowerSeries.C c) 0).2 (by simp)
    simpa using sub_mem h2 h1
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  let bV := Module.finBasis ↥LL.1 T.V
  have hΛ : ∀ g, g ∈ Lat (Cm l) h T i ζ ↔
      ∃ e : Fin _ → PowerSeries ↥LL.1, g = ∑ j, conv (e j) (ex (Cm l) h T i ζ (nb j)) := fun g =>
    ⟨hgen g, fun ⟨e, he⟩ => he ▸ sum_mem fun j _ => Submodule.subset_span ⟨e j, nb j, rfl⟩⟩
  have hD : ∀ g ∈ Lat (Cm l) h T i ζ, ∀ k, g k ∈ Di (HW l) h T i := fun g hg k => by
    obtain ⟨e, rfl⟩ := (hΛ g).1 hg
    rw [Finset.sum_apply]
    exact sum_mem fun j _ => conv_mem _ _ _ (fun r => ((Cm l).C K s LL h).tie.levB_mem T i ζ _ r) k
  obtain ⟨m₀, hm₀⟩ := hfull
  have main : ∀ d ∈ Di (HW l) h T i, ∀ k : ℤ, Pi.single k d ∈ Lat (Cm l) h T i ζ ↔
      ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ (-k) := by
    intro d hd k
    rw [hfil d hd, mem_sup_iff _ T ι bV hι]
    refine single_mem_iff anti ((D.loc l).PD K).Fil_exh sep ((D.loc l).PD K).Fil_mul ht htu ι hι ev hev hdiv
      (finrank_le T)
      (fun α => (crd T ι (bV.coord α)).toAddMonoidHom.comp
        (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)).toAddMonoidHom)
      (fun α c d => ?_) (ex (Cm l) h T i ζ) (fun x α => crd T ι (bV.coord α) (Ψ x))
      (fun x α => crd_filV _ T ι hι _ _ (hΨ0 x)) (fun z hz => ?_) (fun x a ha α => ?_) nb
      (fun x => ((Cm l).C K s LL h).tie.levB_supp T i ζ x) _ hΛ
      (fun x => Submodule.subset_span ⟨1, x, (conv_one _).symm⟩) d m₀ (fun k hk => hm₀ _ (fun r => ?_) fun r hr => ?_) k
    · simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, map_smul, crd_smul]
    · obtain ⟨m, b, x, hb, hx⟩ := hΨs _ (sum_tmul_mem_filV _ T bV 0 z hz)
      refine ⟨m, b, x, hb, fun α => ?_⟩
      have := crd_compKer T ι (bV.coord α) hx
      rw [map_sub, crd_sum_tmul, map_sum, sub_eq_zero] at this
      simpa only [crd_mulVR] using this
    · obtain ⟨c, hc⟩ := hΨr x a ha
      refine ⟨c, fun M => ?_⟩
      have := crd_sup _ T ι hι (bV.coord α) _ (hc M)
      rw [map_sub, map_sum] at this
      simp only [crd_mulVR] at this
      exact this
    · by_cases hr : r = k
      · rw [hr, Pi.single_eq_same]; exact hd
      · rw [Pi.single_eq_of_ne hr]; exact zero_mem _
    · exact Pi.single_eq_of_ne (by omega) _
  rw [hgr f]
  refine and_congr_right fun _ => forall_congr' fun k => ⟨fun hk => ?_, fun hk => (main _ hk.1 k).2 hk.2⟩
  have hd : f k ∈ Di (HW l) h T i := by simpa using hD _ hk k
  exact ⟨hd, (main _ hd k).1 hk⟩

end GlobalTheory.NL.LatFil
