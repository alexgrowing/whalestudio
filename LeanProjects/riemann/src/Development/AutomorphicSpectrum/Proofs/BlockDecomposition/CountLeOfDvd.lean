import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf

noncomputable section

open Polynomial

namespace GlobalTheory.CompanionTheory.GapPolyProof

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def dd (n : ℕ) (v : ℕ → E) (ψ : E →ₗ[ℂ] ℂ) : ℂ[X] :=
  ∑ j ∈ Finset.range (n + 1), C (ψ (v j)) * X ^ (n - j)

lemma dd_add (n : ℕ) (v : ℕ → E) (ψ ψ' : E →ₗ[ℂ] ℂ) : dd n v (ψ + ψ') = dd n v ψ + dd n v ψ' := by
  simp [dd, add_mul, Finset.sum_add_distrib]

lemma dd_smul (n : ℕ) (v : ℕ → E) (a : ℂ) (ψ : E →ₗ[ℂ] ℂ) : dd n v (a • ψ) = C a * dd n v ψ := by
  simp [dd, Finset.mul_sum, mul_assoc]

lemma dd_zero (n : ℕ) (v : ℕ → E) : dd n v (0 : E →ₗ[ℂ] ℂ) = 0 := by
  simp [dd]

lemma dd_step (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1) (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x) (ψ : E →ₗ[ℂ] ℂ) :
    X * dd n v ψ - dd n v (ψ ∘ₗ T) = C (ψ x) * (S.map (fun t => X - C t)).prod := by
  have key : X * dd n v ψ = (∑ j ∈ Finset.range (n + 1), C (ψ (v (j + 1))) * X ^ (n - j)) + C (ψ x) * X ^ (n + 1) := by
    have h1 := Finset.sum_range_succ (fun j => (C (ψ (v j)) : ℂ[X]) * X ^ (n + 1 - j)) (n + 1)
    have h2 := Finset.sum_range_succ' (fun j => (C (ψ (v j)) : ℂ[X]) * X ^ (n + 1 - j)) (n + 1)
    rw [h1] at h2
    simp only [hn, map_zero, zero_mul, add_zero, h0, Nat.sub_zero, Nat.add_sub_add_right] at h2
    rw [← h2, dd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : n + 1 - j = (n - j) + 1 := by have := Finset.mem_range.1 hj; omega
    rw [this, pow_succ]; ring
  have hG : (S.map (fun t => X - C t)).prod =
      (∑ j ∈ Finset.range (n + 1), C (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) * X ^ (n - j)) + X ^ (n + 1) := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hS, Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Nat.add_sub_add_right, map_mul, map_pow, map_neg, map_one]
      ring
    · simp [Multiset.esymm]
  rw [key, hG, dd, mul_add, Finset.mul_sum, add_sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have h := congrArg ψ (hrec j (by have := Finset.mem_range.1 hj; omega))
  simp only [map_sub, map_smul, smul_eq_mul] at h
  have h' : ψ (v (j + 1)) = ψ (T (v j)) + (-1 : ℂ) ^ (j + 1) * S.esymm (j + 1) * ψ x := by
    rw [← h]; ring
  rw [h']
  simp only [LinearMap.comp_apply, map_add, map_mul]
  ring

lemma dd_pow (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1) (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x) (k : ℕ) :
    ∀ ψ : E →ₗ[ℂ] ℂ, (S.map (fun t => X - C t)).prod ∣ X ^ k * dd n v ψ - dd n v (ψ ∘ₗ (T ^ k)) := by
  induction k with
  | zero => intro ψ; simp [Module.End.one_eq_id]
  | succ k ih =>
    intro ψ
    have e : ψ ∘ₗ (T ^ (k + 1)) = (ψ ∘ₗ (T ^ k)) ∘ₗ T := by
      rw [pow_succ]; rfl
    have : X ^ (k + 1) * dd n v ψ - dd n v (ψ ∘ₗ (T ^ (k + 1))) =
        X * (X ^ k * dd n v ψ - dd n v (ψ ∘ₗ (T ^ k))) +
          (X * dd n v (ψ ∘ₗ (T ^ k)) - dd n v ((ψ ∘ₗ (T ^ k)) ∘ₗ T)) := by
      rw [e]; ring
    rw [this, dd_step S n hS T v x h0 hn hrec]
    exact dvd_add (Dvd.dvd.mul_left (ih ψ) _) (Dvd.intro_left _ rfl)

lemma dd_aeval (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1) (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x) (p : ℂ[X])
    (ψ : E →ₗ[ℂ] ℂ) :
    (S.map (fun t => X - C t)).prod ∣ p * dd n v ψ - dd n v (ψ ∘ₗ (aeval T p)) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    have : (p + r) * dd n v ψ - dd n v (ψ ∘ₗ (aeval T (p + r))) =
        (p * dd n v ψ - dd n v (ψ ∘ₗ (aeval T p))) + (r * dd n v ψ - dd n v (ψ ∘ₗ (aeval T r))) := by
      rw [map_add, LinearMap.comp_add, dd_add]; ring
    rw [this]; exact dvd_add hp hr
  | monomial k a =>
    have e : ψ ∘ₗ (aeval T (monomial k a)) = a • (ψ ∘ₗ (T ^ k)) := by
      rw [aeval_monomial]
      ext y
      simp [Algebra.algebraMap_eq_smul_one]
    have : monomial k a * dd n v ψ - dd n v (ψ ∘ₗ (aeval T (monomial k a))) =
        C a * (X ^ k * dd n v ψ - dd n v (ψ ∘ₗ (T ^ k))) := by
      rw [e, dd_smul, ← C_mul_X_pow_eq_monomial]; ring
    rw [this]
    exact Dvd.dvd.mul_left (dd_pow S n hS T v x h0 hn hrec k ψ) _

lemma dvd_minpoly_mul [FiniteDimensional ℂ E] (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1)
    (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x)
    (ψ : E →ₗ[ℂ] ℂ) :
    (S.map (fun t => X - C t)).prod ∣ minpoly ℂ T * dd n v ψ := by
  have h := dd_aeval S n hS T v x h0 hn hrec (minpoly ℂ T) ψ
  rwa [minpoly.aeval, LinearMap.comp_zero, dd_zero, sub_zero] at h

lemma pow_dvd_dd [FiniteDimensional ℂ E] (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1)
    (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x)
    (ψ : E →ₗ[ℂ] ℂ) (z : ℂ) (hz : ¬ T.HasEigenvalue z) :
    (X - C z) ^ (S.count z) ∣ dd n v ψ := by
  have hG : (S.map (fun t => X - C t)).prod.roots = S := roots_multiset_prod_X_sub_C S
  have hcount : S.count z = rootMultiplicity z (S.map (fun t => X - C t)).prod := by
    rw [← count_roots, hG]
  have h1 : (X - C z) ^ (S.count z) ∣ (S.map (fun t => X - C t)).prod := by
    rw [hcount]; exact pow_rootMultiplicity_dvd _ _
  have h2 := h1.trans (dvd_minpoly_mul S n hS T v x h0 hn hrec ψ)
  have hcop : IsCoprime (X - C z) (minpoly ℂ T) := by
    rw [(irreducible_X_sub_C z).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact fun h => hz (Module.End.hasEigenvalue_of_isRoot h)
  exact (hcop.pow_left).dvd_of_dvd_mul_left h2

lemma count_le_of_dvd (S : Multiset ℂ) (q c d z : ℂ) (hq : q ≠ 0) (hc : c ≠ 0) (f : ℂ[X])
    (hf : (X - C z) ^ (S.count z) ∣ f)
    (hrel : C d * (X * f) = C c * (((S.map (fun t => X - C t)).prod).comp (C q * X) - (S.map (fun t => X - C t)).prod)) :
    S.count z ≤ S.count (q * z) := by
  set G := (S.map (fun t => X - C t)).prod with hGdef
  have hGroots : G.roots = S := roots_multiset_prod_X_sub_C S
  have hG0 : G ≠ 0 := (monic_multiset_prod_of_monic _ _ (fun t _ => monic_X_sub_C t)).ne_zero
  have hcount : ∀ w, S.count w = rootMultiplicity w G := fun w => by rw [← count_roots, hGroots]
  have h1 : (X - C z) ^ (S.count z) ∣ G := by
    rw [hcount]; exact pow_rootMultiplicity_dvd _ _
  have h2 : (X - C z) ^ (S.count z) ∣ C c * G.comp (C q * X) := by
    have : C c * G.comp (C q * X) = C d * (X * f) + C c * G := by rw [hrel]; ring
    rw [this]
    exact dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left hf _) _) (Dvd.dvd.mul_left h1 _)
  have h3 : (X - C z) ^ (S.count z) ∣ G.comp (C q * X) :=
    ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)).dvd_mul_left).1 h2
  obtain ⟨H, hH⟩ := h3
  have h4 : G = (C q⁻¹ * (X - C (q * z))) ^ (S.count z) * H.comp (C q⁻¹ * X) := by
    have e1 : (G.comp (C q * X)).comp (C q⁻¹ * X) = G := by
      rw [comp_assoc]
      have : (C q * X : ℂ[X]).comp (C q⁻¹ * X) = X := by
        simp only [mul_comp, C_comp, X_comp]
        rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hq, C_1, one_mul]
      rw [this, comp_X]
    have e2 : (X - C z : ℂ[X]).comp (C q⁻¹ * X) = C q⁻¹ * (X - C (q * z)) := by
      simp only [sub_comp, X_comp, C_comp, mul_sub, ← C_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul]
    rw [← e1, hH, mul_comp, pow_comp, e2]
  have h5 : (X - C (q * z)) ^ (S.count z) ∣ G := by
    rw [h4, mul_pow, mul_assoc]
    refine ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hq))).pow _).dvd_mul_left.2 ?_
    exact Dvd.intro _ rfl
  rw [hcount (q * z)]
  exact (le_rootMultiplicity_iff hG0).2 h5

lemma rel_of_pair (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1) (q c d : ℂ) (v : ℕ → E)
    (φ : E →ₗ[ℂ] ℂ)
    (hp : ∀ j ≤ n, d * φ (v j) = (q ^ (n + 1 - j) - 1) * (((-1 : ℂ) ^ j) * S.esymm j) * c) :
    C d * (X * dd n v φ) =
      C c * (((S.map (fun t => X - C t)).prod).comp (C q * X) - (S.map (fun t => X - C t)).prod) := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hS, ← coe_compRingHom_apply, map_sum, ← Finset.sum_sub_distrib,
    Finset.sum_range_succ, dd, Finset.mul_sum, Finset.mul_sum]
  simp only [coe_compRingHom_apply]
  have hlast : ((-1 : ℂ[X]) ^ (n + 1) * (C (S.esymm (n + 1)) * X ^ (n + 1 - (n + 1)))).comp (C q * X) -
      (-1 : ℂ[X]) ^ (n + 1) * (C (S.esymm (n + 1)) * X ^ (n + 1 - (n + 1))) = 0 := by
    simp
  rw [hlast, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := by have := Finset.mem_range.1 hj; omega
  have e : n + 1 - j = (n - j) + 1 := by omega
  have h := congrArg (C : ℂ → ℂ[X]) (hp j hj')
  simp only [map_mul, map_sub, map_pow, map_neg, map_one] at h
  simp only [mul_comp, pow_comp, neg_comp, one_comp, C_comp, X_comp]
  rw [e] at h ⊢
  rw [mul_pow]
  calc C d * (X * (C (φ (v j)) * X ^ (n - j))) = (C d * C (φ (v j))) * X ^ (n - j + 1) := by ring
    _ = _ := by rw [h]; ring

theorem gapPoly : PositivityTheory.Rg.Rs.GapPoly := by
  intro q n hq V _ _ B W U Z S hpos hcard h0S hZ0 hUW hZW hexp hZtop hrec hpair z hz
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)

  obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = (q : ℂ) ^ (((2 : ℕ) : ℂ)⁻¹) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = q := by rw [hsdef]; exact Complex.cpow_nat_inv_pow _ (by norm_num)
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs2; exact hq0 (by simpa using hs2.symm)
  have hsn : ‖s‖ ^ 2 = q := by
    rw [← norm_pow, hs2]; simp
  have hpow : ∀ j ≤ n + 1, (q : ℂ) ^ (((j : ℂ) * (((n + 1 : ℕ) : ℂ) - j)) / 2) = s ^ (j * (n + 1 - j)) := by
    intro j hj
    have : ((j : ℂ) * (((n + 1 : ℕ) : ℂ) - j)) / 2 = ((j * (n + 1 - j) : ℕ) : ℂ) * (((2 : ℕ) : ℂ)⁻¹) := by
      rw [Nat.cast_mul, Nat.cast_sub hj]; push_cast; ring
    rw [this, Complex.cpow_nat_mul, ← hsdef]

  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → ℂ, ∀ j, b j = (-1) ^ j * s ^ (j * (j - 1)) * (s ^ (n * j))⁻¹ := ⟨_, fun _ => rfl⟩
  have hbtop : ∀ j ≤ n + 1, b j * s ^ (j * (n + 1 - j)) = (-1) ^ j := by
    intro j hj
    have e : j * (j - 1) + j * (n + 1 - j) = n * j := by
      obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le hj
      cases j with
      | zero => simp
      | succ j =>
        have : n + 1 - (j + 1) = i := by omega
        have hn' : n = j + i := by omega
        rw [this, hn']; simp only [Nat.add_sub_cancel]; ring
    rw [hbdef, mul_assoc, mul_assoc, mul_comm (s ^ (n * j))⁻¹, ← mul_assoc (s ^ (j * (j - 1))), ← pow_add, e]
    rw [mul_inv_cancel₀ (pow_ne_zero _ hs0), mul_one]
  have hbrec : ∀ j, b (j + 1) = -((s ^ n)⁻¹ * b j * (q : ℂ) ^ j) := by
    intro j
    have e : (j + 1) * (j + 1 - 1) = j * (j - 1) + 2 * j := by
      cases j with
      | zero => simp
      | succ j => simp only [Nat.add_sub_cancel]; ring
    rw [hbdef, hbdef, e, pow_add, ← hs2, ← pow_mul, Nat.mul_succ, pow_add s (n * j) n, mul_inv]
    ring

  obtain ⟨Ee, hEe⟩ : ∃ Ee : Submodule ℂ V, Ee = Submodule.span ℂ (Z '' (Finset.range (n + 1) : Set ℕ)) := ⟨_, rfl⟩
  have : FiniteDimensional ℂ Ee := by
    rw [hEe]; exact FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet _).image _)
  have hEmem : ∀ j ≤ n + 1, Z j ∈ Ee := by
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · rw [hEe]; exact Submodule.subset_span ⟨j, by simpa using h, rfl⟩
    · have : j = n + 1 := by omega
      rw [this, hZtop]; exact Ee.zero_mem
  have hEW : ∀ y ∈ Ee, y ∈ W := by
    intro y hy
    have : Ee ≤ W := by
      rw [hEe, Submodule.span_le]; rintro _ ⟨j, _, rfl⟩; exact hZW j
    exact this hy
  have hEU : ∀ y ∈ Ee, U y ∈ Ee := by
    have : Ee ≤ Ee.comap U := by
      conv_lhs => rw [hEe]
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j ≤ n := by simpa using hj
      show U (Z j) ∈ Ee
      rw [hrec j hj']
      exact Ee.smul_mem _ (Ee.sub_mem (Ee.smul_mem _ (hEmem 0 (by omega))) (hEmem _ (by omega)))
    exact fun y hy => this hy
  obtain ⟨T, hT⟩ : ∃ T : Module.End ℂ Ee, ∀ y : Ee, ((T y : Ee) : V) = (s ^ n)⁻¹ • U y :=
    ⟨(s ^ n)⁻¹ • U.restrict hEU, fun y => rfl⟩
  obtain ⟨Zs, hZs⟩ : ∃ Zs : ℕ → Ee, ∀ j ≤ n + 1, ((Zs j : Ee) : V) = Z j :=
    ⟨fun j => if h : j ≤ n + 1 then ⟨Z j, hEmem j h⟩ else 0, fun j hj => by simp [hj]⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Ee →ₗ[ℂ] ℂ, ∀ y : Ee, φ y = B y (Z 0) :=
    ⟨{ toFun := fun y => B y (Z 0), map_add' := by simp, map_smul' := by simp }, fun _ => rfl⟩
  have h0 : (fun j => b j • Zs j) 0 = Zs 0 := by simp [hbdef]
  have hn : (fun j => b j • Zs j) (n + 1) = 0 := by
    apply Subtype.ext
    simp [hZs (n + 1) le_rfl, hZtop]
  have hrec' : ∀ j ≤ n, (fun j => b j • Zs j) (j + 1) - T ((fun j => b j • Zs j) j) =
      (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • Zs 0 := by
    intro j hj
    apply Subtype.ext
    have h1 := hbtop (j + 1) (by omega)
    have h2 := hbrec j
    simp only [map_smul, Submodule.coe_sub, Submodule.coe_smul, hT, hZs (j + 1) (by omega), hZs j (by omega),
      hZs 0 (by omega), hrec j hj, hpow (j + 1) (by omega)]
    have key : ∀ w : V, b j • (s ^ n)⁻¹ • (q : ℂ) ^ j • w = (-b (j + 1)) • w := by
      intro w
      rw [smul_smul, smul_smul, h2]
      congr 1
      ring
    rw [key, ← h1]
    module
  have hzE : ¬ T.HasEigenvalue z := by
    intro h
    obtain ⟨y, hy⟩ := h.exists_hasEigenvector
    have hy1 := congrArg (Subtype.val) hy.apply_eq_smul
    rw [hT] at hy1
    have hy0 : (y : V) ≠ 0 := fun h => hy.2 (Subtype.ext h)
    have hUy : U y = (s ^ n * z) • (y : V) := by
      calc U y = s ^ n • (s ^ n)⁻¹ • U y := by
            rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hs0), one_smul]
        _ = _ := by rw [hy1, Submodule.coe_smul, smul_smul]
    have hr := hpos y hy0
    have h1 := hexp y (hEW y y.2)
    have h2 : (B ((s ^ n * z) • (y : V)) ((s ^ n * z) • (y : V))).re =
        ‖s ^ n * z‖ ^ 2 * (B y y).re := by
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [← mul_assoc, mul_comm ((starRingEnd ℂ) _), Complex.mul_conj, Complex.re_ofReal_mul,
        Complex.normSq_eq_norm_sq]
    rw [hUy, h2] at h1
    have h3 := le_of_mul_le_mul_right h1 hr
    have h4 : ‖s ^ n * z‖ ^ 2 = (q : ℝ) ^ n * ‖z‖ ^ 2 := by
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm n 2, pow_mul, hsn]
    have hz2 : ‖z‖ ^ 2 < (q : ℝ)⁻¹ := by
      have := pow_lt_pow_left₀ hz (norm_nonneg z) two_ne_zero
      rw [← Real.rpow_natCast ((q : ℝ) ^ (-(1 / 2) : ℝ)), ← Real.rpow_mul hqR.le] at this
      norm_num at this
      rw [Real.rpow_neg_one] at this
      simpa using this
    have h5 : (q : ℝ) ^ ((n : ℝ) - 1) = (q : ℝ) ^ n * (q : ℝ)⁻¹ := by
      rw [Real.rpow_sub_one hqR.ne', Real.rpow_natCast, div_eq_mul_inv]
    rw [h4, h5] at h3
    exact absurd h3 (not_le.2 (mul_lt_mul_of_pos_left hz2 (pow_pos hqR n)))
  have hc : B (Z 0) (Z 0) ≠ 0 := by
    intro h
    have := hpos _ hZ0
    rw [h] at this
    simp at this
  refine count_le_of_dvd S q (B (Z 0) (Z 0)) ((q : ℂ) ^ (n + 1) - 1) z hq0 hc
    (dd n (fun j => b j • Zs j) φ) (pow_dvd_dd S n hcard T _ (Zs 0) h0 hn hrec' φ z hzE)
    (rel_of_pair S n hcard q _ _ _ φ ?_)
  intro j hj
  have hp := hpair j (by omega)
  rw [hpow j (by omega)] at hp
  show _ * φ (b j • Zs j) = _
  rw [map_smul, hφ, hZs j (by omega), smul_eq_mul, ← hbtop j (by omega)]
  calc ((q : ℂ) ^ (n + 1) - 1) * (b j * B (Z j) (Z 0))
      = b j * (((q : ℂ) ^ (n + 1) - 1) * B (Z j) (Z 0)) := by ring
    _ = _ := by rw [hp]; ring

end GlobalTheory.CompanionTheory.GapPolyProof
