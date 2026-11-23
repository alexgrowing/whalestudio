import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.WeylComplementInDetCoeffSpan

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

section Coeff

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {τ : Type*}

theorem eval_mem_span (F : MvPolynomial τ A) (p : τ → R) :
    eval (fun t => algebraMap R A (p t)) F ∈ Submodule.span R (Set.range fun m => coeff m F) := by
  classical
  rw [MvPolynomial.eval_eq]
  refine Submodule.sum_mem _ fun d _ => ?_
  have : (∏ i ∈ d.support, algebraMap R A (p i) ^ d i) = algebraMap R A (∏ i ∈ d.support, p i ^ d i) := by
    simp only [map_prod, map_pow]
  rw [this, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, rfl⟩)

theorem coeff_twist_mem (ρ : A →+* Polynomial A) (ψ : τ → MvPolynomial τ (Polynomial R)) (H : MvPolynomial τ A)
    (hH : map ρ H = eval₂ ((C : Polynomial A →+* MvPolynomial τ (Polynomial A)).comp Polynomial.C)
        (fun t => map (Polynomial.mapRingHom (algebraMap R A)) (ψ t)) H) (m : τ →₀ ℕ) (k : ℕ) :
    (ρ (coeff m H)).coeff k ∈ Submodule.span R (Set.range fun m => coeff m H) := by
  classical
  set g : τ → MvPolynomial τ (Polynomial A) := fun t => map (Polynomial.mapRingHom (algebraMap R A)) (ψ t) with hg
  set f := (C : Polynomial A →+* MvPolynomial τ (Polynomial A)).comp Polynomial.C with hf
  have e1 : eval₂ f g H = ∑ d ∈ H.support, eval₂ f g (monomial d (coeff d H)) := by
    conv_lhs => rw [H.as_sum]
    exact map_sum (eval₂Hom f g) _ _
  rw [← coeff_map, hH, e1, coeff_sum, Polynomial.finsetSum_coeff]
  refine Submodule.sum_mem _ fun d _ => ?_
  have e2 : (d.prod fun n e => g n ^ e) =
      map (Polynomial.mapRingHom (algebraMap R A)) (d.prod fun n e => ψ n ^ e) := by
    simp only [Finsupp.prod, map_prod, map_pow, hg]
  rw [eval₂_monomial, e2, hf, RingHom.comp_apply, coeff_C_mul, coeff_map, Polynomial.coeff_C_mul,
    Polynomial.coe_mapRingHom, Polynomial.coeff_map, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, rfl⟩)

end Coeff

section Row

variable {R : Type*} [CommRing R]

def rowDivL {n : ℕ} (a b : Fin n) (k : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R where
  toFun := rowDiv R a b k
  map_add' f g := by simp only [rowDiv, map_add, Polynomial.coeff_add]
  map_smul' c f := by simp only [rowDiv, map_smul, Polynomial.coeff_smul, RingHom.id_apply]

theorem rowDiv_span {n : ℕ} (a b : Fin n) (k : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) R))
    (hS : ∀ f ∈ S, rowDiv R a b k f ∈ Submodule.span R S) :
    ∀ f ∈ Submodule.span R S, rowDiv R a b k f ∈ Submodule.span R S := by
  have : Submodule.span R S ≤ (Submodule.span R S).comap (rowDivL a b k) :=
    Submodule.span_le.mpr fun f hf => hS f hf
  exact fun f hf => this hf

theorem rowGen_diag_monomial {n : ℕ} (a : Fin n) (d : Fin n × Fin n →₀ ℕ) (c : R) :
    rowGen R a a (monomial d c) = Polynomial.C (monomial d c) *
      (Polynomial.X + 1) ^ (∑ v ∈ d.support, if v.1 = a then d v else 0) := by
  classical
  have hg : ∀ v : Fin n × Fin n, (Polynomial.C (X v) +
      (if v.1 = a then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) : Polynomial (MvPolynomial (Fin n × Fin n) R)) =
      Polynomial.C (X v) * (if v.1 = a then Polynomial.X + 1 else 1) := by
    intro v
    split_ifs with h
    · have : (a, v.2) = v := by rw [← h]
      rw [this]; ring
    · ring
  unfold rowGen
  rw [aeval_monomial]
  simp only [hg, mul_pow]
  rw [Finsupp.prod_mul]
  have h1 : (d.prod fun v e => (Polynomial.C (X v) : Polynomial (MvPolynomial (Fin n × Fin n) R)) ^ e) =
      Polynomial.C (monomial d 1) := by
    rw [monomial_eq, C_1, one_mul]
    simp only [Finsupp.prod, map_prod, map_pow]
  have h2 : (d.prod fun v e => ((if v.1 = a then Polynomial.X + 1 else 1 : Polynomial (MvPolynomial (Fin n × Fin n) R))) ^ e) =
      (Polynomial.X + 1) ^ (∑ v ∈ d.support, if v.1 = a then d v else 0) := by
    rw [Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun v _ => ?_
    split_ifs <;> simp
  rw [h1, h2, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, ← mul_assoc, ← Polynomial.C_mul, C_mul_monomial,
    mul_one]

def rowInd {n : ℕ} (a : Fin n) : Fin n × Fin n → ℤ := fun v => if v.1 = a then 1 else 0

theorem weight_rowInd {n : ℕ} (a : Fin n) (d : Fin n × Fin n →₀ ℕ) :
    Finsupp.weight (rowInd a) d = ((∑ v ∈ d.support, if v.1 = a then d v else 0 : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold rowInd
  split_ifs <;> simp

theorem rowDiv_diag {n : ℕ} (a : Fin n) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) R) (z : ℤ)
    (hf : IsWeightedHomogeneous (rowInd a) f z) : rowDiv R a a k f = (z.toNat.choose k) • f := by
  classical
  have e : ∀ d ∈ f.support, rowDiv R a a k (monomial d (coeff d f)) = (z.toNat.choose k) • monomial d (coeff d f) := by
    intro d hd
    have hw := hf (mem_support_iff.mp hd)
    rw [weight_rowInd] at hw
    rw [rowDiv, rowGen_diag_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow, ← hw, Int.toNat_natCast,
      mul_comm, ← nsmul_eq_mul]
  conv_lhs => rw [f.as_sum]
  rw [show rowDiv R a a k (∑ d ∈ f.support, monomial d (coeff d f)) = rowDivL a a k (∑ d ∈ f.support, monomial d (coeff d f))
    from rfl, map_sum]
  conv_rhs => rw [f.as_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl e

end Row

section Grade

variable {r : ℕ} (ht : Fin r → ℤ)

def htW (n : ℕ) : Fin r × Fin n → ℤ := fun v => ht v.1

def GShift {R : Type*} [CommRing R] {n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous (htW ht n) (P.coeff k) (μ + k * δ)

variable {ht}

theorem gShift_mul {R : Type*} [CommRing R] {n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : GShift ht P μ δ) (hQ : GShift ht Q μ' δ) : GShift ht (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have e : μ + μ' + (k : ℤ) * δ = (μ + (x.1 : ℤ) * δ) + (μ' + (x.2 : ℤ) * δ) := by
    rw [← hx']; push_cast; ring
  rw [e]
  exact (hP x.1).mul (hQ x.2)

theorem gShift_one {R : Type*} [CommRing R] {n : ℕ} (δ : ℤ) :
    GShift ht (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    simpa using isWeightedHomogeneous_one R (htW ht n)
  · exact isWeightedHomogeneous_zero R _ _

theorem gShift_pow {R : Type*} [CommRing R] {n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : GShift ht P μ δ) (e : ℕ) : GShift ht (P ^ e) (e • μ) δ := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact gShift_one δ
  | succ e ih => rw [pow_succ, succ_nsmul]; exact gShift_mul ih hP

theorem gShift_prod {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, GShift ht (P i) (μ i) δ) : GShift ht (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (gShift_one (ht := ht) (R := R) (n := n) δ)
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact gShift_mul (h i (Finset.mem_insert_self _ _))
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem gShift_algebraMap {R : Type*} [CommRing R] {n : ℕ} (c : R) (δ : ℤ) :
    GShift ht (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [MvPolynomial.algebraMap_eq]
    simpa using isWeightedHomogeneous_C (htW ht n) c
  · exact isWeightedHomogeneous_zero R _ _

theorem gShift_gen {R : Type*} [CommRing R] {n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    GShift ht (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (htW ht n v) (ht a - ht b) := by
  intro k
  have hX : IsWeightedHomogeneous (htW ht n) (X v : MvPolynomial (Fin r × Fin n) R)
      (htW ht n v) := isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (htW ht n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (htW ht n (a, v.2)) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs with h
    · subst h; simpa using hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs with hb
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h
        have e : htW ht n v + ((1 : ℕ) : ℤ) * (ht a - ht b) = htW ht n (a, v.2) := by
          simp [htW, hb]
        rw [e]; exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

theorem gShift_rowGen_monomial (R : Type*) [CommRing R] {n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    GShift ht (rowGen R a b (monomial d c)) (Finsupp.weight (htW ht n) d) (ht a - ht b) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine gShift_mul (gShift_algebraMap c _) ?_
  unfold Finsupp.prod Finsupp.sum
  exact gShift_prod _ _ _ _ fun v _ => gShift_pow (gShift_gen a b v) _

theorem g_rowDiv_shift (R : Type*) [CommRing R] {n : ℕ} (H : ℤ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (htW ht n) f H) :
    IsWeightedHomogeneous (htW ht n) (rowDiv R a b k f) (H + k * (ht a - ht b)) := by
  unfold rowDiv
  conv => enter [2, 1, 2]; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := gShift_rowGen_monomial (ht := ht) R a b d (coeff d f) k
  rwa [hf (mem_support_iff.mp hd)] at this

theorem g_weight {n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (htW ht n) d = ∑ a : Fin r, ht a * ((Finsupp.weight (rowW r n) d a : ℕ) : ℤ) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib, hf, hg]
  | single v c =>
    simp [Finsupp.weight_apply, htW, rowW, Pi.single_apply, Finsupp.sum_single_index, mul_comm]

theorem g_of_rowW {R : Type*} [CommRing R] {n : ℕ} {f : MvPolynomial (Fin r × Fin n) R} {μ : Fin r → ℕ}
    (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    IsWeightedHomogeneous (htW ht n) f (∑ a : Fin r, ht a * (μ a : ℤ)) := by
  intro d hd
  rw [g_weight, hf hd]

theorem g_applyWord (R : Type) [CommRing R] {n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (w : List (Fin r × Fin r × ℕ)) :
    ∃ z : ℤ, IsWeightedHomogeneous (htW ht n) (applyWord R w (hw R hn ν)) z := by
  induction w with
  | nil => exact ⟨_, g_of_rowW (hwRowWeight R r n hn ν hν)⟩
  | cons x w ih =>
    obtain ⟨z, hz⟩ := ih
    exact ⟨_, g_rowDiv_shift R z x.1 x.2.1 x.2.2 _ hz⟩

end Grade

theorem weyl_le_of {R : Type} [CommRing R] {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν)
    (S : Set (MvPolynomial (Fin n × Fin n) R)) (h0 : hw R le_rfl ν ∈ Submodule.span R S)
    (hS : ∀ a b : Fin n, a ≠ b → ∀ k, ∀ f ∈ S, rowDiv R a b k f ∈ Submodule.span R S) :
    weyl R n n le_rfl ν ≤ Submodule.span R S := by
  have hw' : ∀ w : List (Fin n × Fin n × ℕ), applyWord R w (hw R le_rfl ν) ∈ Submodule.span R S := by
    intro w
    induction w with
    | nil => exact h0
    | cons x w ih =>
      show rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (hw R le_rfl ν)) ∈ _
      by_cases hab : x.1 = x.2.1
      · obtain ⟨z, hz⟩ := g_applyWord (ht := fun b => if b = x.1 then (1 : ℤ) else 0) R le_rfl ν hν w
        rw [← hab, rowDiv_diag x.1 x.2.2 _ z hz]
        exact Submodule.smul_of_tower_mem _ _ ih
      · exact rowDiv_span x.1 x.2.1 x.2.2 S (hS _ _ hab _) _ ih
  exact Submodule.span_le.mpr (by rintro _ ⟨w, rfl⟩; exact hw' w)

section Count

theorem colH_ge_iff {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (k : ℕ) (s : Fin n) :
    s.val + 1 ≤ colH ν k ↔ k < ν s := by
  unfold colH
  constructor
  · intro h
    by_contra hk
    push Not at hk
    have hsub : (Finset.univ.filter fun t : Fin n => k < ν t) ⊆ Finset.univ.filter fun t : Fin n => t.val < s.val := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      by_contra hts
      push Not at hts
      have := hν (show s ≤ t from Fin.le_iff_val_le_val.mpr hts)
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt] at this
    omega
  · intro hk
    have hsub : (Finset.univ.filter fun t : Fin n => t.val < s.val + 1) ⊆ Finset.univ.filter fun t : Fin n => k < ν t := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      have := hν (show t ≤ s from Fin.le_iff_val_le_val.mpr (by omega))
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt] at this
    have := s.isLt
    omega

theorem colH_eq_iff {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (k : ℕ) (s : Fin n) :
    colH ν k = s.val + 1 ↔ nuNext ν s ≤ k ∧ k < ν s := by
  have h1 := colH_ge_iff ν hν k s
  have hle := colH_le ν k
  unfold nuNext
  split_ifs with hs
  · have h2 := colH_ge_iff ν hν k ⟨s.val + 1, hs⟩
    simp only at h2
    constructor
    · intro h
      refine ⟨?_, h1.mp (by omega)⟩
      by_contra hc
      push Not at hc
      have := h2.mpr hc
      omega
    · rintro ⟨ha, hb⟩
      have := h1.mpr hb
      have : ¬ (s.val + 1 + 1 ≤ colH ν k) := fun hh => by have := h2.mp hh; omega
      omega
  · constructor
    · intro h
      exact ⟨Nat.zero_le _, h1.mp (by omega)⟩
    · rintro ⟨_, hb⟩
      have := h1.mpr hb
      have := s.isLt
      omega

theorem card_Ico_fin (c a b : ℕ) (hb : b ≤ c) :
    (Finset.univ.filter fun k : Fin c => a ≤ k.val ∧ k.val < b).card = b - a := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun k : Fin c => k.val < b)
    (fun k : Fin c => k.val < a)
  rw [Finset.filter_filter, Finset.filter_filter, Fin.card_filter_val_lt] at h
  have e1 : (Finset.univ.filter fun k : Fin c => k.val < b ∧ k.val < a) =
      Finset.univ.filter fun k : Fin c => k.val < min a b := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have e2 : (Finset.univ.filter fun k : Fin c => k.val < b ∧ ¬ k.val < a) =
      Finset.univ.filter fun k : Fin c => a ≤ k.val ∧ k.val < b := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [e1, e2, Fin.card_filter_val_lt] at h
  omega

theorem prod_fin_count {M : Type*} [CommMonoid M] {c n : ℕ} (g : Fin c → ℕ) (hg : ∀ k, g k ≤ n) (F : ℕ → M)
    (hF : F 0 = 1) :
    ∏ k : Fin c, F (g k) =
      ∏ s : Fin n, F (s.val + 1) ^ (Finset.univ.filter fun k : Fin c => g k = s.val + 1).card := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (n + 1)) (g := g)
    (fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hg k)))]
  have inner : ∀ j, ∏ i ∈ Finset.univ.filter (fun i => g i = j), F (g i) =
      F j ^ (Finset.univ.filter fun i => g i = j).card := fun j => by
    rw [Finset.prod_congr rfl (fun i hi => congrArg F (Finset.mem_filter.mp hi).2), Finset.prod_const]
  simp only [inner]
  rw [Finset.prod_range_succ', hF, one_pow, mul_one,
    Fin.prod_univ_eq_prod_range (fun s => F (s + 1) ^ (Finset.univ.filter fun k : Fin c => g k = s + 1).card) n]

theorem count_even {n c : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (hc : ∀ t, ν t ≤ c) (s : Fin n) :
    (Finset.univ.filter fun k : Fin c => colH ν k.val = s.val + 1).card = ν s - nuNext ν s := by
  have e : (Finset.univ.filter fun k : Fin c => colH ν k.val = s.val + 1) =
      Finset.univ.filter fun k : Fin c => nuNext ν s ≤ k.val ∧ k.val < ν s := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact colH_eq_iff ν hν k.val s
  rw [e, card_Ico_fin c _ _ (hc s)]

theorem count_odd {n c : ℕ} (μ : Fin n → ℕ) (hμ : Antitone μ) (hc : ∀ t, μ t ≤ c) (s : Fin n) :
    (Finset.univ.filter fun k : Fin c => n - colH μ k.val = s.val + 1).card =
      (fun t : Fin n => c - μ t.rev) s - nuNext (fun t : Fin n => c - μ t.rev) s := by
  have hs := s.isLt
  by_cases hl : s.val + 1 < n
  · set s' : Fin n := ⟨n - 2 - s.val, by omega⟩ with hs'
    have e : (Finset.univ.filter fun k : Fin c => n - colH μ k.val = s.val + 1) =
        Finset.univ.filter fun k : Fin c => nuNext μ s' ≤ k.val ∧ k.val < μ s' := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← colH_eq_iff μ hμ k.val s']
      have := colH_le μ k.val
      simp only [hs']
      omega
    rw [e, card_Ico_fin c _ _ (hc s')]
    unfold nuNext
    rw [dif_pos hl, dif_pos (show s'.val + 1 < n by simp only [hs']; omega)]
    have r1 : (⟨s.val + 1, hl⟩ : Fin n).rev = s' := Fin.ext (by simp only [Fin.val_rev, hs']; omega)
    have r2 : s.rev = ⟨s'.val + 1, by simp only [hs']; omega⟩ := Fin.ext (by simp only [Fin.val_rev, hs']; omega)
    simp only [r1, r2]
    have := hμ (show s' ≤ ⟨s'.val + 1, by simp only [hs']; omega⟩ from Fin.le_iff_val_le_val.mpr (by simp))
    have := hc s'
    omega
  · have hn : s.val + 1 = n := by omega
    have e : (Finset.univ.filter fun k : Fin c => n - colH μ k.val = s.val + 1) =
        Finset.univ.filter fun k : Fin c => μ ⟨0, by omega⟩ ≤ k.val ∧ k.val < c := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := colH_ge_iff μ hμ k.val ⟨0, by omega⟩
      have := colH_le μ k.val
      have := k.isLt
      simp only [zero_add] at h1
      constructor
      · intro h
        refine ⟨?_, k.isLt⟩
        by_contra hh
        push Not at hh
        have := h1.mpr hh
        omega
      · rintro ⟨h, _⟩
        have : ¬ 1 ≤ colH μ k.val := fun hh => by have := h1.mp hh; omega
        omega
    rw [e, card_Ico_fin c _ _ le_rfl]
    unfold nuNext
    rw [dif_neg hl]
    have r2 : s.rev = ⟨0, by omega⟩ := Fin.ext (by simp only [Fin.val_rev]; omega)
    simp only [r2]
    omega

end Count

section Even

variable {R : Type} [CommRing R] {n : ℕ}

def lpF (R : Type) [CommRing R] (n s : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  if h : s ≤ n then lpMinor R s h h else 1

theorem lpF_zero : lpF R n 0 = 1 := by
  unfold lpF lpMinor
  rw [dif_pos (Nat.zero_le n), Matrix.det_isEmpty]

theorem prod_lpF_eq_hw (ν : Fin n → ℕ) (c : ℕ) (g : Fin c → ℕ) (hg : ∀ k, g k ≤ n)
    (hcount : ∀ s : Fin n, (Finset.univ.filter fun k : Fin c => g k = s.val + 1).card = ν s - nuNext ν s) :
    ∏ k : Fin c, lpF R n (g k) = hw R le_rfl ν := by
  rw [prod_fin_count g hg (lpF R n) lpF_zero]
  unfold hw
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hcount s, lpF, dif_pos (show s.val + 1 ≤ n from s.isLt)]

def ptE (R : Type) [CommRing R] (n : ℕ) : ℕ × Fin n → R := fun v => if v.1 = v.2.val then 1 else 0

theorem eval_detX (e : ℕ) :
    eval (fun v => algebraMap R (MvPolynomial (Fin n × Fin n) R) (ptE R n v))
      ((Matrix.of fun a i : Fin n => gX R n a i.val).det ^ e) = 1 := by
  rw [map_pow, RingHom.map_det]
  have : (eval fun v => algebraMap R (MvPolynomial (Fin n × Fin n) R) (ptE R n v)).mapMatrix
      (Matrix.of fun a i : Fin n => gX R n a i.val) = 1 := by
    ext a i
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, gX, eval_X, ptE, Matrix.one_apply]
    by_cases h : a = i
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'.symm)), map_zero]
  rw [this, Matrix.det_one, one_pow]

theorem eval_hvE (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    eval (fun v => algebraMap R (MvPolynomial (Fin n × Fin n) R) (ptE R n v)) (hvE (gX R n) (gY R n) c h hh) =
      ∏ k, lpF R n (h k) := by
  unfold hvE
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det, lpF, dif_pos (hh k)]
  unfold lpMinor
  congr 1
  ext i t
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, gX, gY, map_sum, map_mul, eval_X, eval_C, ptE]
  rw [Finset.sum_eq_single (Fin.castLE (hh k) i)]
  · simp
  · intro b _ hb
    rw [if_neg (fun h' => hb (Fin.ext (by simp [h']))), map_zero, zero_mul]
  · simp

def psiE (R : Type) [CommRing R] (a b : Fin n) : ℕ × Fin n → MvPolynomial (ℕ × Fin n) (Polynomial R) :=
  fun v => X v + if v.2 = a then C Polynomial.X * X (v.1, b) else 0

theorem rowGen_X (a b : Fin n) (v : Fin n × Fin n) :
    rowGen R a b (X v) = Polynomial.C (X v) + (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  unfold rowGen; rw [aeval_X]

theorem entry_even (a b : Fin n) (i : ℕ) (t : Fin n) :
    map (rowGen R (n := n) a b).toRingHom
        (∑ a' : Fin n, (X (i, a') : GenR R n) * C (X (a', t))) =
      eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiE R a b v))
        (∑ a' : Fin n, (X (i, a') : GenR R n) * C (X (a', t))) := by
  simp only [map_sum, map_mul, map_X, map_C, eval₂Hom_X', eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowGen_X, psiE,
    map_add, map_X]
  have hL : ∀ a' : Fin n, (X (i, a') : MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R))) *
      (C (Polynomial.C (X (a', t))) + C (if a' = b then Polynomial.X * Polynomial.C (X (a, t)) else 0)) =
      X (i, a') * C (Polynomial.C (X (a', t))) +
        if a' = b then X (i, b) * C (Polynomial.X * Polynomial.C (X (a, t))) else 0 := by
    intro a'
    split_ifs with h
    · subst h; rw [mul_add]
    · simp
  have hR : ∀ a' : Fin n, ((X (i, a') : MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R))) +
      map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R)))
        (if a' = a then C Polynomial.X * X (i, b) else 0)) * C (Polynomial.C (X (a', t))) =
      X (i, a') * C (Polynomial.C (X (a', t))) +
        if a' = a then C Polynomial.X * X (i, b) * C (Polynomial.C (X (a, t))) else 0 := by
    intro a'
    split_ifs with h
    · subst h; rw [map_mul, map_C, map_X, Polynomial.coe_mapRingHom, Polynomial.map_X, add_mul]
    · rw [map_zero, add_zero, add_zero]
  rw [Finset.sum_congr rfl fun a' _ => hL a', Finset.sum_congr rfl fun a' _ => hR a', Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _),
    C_mul]
  ring

theorem detX_even (a b : Fin n) (hab : a ≠ b) :
    map (rowGen R (n := n) a b).toRingHom (Matrix.of fun a i : Fin n => gX R n a i.val).det =
      eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiE R a b v))
        (Matrix.of fun a i : Fin n => gX R n a i.val).det := by
  rw [RingHom.map_det, RingHom.map_det]
  set Xm : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R))) :=
    Matrix.of fun a i : Fin n => X (i.val, a) with hXm
  have h1 : (map (rowGen R (n := n) a b).toRingHom).mapMatrix (Matrix.of fun a i : Fin n => gX R n a i.val) = Xm := by
    refine Matrix.ext fun a' i => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, gX, map_X, hXm]
  have h2 : (eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiE R a b v))).mapMatrix
        (Matrix.of fun a i : Fin n => gX R n a i.val) = Xm.updateRow a (Xm a + (C (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) :
          MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R))) • Xm b) := by
    refine Matrix.ext fun a' i => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, gX, eval₂Hom_X', psiE, map_add, map_X, hXm]
    by_cases h : a' = a
    · subst h
      rw [Matrix.updateRow_self, if_pos rfl, map_mul, map_C, map_X, Polynomial.coe_mapRingHom, Polynomial.map_X]
      simp only [Pi.add_apply, Pi.smul_apply, Matrix.of_apply, smul_eq_mul]
    · rw [Matrix.updateRow_ne h, if_neg h, map_zero, add_zero]
      rfl
  rw [h1, h2, Matrix.det_updateRow_add_smul_self _ hab]

theorem hvE_even (a b : Fin n) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    map (rowGen R (n := n) a b).toRingHom (hvE (gX R n) (gY R n) c h hh) =
      eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiE R a b v))
        (hvE (gX R n) (gY R n) c h hh) := by
  unfold hvE
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i t => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, gX, gY]
  exact entry_even (R := R) a b i.val (Fin.castLE (hh k) t)

theorem twist_even (a b : Fin n) (hab : a ≠ b) (c e : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    map (rowGen R (n := n) a b).toRingHom
        ((Matrix.of fun a i : Fin n => gX R n a i.val).det ^ e * hvE (gX R n) (gY R n) c h hh) =
      eval₂ ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiE R a b v))
        ((Matrix.of fun a i : Fin n => gX R n a i.val).det ^ e * hvE (gX R n) (gY R n) c h hh) := by
  rw [← coe_eval₂Hom, map_mul, map_mul, map_pow, map_pow, detX_even a b hab, hvE_even a b c h hh]

end Even

theorem weyl_lattice_det_coeff_span : WeylLatticeInDetCoeffSpan := by
  intro R _ n ν hν c e hc
  refine weyl_le_of ν hν _ ?_ ?_
  · have := eval_mem_span (R := R)
      ((Matrix.of fun a i : Fin n => gX R n a i.val).det ^ e *
        hvE (gX R n) (gY R n) c (fun k => colH ν k.val) (fun k => colH_le ν k.val)) (ptE R n)
    rwa [map_mul, eval_detX, eval_hvE, one_mul,
      prod_lpF_eq_hw ν c (fun k => colH ν k.val) (fun k => colH_le ν k.val) (count_even ν hν hc)] at this
  · rintro a b hab k _ ⟨m, rfl⟩
    exact coeff_twist_mem (rowGen R (n := n) a b).toRingHom (psiE R a b) _ (twist_even a b hab c e _ _) m k

section MatO

variable {S : Type*} [CommRing S] {n : ℕ}

theorem tv_mul_apply (i j : Fin n) (c : S) (M : Matrix (Fin n) (Fin n) S) (a t : Fin n) :
    (Matrix.transvection i j c * M) a t = M a t + if a = i then c * M j t else 0 := by
  rw [Matrix.transvection, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  by_cases h : a = i
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm h]

theorem mulC_tv_apply (i j : Fin n) (c : S) (x : Fin n → ℕ → S) (a : Fin n) (k : ℕ) :
    mulC (Matrix.transvection i j c) x a k = x a k + if a = i then c * x j k else 0 := by
  unfold mulC
  simp only [Matrix.transvection, Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  by_cases h : a = i
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm h]

theorem mulC_one' (x : Fin n → ℕ → S) : mulC (1 : Matrix (Fin n) (Fin n) S) x = x := by
  funext a k
  simp [mulC, Matrix.one_apply]

theorem det_catM_tv (l : ℕ) (i j : Fin n) (hij : i ≠ j) (c : S) (y : Matrix (Fin n) (Fin n) S) (x : Fin n → ℕ → S) :
    (catM l (Matrix.transvection i j c * y) x).det = (catM l y (mulC (Matrix.transvection i j (-c)) x)).det := by
  have h1 : x = mulC (Matrix.transvection i j c) (mulC (Matrix.transvection i j (-c)) x) := by
    rw [← mulC_mul, Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel, Matrix.transvection_zero,
      mulC_one']
  conv_lhs => rw [h1]
  rw [← mul_catM, Matrix.det_mul, Matrix.det_transvection_of_ne i j hij, one_mul]

def revTail (n h : ℕ) (hh : h ≤ n) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (fun t => if ht : t.val < n - h then t else ⟨2 * n - h - 1 - t.val, by have := t.isLt; omega⟩)
    (by
      intro t
      by_cases ht : t.val < n - h
      · simp only [dif_pos ht]
      · have := t.isLt
        have h2 : ¬ (2 * n - h - 1 - t.val < n - h) := by omega
        simp only [dif_neg ht, dif_neg h2]
        exact Fin.ext (by simp only []; omega))

theorem revTail_apply_lt (n h : ℕ) (hh : h ≤ n) (t : Fin n) (ht : t.val < n - h) : revTail n h hh t = t := by
  change (fun t : Fin n => if ht : t.val < n - h then t else
    (⟨2 * n - h - 1 - t.val, by have := t.isLt; omega⟩ : Fin n)) t = t
  simp only [dif_pos ht]

theorem revTail_apply_ge (n h : ℕ) (hh : h ≤ n) (t : Fin n) (ht : ¬ t.val < n - h) :
    (revTail n h hh t).val = 2 * n - h - 1 - t.val := by
  change ((fun t : Fin n => if ht : t.val < n - h then t else
    (⟨2 * n - h - 1 - t.val, by have := t.isLt; omega⟩ : Fin n)) t).val = _
  simp only [dif_neg ht]

theorem det_catM_rev (h : ℕ) (hh : h ≤ n) (y : Matrix (Fin n) (Fin n) S) (x : Fin n → ℕ → S)
    (hx : ∀ a i, x a i = if i + a.val + 1 = n then 1 else 0) :
    ((Equiv.Perm.sign (revTail n h hh) : ℤ) : S) * (catM h y x).det =
      (Matrix.of fun p q : Fin (n - h) => y (Fin.castLE (Nat.sub_le n h) p) (Fin.castLE (Nat.sub_le n h) q)).det := by
  rw [← Matrix.det_permute', det_unit_cols (Nat.sub_le n h)]
  · congr 1
    refine Matrix.ext fun p q => ?_
    have hq : (Fin.castLE (Nat.sub_le n h) q).val < n - h := by simp
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, revTail_apply_lt n h hh _ hq, catM, hq, if_true]
  · intro a t ht
    have hnt : ¬ t.val < n - h := by omega
    have hv := revTail_apply_ge n h hh t hnt
    have := t.isLt
    have h3 : ¬ (revTail n h hh t).val < n - h := by omega
    simp only [Matrix.submatrix_apply, id, catM, h3, if_false, hx]
    rw [hv]
    by_cases hat : a = t
    · subst hat; rw [if_pos (by omega), if_pos rfl]
    · rw [if_neg (fun h' => hat (Fin.ext (by omega))), if_neg hat]

end MatO

section Odd

variable {R : Type} [CommRing R] {n : ℕ}

def ptO (R : Type) [CommRing R] (n : ℕ) : ℕ × Fin n → R := fun v => if v.1 + v.2.val + 1 = n then 1 else 0

theorem eval_hvO (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    (∏ k, ((Equiv.Perm.sign (revTail n (h k) (hh k)) : ℤ) : MvPolynomial (Fin n × Fin n) R)) *
      eval (fun v => algebraMap R (MvPolynomial (Fin n × Fin n) R) (ptO R n v)) (hvO (gX R n) (gY R n) c h) =
      ∏ k, lpF R n (n - h k) := by
  unfold hvO
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_catM, det_catM_rev (h k) (hh k), lpF, dif_pos (Nat.sub_le _ _)]
  · unfold lpMinor
    congr 1
    refine Matrix.ext fun p q => ?_
    simp [gY]
  · intro a i
    simp only [gX, eval_X, ptO]
    split_ifs <;> simp

def psiO (R : Type) [CommRing R] (a b : Fin n) : ℕ × Fin n → MvPolynomial (ℕ × Fin n) (Polynomial R) :=
  fun v => X v + if v.2 = b then (-C Polynomial.X) * X (v.1, a) else 0

theorem catM_odd (a b : Fin n) (hab : a ≠ b) (l : ℕ) :
    map (rowGen R (n := n) a b).toRingHom (catM l (gY R n) (gX R n)).det =
      eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiO R a b v))
        (catM l (gY R n) (gX R n)).det := by
  rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_catM, map_catM]
  set Y' : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R))) :=
    fun a t => C (Polynomial.C (X (a, t))) with hY'
  set X' : Fin n → ℕ → MvPolynomial (ℕ × Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R)) :=
    fun a i => X (i, a) with hX'
  have e1 : (gY R n).map (map (rowGen R (n := n) a b).toRingHom) = Matrix.transvection b a (C Polynomial.X) * Y' := by
    refine Matrix.ext fun a' t => ?_
    rw [tv_mul_apply]
    simp only [Matrix.map_apply, gY, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowGen_X, hY']
    by_cases h : a' = b
    · subst h; rw [if_pos rfl, if_pos rfl, C_add, C_mul]
    · rw [if_neg h, if_neg h, add_zero, add_zero]
  have e2 : (fun a₁ i => map (rowGen R (n := n) a b).toRingHom (gX R n a₁ i)) = X' := by
    funext a' i
    simp only [gX, map_X, hX']
  have e3 : (gY R n).map (eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp
      Polynomial.C) (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiO R a b v))) =
      Y' := by
    refine Matrix.ext fun a' t => ?_
    simp only [Matrix.map_apply, gY, eval₂Hom_C, RingHom.comp_apply, hY']
  have e4 : (fun a₁ i => eval₂Hom ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp
      Polynomial.C) (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiO R a b v))
      (gX R n a₁ i)) = mulC (Matrix.transvection b a (-(C Polynomial.X))) X' := by
    funext a' i
    rw [mulC_tv_apply]
    simp only [gX, eval₂Hom_X', psiO, map_add, map_X, hX']
    by_cases h : a' = b
    · subst h; rw [if_pos rfl, if_pos rfl, map_mul, map_neg, map_C, map_X, Polynomial.coe_mapRingHom, Polynomial.map_X]
    · rw [if_neg h, if_neg h, map_zero]
  rw [e1, e2, e3, e4, det_catM_tv l b a (Ne.symm hab)]

theorem twist_odd (a b : Fin n) (hab : a ≠ b) (c : ℕ) (h : Fin c → ℕ) :
    map (rowGen R (n := n) a b).toRingHom (hvO (gX R n) (gY R n) c h) =
      eval₂ ((C : Polynomial (MvPolynomial (Fin n × Fin n) R) →+* MvPolynomial (ℕ × Fin n) _).comp Polynomial.C)
        (fun v => map (Polynomial.mapRingHom (algebraMap R (MvPolynomial (Fin n × Fin n) R))) (psiO R a b v))
        (hvO (gX R n) (gY R n) c h) := by
  unfold hvO
  rw [← coe_eval₂Hom, map_prod, map_prod]
  exact Finset.prod_congr rfl fun k _ => catM_odd a b hab (h k)

end Odd

theorem weyl_complement_det_coeff_span : WeylComplementInDetCoeffSpan := by
  intro R _ n μ hμ c hc
  have hκ : Antitone (fun t : Fin n => c - μ t.rev) := fun s t hst => by
    have := hμ (Fin.rev_le_rev.mpr hst)
    simp only
    omega
  refine weyl_le_of _ hκ _ ?_ ?_
  · have hm := eval_mem_span (R := R) (hvO (gX R n) (gY R n) c (fun k => colH μ k.val)) (ptO R n)
    have e := eval_hvO (R := R) c (fun k => colH μ k.val) (fun k => colH_le μ k.val)
    rw [prod_lpF_eq_hw _ c (fun k => n - colH μ k.val) (fun k => Nat.sub_le _ _) (count_odd μ hμ hc)] at e
    rw [← e, ← Int.cast_prod, ← zsmul_eq_mul]
    exact Submodule.smul_of_tower_mem _ _ hm
  · rintro a b hab k _ ⟨m, rfl⟩
    exact coeff_twist_mem (rowGen R (n := n) a b).toRingHom (psiO R a b) _ (twist_odd a b hab c _) m k

end Formalism.L2.PairingIndexBounds.Ent
