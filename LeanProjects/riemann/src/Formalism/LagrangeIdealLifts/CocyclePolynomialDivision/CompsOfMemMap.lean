import Formalism.LagrangeIdealLifts.Statement

noncomputable section

namespace Formalism.LIFT

open Finset

section XH

variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A) (aa : Ideal A)

def Comps (ℓ : ℕ) (x : A) : Prop :=
  ∃ e : Fin ℓ → A, (∀ i, e i ∈ aa) ∧ x = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)

theorem comps_zero : Comps φA ε aa ℓ 0 :=
  ⟨0, fun _ => aa.zero_mem, by simp⟩

theorem comps_add {x y : A} (hx : Comps φA ε aa ℓ x) (hy : Comps φA ε aa ℓ y) :
    Comps φA ε aa ℓ (x + y) := by
  obtain ⟨e, he, rfl⟩ := hx
  obtain ⟨e', he', rfl⟩ := hy
  refine ⟨e + e', fun i => aa.add_mem (he i) (he' i), ?_⟩
  simp [map_add, mul_add, sum_add_distrib]

theorem comps_mul_phi (s : A) {x : A} (hx : Comps φA ε aa ℓ x) :
    Comps φA ε aa ℓ (φA s * x) := by
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨fun i => s * e i, fun i => aa.mul_mem_left s (he i), ?_⟩
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_mul]; ring

theorem comps_mul_eps (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ) {x : A} (hx : Comps φA ε aa ℓ x) :
    Comps φA ε aa ℓ (ε * x) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨Fin.cons (ε * e (Fin.last k)) (fun i => e i.castSucc), ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using aa.mul_mem_left ε (he (Fin.last k))
    · simpa using he j.castSucc
  · rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, Fin.val_castSucc,
      Fin.val_last, map_mul, hε, pow_zero, one_mul, mul_add, mul_sum]
    rw [add_comm]
    congr 1
    · ring
    · refine sum_congr rfl fun i _ => ?_
      ring

theorem comps_mul_pow (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ) (n : ℕ) {x : A}
    (hx : Comps φA ε aa ℓ x) : Comps φA ε aa ℓ (ε ^ n * x) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    exact comps_mul_eps φA ε aa hℓ hε ih

theorem comps_sum {ι : Type} (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, Comps φA ε aa ℓ (f i)) :
    Comps φA ε aa ℓ (∑ i ∈ s, f i) :=
  Finset.sum_induction _ _ (fun _ _ => comps_add φA ε aa) (comps_zero φA ε aa) h

theorem comps_mul (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (r : A) {x : A} (hx : Comps φA ε aa ℓ x) : Comps φA ε aa ℓ (r * x) := by
  obtain ⟨e, he⟩ := (hU r).exists
  rw [he, sum_mul]
  refine comps_sum φA ε aa _ _ fun i _ => ?_
  rw [mul_assoc]
  exact comps_mul_pow φA ε aa hℓ hε _ (comps_mul_phi φA ε aa _ hx)

theorem comps_phi (hℓ : 0 < ℓ) {a : A} (ha : a ∈ aa) : Comps φA ε aa ℓ (φA a) := by
  refine ⟨fun i => if (i : ℕ) = 0 then a else 0, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact ha
    · exact aa.zero_mem
  · rw [Fintype.sum_eq_single ⟨0, hℓ⟩]
    · simp
    · intro i hi
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]

theorem comps_of_mem_map (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    {x : A} (hx : x ∈ Ideal.map φA aa) : Comps φA ε aa ℓ x := by
  let S : Ideal A :=
    { carrier := {x | Comps φA ε aa ℓ x}
      add_mem' := fun ha hb => comps_add φA ε aa ha hb
      zero_mem' := comps_zero φA ε aa
      smul_mem' := fun r _ hx => comps_mul φA ε aa hℓ hε hU r hx }
  have hle : Ideal.map φA aa ≤ S :=
    Ideal.map_le_iff_le_comap.2 fun a ha => comps_phi φA ε aa hℓ ha
  exact hle hx

theorem comp_mem (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    {x : A} (hx : x ∈ Ideal.map φA aa) (e : Fin ℓ → A)
    (he : x = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) (i : Fin ℓ) : e i ∈ aa := by
  obtain ⟨e', he', hx'⟩ := comps_of_mem_map φA ε aa hℓ hε hU hx
  have : e = e' := (hU x).unique he hx'
  rw [this]
  exact he' i

theorem xh_comp (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (X Q : A) (H : ℕ) (hX : φA X = X * Q)
    (hQ : ∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) (e : Fin ℓ → A)
    (h : X ^ H * ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i) ∈ aa) (i : Fin ℓ) :
    X ^ H * e i ∈ aa := by
  have h1 := hQ _ h
  have h2 : Q ^ H * (X ^ H * ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) =
      ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (X ^ H * e i) := by
    simp only [map_mul, map_pow, hX, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  exact comp_mem φA ε aa hℓ hε hU h1 (fun i => X ^ H * e i) h2 i

theorem sum_split {M : Type} [AddCommMonoid M] (F : ℕ → M) (a N : ℕ) :
    ∑ i : Fin a, ∑ j ∈ range N, F (i + a * j) = ∑ k ∈ range (a * N), F k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, sum_range_add, ← ih]
    simp only [sum_range_succ, sum_add_distrib]
    congr 1
    rw [Finset.sum_range (fun x => F (a * N + x))]
    refine sum_congr rfl fun i _ => ?_
    rw [add_comm]

theorem xh_coeffs (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (X Q : A) (H : ℕ) (hX : φA X = X * Q)
    (hQ : ∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) (n : ℕ) :
    ∀ m : ℕ → ℤ, X ^ H * ∑ k ∈ range (ℓ ^ n), (m k : A) * ε ^ k ∈ aa →
      ∀ k < ℓ ^ n, X ^ H * (m k : A) ∈ aa := by
  induction n with
  | zero =>
    intro m h k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simpa using h
  | succ n ih =>
    intro m h k hk
    let e : Fin ℓ → A := fun i => ∑ j ∈ range (ℓ ^ n), (m (i + ℓ * j) : A) * ε ^ j
    have hdec : ∑ k ∈ range (ℓ ^ (n + 1)), (m k : A) * ε ^ k =
        ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i) := by
      rw [pow_succ', ← sum_split (fun k => (m k : A) * ε ^ k) ℓ (ℓ ^ n)]
      refine sum_congr rfl fun i _ => ?_
      simp only [e, map_sum, map_mul, map_intCast, map_pow, hε, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [pow_add, ← pow_mul]
      ring
    rw [hdec] at h
    have hb := xh_comp φA ε aa hℓ hε hU X Q H hX hQ e h ⟨k % ℓ, Nat.mod_lt _ hℓ⟩
    have hk' : k / ℓ < ℓ ^ n := by
      rw [Nat.div_lt_iff_lt_mul hℓ]
      rw [pow_succ] at hk
      exact hk
    have := ih (fun j => m (k % ℓ + ℓ * j)) hb (k / ℓ) hk'
    simpa [Nat.mod_add_div] using this

end XH

theorem xHKills_proof : XHKills := by
  intro ℓ _ A _ φA ε X Q H c aa _ hε hU hX hQ hc
  have hℓ : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have h1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  obtain ⟨n, hn⟩ : ∃ n, c < ℓ ^ n := ⟨c, Nat.lt_pow_self h1⟩
  let p : Polynomial ℤ := (Polynomial.X - Polynomial.C 1) ^ c
  have hmon : p.Monic := (Polynomial.monic_X_sub_C (1 : ℤ)).pow c
  have hdeg : p.natDegree = c := by
    simp only [p]
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hsum : (ε - 1) ^ c = ∑ k ∈ range (ℓ ^ n), (p.coeff k : A) * ε ^ k := by
    have := Polynomial.aeval_eq_sum_range' (p := p) (by omega : p.natDegree < ℓ ^ n) ε
    simp only [zsmul_eq_mul] at this
    rw [← this]
    simp [p]
  have hmem : X ^ H * ∑ k ∈ range (ℓ ^ n), (p.coeff k : A) * ε ^ k ∈ aa := by
    rw [← hsum]
    exact aa.mul_mem_left _ hc
  have := xh_coeffs φA ε aa hℓ hε hU X Q H hX hQ n (fun k => p.coeff k) hmem c hn
  have hcoef : p.coeff c = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  simpa [hcoef] using this

end Formalism.LIFT
