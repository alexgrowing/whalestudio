import Mathlib

open scoped BigOperators

namespace GlobalTheory

namespace Amitsur

open Matrix Polynomial

theorem det_one_sub_smul_mem_of_nilpotent {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (U : Subring A) (t : A) (N : ℕ) (ht : t ^ N = 0) (S : Set (Matrix ι ι A))
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hsm : ∀ a ∈ S, t • a ∈ S)
    (hdet : ∀ a ∈ S, (1 - a).det ∈ U) :
    ∀ B ∈ AddSubmonoid.closure S, (1 - t • B).det ∈ U := by
  have hpow : ∀ (k : ℕ), ∀ a ∈ S, t ^ k • a ∈ S := by
    intro k a ha
    induction k with
    | zero => simpa using ha
    | succ k ih => rw [pow_succ', mul_smul]; exact hsm _ ih
  have hM1 : ∀ a ∈ S, ∀ y ∈ AddSubmonoid.closure S, a * y ∈ AddSubmonoid.closure S := by
    intro a ha y hy
    induction hy using AddSubmonoid.closure_induction with
    | mem x hx => exact AddSubmonoid.subset_closure (hmul a ha x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  have hM2 : ∀ y ∈ AddSubmonoid.closure S, t • y ∈ AddSubmonoid.closure S := by
    intro y hy
    induction hy using AddSubmonoid.closure_induction with
    | mem x hx => exact AddSubmonoid.subset_closure (hsm x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  have hM3 : ∀ a ∈ S, ∀ (j : ℕ), ∀ y ∈ AddSubmonoid.closure S,
      a ^ j * y ∈ AddSubmonoid.closure S := by
    intro a ha j y hy
    induction j with
    | zero => simpa using hy
    | succ j ih => rw [pow_succ', mul_assoc]; exact hM1 a ha _ ih
  have step : ∀ e : ℕ, (∀ C ∈ AddSubmonoid.closure S, (1 - t ^ (e + 2) • C).det ∈ U) →
      ∀ B ∈ AddSubmonoid.closure S, (1 - t ^ (e + 1) • B).det ∈ U := by
    intro e ih
    have key : ∀ B ∈ AddSubmonoid.closure S, ∀ C ∈ AddSubmonoid.closure S,
        (1 - t ^ (e + 1) • (B + t • C)).det ∈ U := by
      intro B hB
      induction hB using AddSubmonoid.closure_induction_left with
      | zero =>
        intro C hC
        have := ih C hC
        rwa [zero_add, smul_smul, ← pow_succ]
      | add_left s hs B hB ihB =>
        intro C hC
        set a : Matrix ι ι A := t ^ (e + 1) • s with ha
        have haS : a ∈ S := hpow _ _ hs
        have haN : a ^ N = 0 := by
          rw [ha, _root_.smul_pow, ← pow_mul, add_mul, one_mul, pow_add, ht, mul_zero, zero_smul]
        set g : Matrix ι ι A := ∑ j ∈ Finset.range N, a ^ j with hg
        have hga : (1 - a) * g = 1 := by
          rw [hg, mul_neg_geom_sum, haN, sub_zero]
        set y : Matrix ι ι A := B + t • C with hy
        have hyM : y ∈ AddSubmonoid.closure S := add_mem hB (hM2 C hC)
        have hgy : g * y ∈ AddSubmonoid.closure S := by
          rw [hg, Finset.sum_mul]
          exact sum_mem fun j _ => hM3 a haS j y hyM
        have hC' : C + (t ^ e • s) * (g * y) ∈ AddSubmonoid.closure S :=
          add_mem hC (hM1 _ (hpow _ _ hs) _ hgy)
        have h1 := ihB _ hC'
        have e1 : B + t • (C + (t ^ e • s) * (g * y)) = g * y := by
          have h2 : t • ((t ^ e • s) * (g * y)) = a * (g * y) := by
            rw [← smul_mul_assoc, smul_smul, ← pow_succ']
          have h3 : g * y = (1 - a) * g * y + a * (g * y) := by noncomm_ring
          rw [smul_add, h2, ← add_assoc, ← hy]
          conv_rhs => rw [h3, hga, one_mul]
        rw [e1] at h1
        have e2 : 1 - t ^ (e + 1) • (s + B + t • C) = (1 - a) * (1 - t ^ (e + 1) • (g * y)) := by
          rw [mul_sub, mul_one, mul_smul_comm, ← mul_assoc, hga, one_mul, add_assoc, ← hy,
            smul_add, ← ha, sub_sub]
        rw [e2, det_mul]
        exact U.mul_mem (hdet a haS) h1
    intro B hB
    simpa using key B hB 0 (zero_mem _)
  have all : ∀ k e : ℕ, N ≤ e + k → ∀ B ∈ AddSubmonoid.closure S,
      (1 - t ^ (e + 1) • B).det ∈ U := by
    intro k
    induction k with
    | zero =>
      intro e he B _
      have : t ^ (e + 1) = 0 := pow_eq_zero_of_le (by omega) ht
      simp [this]
    | succ k ih =>
      intro e he
      exact step e (ih (e + 1) (by omega))
  intro B hB
  simpa using all N 0 (by omega) B hB

theorem eval₂_charpolyRev {R A ι : Type*} [CommRing R] [CommRing A] [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (u : A) (s : Matrix ι ι R) :
    (1 - u • s.map φ).det = s.charpolyRev.eval₂ φ u := by
  rw [← coe_eval₂RingHom, Matrix.charpolyRev, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply] <;> ring

theorem det_sum_smul_mem {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (T : Subring R) (S : Set (Matrix ι ι R)) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hchar : ∀ a ∈ S, ∀ j, a.charpoly.coeff j ∈ T)
    (F : Finset κ) (c : κ → R) (s : κ → Matrix ι ι R) (hc : ∀ k, c k ∈ T) (hs : ∀ k, s k ∈ S) :
    (∑ k ∈ F, c k • s k).det ∈ T := by
  nontriviality R
  set n := Fintype.card ι with hn
  let I : Ideal R[X] := Ideal.span {X ^ (n + 1)}
  let π : R[X] →+* R[X] ⧸ I := Ideal.Quotient.mk I
  let φ : R →+* R[X] ⧸ I := π.comp C
  let U : Subring (R[X] ⧸ I) := (π.comp (Polynomial.mapRingHom T.subtype)).range
  have hφ : ∀ x ∈ T, φ x ∈ U := fun x hx => ⟨C ⟨x, hx⟩, by simp [φ]⟩
  have htU : π X ∈ U := ⟨X, by simp⟩
  have ht : π X ^ (n + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  let S' : Set (Matrix ι ι (R[X] ⧸ I)) := {a | ∃ u ∈ U, ∃ b ∈ S, a = u • b.map φ}
  have main := det_one_sub_smul_mem_of_nilpotent U (π X) (n + 1) ht S' (by
      rintro _ ⟨u, hu, a, ha, rfl⟩ _ ⟨v, hv, b, hb, rfl⟩
      refine ⟨u * v, U.mul_mem hu hv, a * b, hmul a ha b hb, ?_⟩
      rw [Matrix.map_mul, smul_mul_smul_comm]) (by
      rintro _ ⟨u, hu, a, ha, rfl⟩
      exact ⟨π X * u, U.mul_mem htU hu, a, ha, by rw [smul_smul]⟩) (by
      rintro _ ⟨u, hu, a, ha, rfl⟩
      rw [eval₂_charpolyRev, eval₂_eq_sum, Polynomial.sum]
      refine U.sum_mem fun j _ => U.mul_mem (hφ _ ?_) (U.pow_mem hu _)
      rw [← reverse_charpoly, coeff_reverse]
      exact hchar a ha _)
    ((∑ k ∈ F, c k • s k).map φ) (by
      have : (∑ k ∈ F, c k • s k).map φ = ∑ k ∈ F, φ (c k) • (s k).map φ := by
        ext i j
        simp [Matrix.sum_apply]
      rw [this]
      exact sum_mem fun k _ => AddSubmonoid.subset_closure ⟨_, hφ _ (hc k), _, hs k, rfl⟩)
  set B := ∑ k ∈ F, c k • s k
  rw [eval₂_charpolyRev] at main
  have h1 : B.charpolyRev.eval₂ φ (π X) = π B.charpolyRev := by
    rw [← Polynomial.hom_eval₂, eval₂_C_X]
  rw [h1] at main
  obtain ⟨p, hp⟩ := main
  have h2 : X ^ (n + 1) ∣ p.map T.subtype - B.charpolyRev :=
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hp)
  have h3 := X_pow_dvd_iff.1 h2 n (by omega)
  rw [coeff_sub, sub_eq_zero, coeff_map, ← reverse_charpoly, coeff_reverse,
    charpoly_natDegree_eq_dim, ← hn, revAt_le le_rfl, Nat.sub_self] at h3
  rw [det_eq_sign_charpoly_coeff, ← h3]
  exact T.mul_mem (T.pow_mem (T.neg_mem T.one_mem) _) (p.coeff n).2

end Amitsur

theorem coeff_det_generic_sum_mem_of_charpoly_coeff_mem :
    ∀ {O X G : Type} [CommRing O] [Monoid G] (T : Subalgebra O (X → O)) (n : ℕ)
      (r : X → G →* Matrix (Fin n) (Fin n) O),
      (∀ g j, (fun x => (r x g).charpoly.coeff j) ∈ T) →
      ∀ (m : ℕ) (g : Fin m → G) (d : Fin m →₀ ℕ),
        (fun x => MvPolynomial.coeff d (Matrix.det (∑ k,
          (MvPolynomial.X k : MvPolynomial (Fin m) O) • (r x (g k)).map MvPolynomial.C))) ∈ T := by
  intro O X G _ _ T n r h m g d
  let ρ : G → Matrix (Fin n) (Fin n) (X → O) := fun a => Matrix.of fun i j x => r x a i j
  have hρx : ∀ a x, (ρ a).map (Pi.evalRingHom (fun _ : X => O) x) = r x a := by
    intro a x; ext i j; simp [ρ]
  have hρ : ∀ a b, ρ (a * b) = ρ a * ρ b := by
    intro a b
    ext i j x
    simp [ρ, Matrix.mul_apply]
  have hch : ∀ a j, (ρ a).charpoly.coeff j ∈ T := by
    intro a j
    convert h a j using 1
    funext x
    rw [← hρx, Matrix.charpoly_map, Polynomial.coeff_map]
    rfl
  let T' : Subring (MvPolynomial (Fin m) (X → O)) :=
    (MvPolynomial.map (σ := Fin m) T.toSubring.subtype).range
  have main := Amitsur.det_sum_smul_mem T'
    (Set.range fun a => (ρ a).map (MvPolynomial.C (σ := Fin m))) (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ⟨a * b, by simp only [hρ, Matrix.map_mul]⟩) (by
      rintro _ ⟨a, rfl⟩ j
      rw [Matrix.charpoly_map, Polynomial.coeff_map]
      exact ⟨MvPolynomial.C ⟨_, hch a j⟩, MvPolynomial.map_C _ _⟩)
    Finset.univ (fun k => MvPolynomial.X k) (fun k => (ρ (g k)).map MvPolynomial.C)
    (fun k => ⟨MvPolynomial.X k, by simp⟩) (fun k => ⟨g k, rfl⟩)
  obtain ⟨p, hp⟩ := main
  have h1 : MvPolynomial.coeff d (MvPolynomial.map T.toSubring.subtype p) ∈ T := by
    rw [MvPolynomial.coeff_map]
    exact (MvPolynomial.coeff d p).2
  rw [hp] at h1
  convert h1 using 1
  funext x
  change _ = Pi.evalRingHom (fun _ : X => O) x (MvPolynomial.coeff d _)
  rw [← MvPolynomial.coeff_map, RingHom.map_det]
  congr 2
  ext1 i j
  simp [Matrix.sum_apply, ρ]

end GlobalTheory
