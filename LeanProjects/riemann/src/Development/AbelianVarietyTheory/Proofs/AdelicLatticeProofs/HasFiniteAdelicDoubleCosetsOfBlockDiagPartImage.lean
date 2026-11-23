import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosurePointsIsGroupStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatMemRatZariskiClosurePointsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BlockDiagPartOfRatIdempotentOneAndMulOfTriangulaStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPolynomialSectionBlockDiagonalRational
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteIntegralCosetsOfBoundedDenominator
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma exists_nat_mul_ev_mem {R : Type} [CommRing R] [Algebra ℚ R]
    (R₀ : Subring R) (f : MvPolynomial (ι × ι) ℚ) : ∃ N : ℕ, 0 < N ∧
      ∀ u : Matrix ι ι R, (∀ i j, u i j ∈ R₀) → (N : R) * _root_.GlobalTheory.ClassFin.ev f u ∈ R₀ := by
  induction f using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, q.pos, fun u _ => ?_⟩
    have h : (q.den : R) * _root_.GlobalTheory.ClassFin.ev (MvPolynomial.C q) u = (q.num : R) := by
      simp only [_root_.GlobalTheory.ClassFin.ev, MvPolynomial.aeval_C]
      rw [← map_natCast (algebraMap ℚ R), ← map_mul,
        show (q.den : ℚ) * q = q.num by rw [mul_comm, Rat.mul_den_eq_num], map_intCast]
    rw [h]
    exact intCast_mem R₀ _
  | add f g hf hg =>
    obtain ⟨N₁, hN₁, h₁⟩ := hf
    obtain ⟨N₂, hN₂, h₂⟩ := hg
    refine ⟨N₁ * N₂, Nat.mul_pos hN₁ hN₂, fun u hu => ?_⟩
    have h : ((N₁ * N₂ : ℕ) : R) * _root_.GlobalTheory.ClassFin.ev (f + g) u =
        (N₂ : R) * ((N₁ : R) * _root_.GlobalTheory.ClassFin.ev f u) +
          (N₁ : R) * ((N₂ : R) * _root_.GlobalTheory.ClassFin.ev g u) := by
      simp only [_root_.GlobalTheory.ClassFin.ev, map_add]
      push_cast
      ring
    rw [h]
    exact R₀.add_mem (R₀.mul_mem (natCast_mem R₀ _) (h₁ u hu))
      (R₀.mul_mem (natCast_mem R₀ _) (h₂ u hu))
  | mul_X f n hf =>
    obtain ⟨N, hN, h⟩ := hf
    refine ⟨N, hN, fun u hu => ?_⟩
    have h' : (N : R) * _root_.GlobalTheory.ClassFin.ev (f * MvPolynomial.X n) u =
        ((N : R) * _root_.GlobalTheory.ClassFin.ev f u) * u n.1 n.2 := by
      simp only [_root_.GlobalTheory.ClassFin.ev, map_mul, MvPolynomial.aeval_X]
      ring
    rw [h']
    exact R₀.mul_mem (h u hu) (hu _ _)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma exists_nat_mul_ev_section_mem {R : Type} [CommRing R] [Algebra ℚ R]
    (R₀ : Subring R) (b : ι → ι → MvPolynomial (ι × ι) ℚ) : ∃ N : ℕ, 0 < N ∧
      ∀ u : Matrix ι ι R, (∀ i j, u i j ∈ R₀) →
        ∀ i j, (N : R) * _root_.GlobalTheory.ClassFin.ev (b i j) u ∈ R₀ := by
  choose N hN h using fun p : ι × ι => exists_nat_mul_ev_mem R₀ (b p.1 p.2)
  refine ⟨∏ p, N p, Finset.prod_pos fun p _ => hN p, fun u hu i j => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ (i, j))
  have h' : ((N (i, j) * m : ℕ) : R) * _root_.GlobalTheory.ClassFin.ev (b i j) u =
      (m : R) * ((N (i, j) : R) * _root_.GlobalTheory.ClassFin.ev (b i j) u) := by
    push_cast
    ring
  rw [hm, h']
  exact R₀.mul_mem (natCast_mem R₀ m) (h (i, j) u hu)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_nat_mul_rat_eq_int {κ : Type} [Fintype κ] (q : κ → ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ k, ∃ z : ℤ, (M : ℚ) * q k = z := by
  refine ⟨∏ k, (q k).den, Finset.prod_pos fun k _ => (q k).pos, fun k => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun k => (q k).den) (Finset.mem_univ k)
  refine ⟨m * (q k).num, ?_⟩
  rw [hm]
  push_cast
  calc ((q k).den : ℚ) * m * q k = m * (q k * (q k).den) := by ring
    _ = m * (q k).num := by rw [Rat.mul_den_eq_num]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma exists_nat_mul_linExt_mem {R : Type} [CommRing R] [Algebra ℚ R]
    (R₀ : Subring R) (c : ι × ι → ι × ι → ℚ) : ∃ K : ℕ, 0 < K ∧
      ∀ A : Matrix ι ι R, (∀ i j, A i j ∈ R₀) →
        ∀ i j, (K : R) * _root_.GlobalTheory.ClassFin.linExt c A i j ∈ R₀ := by
  obtain ⟨K, hK, hz⟩ := exists_nat_mul_rat_eq_int (fun p : (ι × ι) × (ι × ι) => c p.1 p.2)
  refine ⟨K, hK, fun A hA i j => ?_⟩
  simp only [_root_.GlobalTheory.ClassFin.linExt, Matrix.of_apply]
  rw [Finset.mul_sum]
  refine R₀.sum_mem fun kl _ => ?_
  obtain ⟨z, hz'⟩ := hz ((i, j), kl)
  have hz'' : (K : ℚ) * c (i, j) kl = z := hz'
  rw [← mul_assoc, ← map_natCast (algebraMap ℚ R) K, ← map_mul, hz'', map_intCast]
  exact R₀.mul_mem (intCast_mem R₀ z) (hA _ _)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma matrix_mul_mem_subring_of_mem {R : Type} [CommRing R] (R₀ : Subring R) {A B : Matrix ι ι R}
    (hA : ∀ i j, A i j ∈ R₀) (hB : ∀ i j, B i j ∈ R₀) : ∀ i j, (A * B) i j ∈ R₀ :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact R₀.sum_mem fun k _ => R₀.mul_mem (hA i k) (hB k j)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma exists_finset_integral_classes {R : Type} [CommRing R] [Algebra ℚ R]
    (R₀ : Subring R) (S : Set (Matrix ι ι R)) (hone : 1 ∈ S)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) (hadj : ∀ x ∈ S, x.adjugate ∈ S)
    (hdet : ∀ x ∈ S, x.det = 1)
    (hi : ∀ M : ℕ, 0 < M → ∀ r ∈ R₀, ∃ z : ℤ, ∃ a ∈ R₀, r = (z : R) + (M : R) * a)
    (hunit : ∀ N : ℕ, 0 < N → IsUnit (N : R)) (N : ℕ) (hN : 0 < N) :
    ∃ F : Finset (Matrix ι ι R), (∀ t ∈ F, t ∈ S) ∧ ∀ w ∈ S, (∀ i j, (N : R) * w i j ∈ R₀) →
      ∃ t ∈ F, ∃ p ∈ S, (∀ i j, p i j ∈ R₀) ∧ w = t * p := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d = Fintype.card ι - 1 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = N * N ^ d := ⟨_, rfl⟩
  have hL0 : 0 < L := hL ▸ Nat.mul_pos hN (pow_pos hN d)
  haveI : NeZero L := ⟨hL0.ne'⟩
  have hLR : (L : R) = (N : R) * (N : R) ^ d := by rw [hL]; push_cast; ring
  let Cls : (ι → ι → ZMod L) → Matrix ι ι R → Prop := fun c w => w ∈ S ∧
    ∀ i j, ∃ z : ℤ, ∃ a ∈ R₀, (z : ZMod L) = c i j ∧ (N : R) * w i j = z + (L : R) * a
  refine ⟨Finset.univ.image (fun c => if h : ∃ w, Cls c w then h.choose else 1), ?_, ?_⟩
  · intro t ht
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 ht
    split_ifs with h
    · exact h.choose_spec.1
    · exact hone
  · intro w hw hwN
    choose z a ha hza using fun i j => hi L hL0 _ (hwN i j)
    have hc : ∃ w', Cls (fun i j => (z i j : ZMod L)) w' :=
      ⟨w, hw, fun i j => ⟨z i j, a i j, ha i j, rfl, hza i j⟩⟩
    refine ⟨hc.choose, Finset.mem_image.2 ⟨_, Finset.mem_univ _, dif_pos hc⟩, ?_⟩
    obtain ⟨htS, ht⟩ := hc.choose_spec
    obtain ⟨t, htdef⟩ : ∃ t, t = hc.choose := ⟨_, rfl⟩
    rw [← htdef] at htS ht ⊢
    have hD : ∀ i j, ∃ D ∈ R₀, w i j = t i j + (N : R) ^ d * D := by
      intro i j
      obtain ⟨z', a', ha', hz', hza'⟩ := ht i j
      obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub z' (z i j) L).1 hz'
      have hk' : ((z i j : ℤ) : R) - (z' : R) = (L : R) * k := by
        have h := congrArg (Int.cast : ℤ → R) hk
        push_cast at h
        exact h
      refine ⟨k + a i j - a', R₀.sub_mem (R₀.add_mem (intCast_mem R₀ k) (ha i j)) ha', ?_⟩
      apply (hunit N hN).mul_left_cancel
      rw [mul_add, hza i j, hza']
      linear_combination hk' + ((k : R) + a i j - a') * hLR
    choose D hDm hDeq using hD
    have hw' : w = t + (N : R) ^ d • Matrix.of D := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      exact hDeq i j
    have htN : ∀ i j, ((N : R) • t) i j ∈ R₀ := fun i j => by
      obtain ⟨z', a', ha', -, hza'⟩ := ht i j
      rw [Matrix.smul_apply, smul_eq_mul, hza']
      exact R₀.add_mem (intCast_mem R₀ z') (R₀.mul_mem (natCast_mem R₀ L) ha')
    have hp : t.adjugate * w = 1 + ((N : R) • t).adjugate * Matrix.of D := by
      rw [hw', Matrix.mul_add, Matrix.adjugate_mul, hdet t htS, one_smul, Matrix.adjugate_smul,
        ← hd, Matrix.mul_smul, Matrix.smul_mul]
    refine ⟨t.adjugate * w, hmul _ (hadj _ htS) _ hw, fun i j => ?_, ?_⟩
    · rw [hp, Matrix.add_apply]
      refine R₀.add_mem ?_ (matrix_mul_mem_subring_of_mem R₀ (_root_.GlobalTheory.ClassFin.adjugate_entry_mem_subring R₀ _ htN) hDm i j)
      rw [Matrix.one_apply]
      split_ifs
      · exact R₀.one_mem
      · exact R₀.zero_mem
    · rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet t htS, one_smul, Matrix.one_mul]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma idempotent_block_mul_of_upper {A : Type*} [Ring A] (E x y : A) (hE : E * E = E)
    (hx : (1 - E) * x * E = 0) (hy : (1 - E) * y * E = 0) :
    E * (x * y) * E + (1 - E) * (x * y) * (1 - E) =
      (E * x * E + (1 - E) * x * (1 - E)) * (E * y * E + (1 - E) * y * (1 - E)) := by
  have h0 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h0' : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h1 : (1 - E) - (1 - E) * (1 - E) = 0 := by
    have h : (1 - E) * (1 - E) = 1 - E := by rw [sub_mul, one_mul, h0, sub_zero]
    rw [h, sub_self]
  have h2 : E - E * E = 0 := by rw [hE, sub_self]
  rw [← sub_eq_zero]
  have key : E * (x * y) * E + (1 - E) * (x * y) * (1 - E) -
      (E * x * E + (1 - E) * x * (1 - E)) * (E * y * E + (1 - E) * y * (1 - E)) =
      E * x * ((1 - E) * y * E) + ((1 - E) * x * E) * y * (1 - E) + E * x * (E - E * E) * y * E
        + (1 - E) * x * ((1 - E) - (1 - E) * (1 - E)) * y * (1 - E)
        - E * x * (E * (1 - E)) * y * (1 - E) - (1 - E) * x * ((1 - E) * E) * y * E := by
    noncomm_ring
  rw [key, hy, hx, h2, h1, h0, h0']
  simp

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma blk_mul_of_upper {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ)
    (he : e * e = e) (x y : Matrix ι ι R)
    (hx : (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0)
    (hy : (1 - e.map (algebraMap ℚ R)) * y * e.map (algebraMap ℚ R) = 0) :
    _root_.GlobalTheory.ClassFin.blk e (x * y) =
      _root_.GlobalTheory.ClassFin.blk e x * _root_.GlobalTheory.ClassFin.blk e y :=
  idempotent_block_mul_of_upper _ x y (by rw [← Matrix.map_mul, he]) hx hy

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma idempotent_block_one {A : Type*} [Ring A] (E : A) (hE : E * E = E) :
    E * 1 * E + (1 - E) * 1 * (1 - E) = 1 := by
  have h : E * 1 * E + (1 - E) * 1 * (1 - E) = 1 + 2 * (E * E - E) := by noncomm_ring
  rw [h, hE, sub_self, mul_zero, add_zero]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma blk_one_of_idempotent {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ)
    (he : e * e = e) : _root_.GlobalTheory.ClassFin.blk e (1 : Matrix ι ι R) = 1 :=
  idempotent_block_one _ (by rw [← Matrix.map_mul, he])

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma blk_map_algebraMap_eq_map_blk {R : Type} [CommRing R] [Algebra ℚ R] (e g : Matrix ι ι ℚ) :
    _root_.GlobalTheory.ClassFin.blk e (g.map (algebraMap ℚ R)) =
      (_root_.GlobalTheory.ClassFin.blk e g).map (algebraMap ℚ R) := by
  unfold _root_.GlobalTheory.ClassFin.blk
  simp [Matrix.map_mul, Matrix.map_add, Matrix.map_sub, Matrix.map_one]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma linExt_add {R : Type} [CommRing R] [Algebra ℚ R] (c : ι × ι → ι × ι → ℚ)
    (X Y : Matrix ι ι R) : _root_.GlobalTheory.ClassFin.linExt c (X + Y) =
      _root_.GlobalTheory.ClassFin.linExt c X + _root_.GlobalTheory.ClassFin.linExt c Y := by
  ext i j
  simp only [_root_.GlobalTheory.ClassFin.linExt, Matrix.of_apply, Matrix.add_apply, mul_add,
    Finset.sum_add_distrib]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma linExt_smul {R : Type} [CommRing R] [Algebra ℚ R] (c : ι × ι → ι × ι → ℚ)
    (k : R) (X : Matrix ι ι R) : _root_.GlobalTheory.ClassFin.linExt c (k • X) =
      k • _root_.GlobalTheory.ClassFin.linExt c X := by
  ext i j
  simp only [_root_.GlobalTheory.ClassFin.linExt, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma linExt_map_algebraMap {R : Type} [CommRing R] [Algebra ℚ R] (c : ι × ι → ι × ι → ℚ)
    (X : Matrix ι ι ℚ) : (_root_.GlobalTheory.ClassFin.linExt c X).map (algebraMap ℚ R) =
      _root_.GlobalTheory.ClassFin.linExt c (X.map (algebraMap ℚ R)) := by
  ext i j
  simp [_root_.GlobalTheory.ClassFin.linExt, map_sum, map_mul]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in

theorem _root_.GlobalTheory.ClassFin.cf_of_cf_blk_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), _root_.GlobalTheory.ClassFin.IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → _root_.GlobalTheory.ClassFin.AdelicPair R R₀ → _root_.GlobalTheory.ClassFin.CF (_root_.GlobalTheory.ClassFin.blk e '' Γ) R R₀ → _root_.GlobalTheory.ClassFin.CF Γ R R₀ := by
  intro ι _ _ Γ e R _ _ R₀ hΓ he hblock hR hCF
  classical
  obtain ⟨hone, hmul, hadj, hdet⟩ :=
    _root_.GlobalTheory.ClassFin.pts_group ι Γ hΓ.toIsPre R
  obtain ⟨-, hmulq, -, -⟩ := _root_.GlobalTheory.ClassFin.pts_group ι Γ hΓ.toIsPre ℚ
  obtain ⟨c, b, hsec⟩ := _root_.GlobalTheory.ClassFin.PolySection.exists_section ι Γ e hΓ he hblock
  obtain ⟨hU, hcc, hker, htri, hσ⟩ := hsec R
  obtain ⟨hUq, -, -, -, hσq⟩ := hsec ℚ
  obtain ⟨hi, hii, -⟩ := _root_.GlobalTheory.ClassFin.adelicPair_elementary R R₀ hR
  have hunit : ∀ N : ℕ, 0 < N → IsUnit (N : R) := fun N hN => by
    have h := (isUnit_iff_ne_zero.2 (by positivity : (N : ℚ) ≠ 0)).map (algebraMap ℚ R)
    rwa [map_natCast] at h
  obtain ⟨N, hN, hNb⟩ := exists_nat_mul_ev_section_mem (R := R) R₀ b
  obtain ⟨Kc, hKc, hcK⟩ := exists_nat_mul_linExt_mem (R := R) R₀ c
  obtain ⟨F, hFS, hF⟩ :=
    exists_finset_integral_classes R₀ _ hone hmul hadj hdet hi hunit N hN
  obtain ⟨TQ, hTQ, hTQd⟩ := hCF
  let σ : Matrix ι ι R → Matrix ι ι R := fun y => Matrix.of fun i j => _root_.GlobalTheory.ClassFin.ev (b i j) y
  refine ⟨(TQ ×ˢ F).image (fun p => σ p.1 * p.2), ?_, ?_⟩
  · intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs
    rw [Finset.mem_product] at hp
    exact hmul _ (hσ _ (hTQ _ hp.1)).1 _ (hFS _ hp.2)
  intro x hx
  have hinvl : ∀ a ∈ _root_.GlobalTheory.ClassFin.pts Γ R, a.adjugate * a = 1 := fun a ha => by
    rw [Matrix.adjugate_mul, hdet a ha, one_smul]
  have hinvr : ∀ a ∈ _root_.GlobalTheory.ClassFin.pts Γ R, a * a.adjugate = 1 := fun a ha => by
    rw [Matrix.mul_adjugate, hdet a ha, one_smul]
  have hbm : ∀ a ∈ _root_.GlobalTheory.ClassFin.pts Γ R, ∀ a' ∈ _root_.GlobalTheory.ClassFin.pts Γ R,
      _root_.GlobalTheory.ClassFin.blk e (a * a') =
        _root_.GlobalTheory.ClassFin.blk e a * _root_.GlobalTheory.ClassFin.blk e a' :=
    fun a ha a' ha' => blk_mul_of_upper e he a a' (htri a ha).1 (htri a' ha').1
  have hbinv : ∀ a ∈ _root_.GlobalTheory.ClassFin.pts Γ R,
      _root_.GlobalTheory.ClassFin.blk e a.adjugate * _root_.GlobalTheory.ClassFin.blk e a = 1 :=
    fun a ha => by rw [← hbm _ (hadj a ha) _ ha, hinvl a ha, blk_one_of_idempotent e he]
  have hbinv' : ∀ a ∈ _root_.GlobalTheory.ClassFin.pts Γ R,
      _root_.GlobalTheory.ClassFin.blk e a * _root_.GlobalTheory.ClassFin.blk e a.adjugate = 1 :=
    fun a ha => by rw [← hbm _ ha _ (hadj a ha), hinvr a ha, blk_one_of_idempotent e he]
  obtain ⟨γQ, hγQ, s, hs, u, hu, huint, hy⟩ := hTQd _ (htri x hx).2
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : Matrix ι ι ℚ, γ' = Matrix.of fun i j =>
    _root_.GlobalTheory.ClassFin.ev (b i j) γQ := ⟨_, rfl⟩
  obtain ⟨hγ'P, hγ'b⟩ := hσq γQ hγQ
  rw [← hγ'def] at hγ'P hγ'b
  have hγR : γ'.map (algebraMap ℚ R) ∈ _root_.GlobalTheory.ClassFin.pts Γ R :=
    (_root_.GlobalTheory.ClassFin.RatPts.rat_mem_pts ι Γ).2 R _ hγ'P
  have hγRb : _root_.GlobalTheory.ClassFin.blk e (γ'.map (algebraMap ℚ R)) =
      γQ.map (algebraMap ℚ R) := by rw [blk_map_algebraMap_eq_map_blk, hγ'b]
  obtain ⟨hsP, hsb⟩ : σ s ∈ _root_.GlobalTheory.ClassFin.pts Γ R ∧ _root_.GlobalTheory.ClassFin.blk e (σ s) = s :=
    hσ s (hTQ s hs)
  obtain ⟨huP, hub⟩ : σ u ∈ _root_.GlobalTheory.ClassFin.pts Γ R ∧ _root_.GlobalTheory.ClassFin.blk e (σ u) = u :=
    hσ u hu
  obtain ⟨g, hgdef⟩ : ∃ g, g = γ'.map (algebraMap ℚ R) * σ s := ⟨_, rfl⟩
  have hgP : g ∈ _root_.GlobalTheory.ClassFin.pts Γ R := hgdef ▸ hmul _ hγR _ hsP
  have hgb : _root_.GlobalTheory.ClassFin.blk e g = γQ.map (algebraMap ℚ R) * s := by
    rw [hgdef, hbm _ hγR _ hsP, hγRb, hsb]
  obtain ⟨r, hrdef⟩ : ∃ r, r = g.adjugate * x := ⟨_, rfl⟩
  have hrP : r ∈ _root_.GlobalTheory.ClassFin.pts Γ R := hrdef ▸ hmul _ (hadj _ hgP) _ hx
  have hrb : _root_.GlobalTheory.ClassFin.blk e r = u := by
    rw [hrdef, hbm _ (hadj _ hgP) _ hx, hy, ← hgb, ← Matrix.mul_assoc, hbinv g hgP, Matrix.one_mul]
  obtain ⟨n, hndef⟩ : ∃ n, n = r * (σ u).adjugate := ⟨_, rfl⟩
  have hnP : n ∈ _root_.GlobalTheory.ClassFin.pts Γ R := hndef ▸ hmul _ hrP _ (hadj _ huP)
  have hnb : _root_.GlobalTheory.ClassFin.blk e n = 1 := by
    have h := hbinv' _ huP
    rw [hub] at h
    rw [hndef, hbm _ hrP _ (hadj _ huP), hrb]
    exact h
  obtain ⟨m, hmdef⟩ : ∃ m, m = σ s * n * (σ s).adjugate := ⟨_, rfl⟩
  have hmP : m ∈ _root_.GlobalTheory.ClassFin.pts Γ R := hmdef ▸ hmul _ (hmul _ hsP _ hnP) _ (hadj _ hsP)
  have hmb : _root_.GlobalTheory.ClassFin.blk e m = 1 := by
    rw [hmdef, hbm _ (hmul _ hsP _ hnP) _ (hadj _ hsP), hbm _ hsP _ hnP, hnb, Matrix.mul_one,
      hbinv' _ hsP]
  obtain ⟨Y, hY⟩ := hker m hmP hmb
  obtain ⟨K1, hK1, hK1s⟩ := hii (ι × ι) (fun p => σ s p.1 p.2)
  obtain ⟨K2, hK2, hK2s⟩ := hii (ι × ι) (fun p => (σ s).adjugate p.1 p.2)
  have hM : 0 < K2 * Kc * K1 := Nat.mul_pos (Nat.mul_pos hK2 hKc) hK1
  choose q a ha hqa using fun i j => hR.approx (K2 * Kc * K1) hM (Y i j)
  have hYsplit : Y = (Matrix.of q).map (algebraMap ℚ R) + ((K2 * Kc * K1 : ℕ) : R) • Matrix.of a := by
    ext i j
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    exact hqa i j
  obtain ⟨A, hAdef⟩ : ∃ A, A = _root_.GlobalTheory.ClassFin.linExt c ((Matrix.of q).map (algebraMap ℚ R)) :=
    ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = _root_.GlobalTheory.ClassFin.linExt c (Matrix.of a) := ⟨_, rfl⟩
  have hm : m = (1 + A) * (1 + ((K2 * Kc * K1 : ℕ) : R) • C) := by
    rw [hY, hYsplit, linExt_add, linExt_smul, ← hAdef, ← hCdef, mul_add, mul_one, add_mul,
      one_mul, Matrix.mul_smul, hAdef, hCdef, hcc, smul_zero, add_zero, add_assoc]
  obtain ⟨γ, hγdef⟩ : ∃ γ, γ = γ' * (1 + _root_.GlobalTheory.ClassFin.linExt c (Matrix.of q)) := ⟨_, rfl⟩
  have hγ : γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ := hγdef ▸ hmulq _ hγ'P _ (hUq _)
  have hγmap : γ.map (algebraMap ℚ R) = γ'.map (algebraMap ℚ R) * (1 + A) := by
    rw [hγdef, Matrix.map_mul, hAdef, ← linExt_map_algebraMap, Matrix.map_add _ (map_add _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨v, hvdef⟩ : ∃ v, v = (σ s).adjugate * (1 + ((K2 * Kc * K1 : ℕ) : R) • C) * σ s :=
    ⟨_, rfl⟩
  have hvP : v ∈ _root_.GlobalTheory.ClassFin.pts Γ R := by
    have h1 : 1 + ((K2 * Kc * K1 : ℕ) : R) • C ∈ _root_.GlobalTheory.ClassFin.pts Γ R := by
      rw [hCdef, ← linExt_smul]
      exact hU _
    exact hvdef ▸ hmul _ (hmul _ (hadj _ hsP) _ h1) _ hsP
  have hvint : ∀ i j, v i j ∈ R₀ := by
    have hv : v = 1 + ((K2 : R) • (σ s).adjugate) * ((Kc : R) • C) * ((K1 : R) • σ s) := by
      rw [hvdef, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hinvl _ hsP]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      congr 2
      push_cast
      ring
    have hCint : ∀ i j, ((Kc : R) • C) i j ∈ R₀ := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, hCdef]
      exact hcK _ ha i j
    have h2 : ∀ i j, ((K2 : R) • (σ s).adjugate) i j ∈ R₀ := fun i j => hK2s (i, j)
    have h3 : ∀ i j, ((K1 : R) • σ s) i j ∈ R₀ := fun i j => hK1s (i, j)
    intro i j
    rw [hv, Matrix.add_apply]
    refine R₀.add_mem ?_ (matrix_mul_mem_subring_of_mem R₀ (matrix_mul_mem_subring_of_mem R₀ h2 hCint) h3 i j)
    rw [Matrix.one_apply]
    split_ifs
    · exact R₀.one_mem
    · exact R₀.zero_mem
  have hp0P : v * σ u ∈ _root_.GlobalTheory.ClassFin.pts Γ R := hmul _ hvP _ huP
  have hp0N : ∀ i j, (N : R) * (v * σ u) i j ∈ R₀ := fun i j => by
    rw [← smul_eq_mul, ← Matrix.smul_apply, ← Matrix.mul_smul]
    exact matrix_mul_mem_subring_of_mem R₀ hvint (fun i j => hNb u huint i j) i j
  obtain ⟨t, ht, p, hpP, hpint, hp0⟩ := hF _ hp0P hp0N
  refine ⟨γ, hγ, σ s * t, Finset.mem_image.2 ⟨(s, t), Finset.mem_product.2 ⟨hs, ht⟩, rfl⟩,
    p, hpP, hpint, ?_⟩
  have e1 : x = g * r := by rw [hrdef, ← Matrix.mul_assoc, hinvr g hgP, Matrix.one_mul]
  have e2 : r = n * σ u := by rw [hndef, Matrix.mul_assoc, hinvl _ huP, Matrix.mul_one]
  have e3 : σ s * n = m * σ s := by
    rw [hmdef, Matrix.mul_assoc (σ s * n), hinvl _ hsP, Matrix.mul_one]
  have e4 : (1 + ((K2 * Kc * K1 : ℕ) : R) • C) * σ s = σ s * v := by
    rw [hvdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinvr _ hsP, Matrix.one_mul]
  rw [hγmap]
  simp only [Matrix.mul_assoc]
  rw [← hp0, e1, e2, hgdef]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (σ s) n, e3, hm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 + ((K2 * Kc * K1 : ℕ) : R) • C) (σ s), e4]
  simp only [Matrix.mul_assoc]

end GlobalTheory.ClassFin
