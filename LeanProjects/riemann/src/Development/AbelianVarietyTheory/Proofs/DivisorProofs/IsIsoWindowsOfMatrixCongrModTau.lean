import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrobeniusSemilinearEquationExistsUniqueStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WindowIso

section Gen

variable {B : Type} [CommRing B] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def lft (σ : B →+* B) (M : Matrix ι ι B) : ℕ → Matrix ι ι B
  | 0 => 1
  | n + 1 => M * (lft σ M n).map σ

noncomputable def rgt (σ : B →+* B) (N : Matrix ι ι B) : ℕ → Matrix ι ι B
  | 0 => 1
  | n + 1 => (rgt σ N n).map σ * N

theorem iter_vec (σ : B →+* B) (M : Matrix ι ι B) (n : ℕ) (w : ι → B) :
    (fun w : ι → B => M.mulVec fun j => σ (w j))^[n] w =
      (lft σ M n).mulVec fun j => σ^[n] (w j) := by
  induction n with
  | zero => simp [lft]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, lft, ← Matrix.mulVec_mulVec]
    congr 1
    funext j
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Function.iterate_succ_apply']

theorem iter_mat (σ : B →+* B) (M N : Matrix ι ι B) (n : ℕ) (Y : Matrix ι ι B) :
    (fun Y : Matrix ι ι B => M * Y.map σ * N)^[n] Y =
      lft σ M n * Y.map σ^[n] * rgt σ N n := by
  induction n with
  | zero => simp [lft, rgt]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, lft, rgt, Matrix.map_mul, Matrix.map_mul, Matrix.map_map]
    rw [Function.iterate_succ']
    simp only [Matrix.mul_assoc]

noncomputable def kron (M N : Matrix ι ι B) : Matrix (ι × ι) (ι × ι) B :=
  Matrix.of fun x y => M x.1 y.1 * N y.2 x.2

theorem kron_mulVec (σ : B →+* B) (M N Y : Matrix ι ι B) (x : ι × ι) :
    (kron M N).mulVec (fun y => σ (Y y.1 y.2)) x = (M * Y.map σ * N) x.1 x.2 := by
  simp only [kron, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem kron_iter (σ : B →+* B) (M N : Matrix ι ι B) (n : ℕ) (v : ι × ι → B) (x : ι × ι) :
    (fun w : ι × ι → B => (kron M N).mulVec fun j => σ (w j))^[n] v x =
      (lft σ M n * (Matrix.of fun j m => v (j, m)).map σ^[n] * rgt σ N n) x.1 x.2 := by
  rw [← iter_mat]
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have : (fun w : ι × ι → B => (kron M N).mulVec fun j => σ (w j))^[n] v =
        fun y => ((fun Y : Matrix ι ι B => M * Y.map σ * N)^[n] (Matrix.of fun j m => v (j, m))) y.1 y.2 :=
      funext ih
    rw [this, kron_mulVec]

end Gen

end GlobalTheory.WindowIso

namespace GlobalTheory.WindowIso

section Nil

theorem isNil_kron {B O ι : Type} [CommRing B] [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι]
    (θ : B →+* O) (σ : B →+* B) (M N : Matrix ι ι B) (h : IsNil θ σ M) : IsNil θ σ (kron M N) := by
  obtain ⟨n, hn⟩ := h
  have hL : ∀ i j, θ (lft σ M n i j) ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    have h1 := hn (Pi.single j 1) i
    rw [iter_vec] at h1
    have h2 : (fun m => σ^[n] ((Pi.single j (1 : B) : ι → B) m)) = Pi.single j 1 := by
      funext m
      by_cases hm : m = j
      · subst hm; simp [Function.iterate_fixed (map_one σ)]
      · simp [hm, Function.iterate_fixed (map_zero σ)]
    rw [h2] at h1
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact (IsLocalRing.mem_maximalIdeal _).2 h1
  refine ⟨n, fun v x => ?_⟩
  rw [kron_iter]
  refine (IsLocalRing.mem_maximalIdeal _).1 ?_
  simp only [Matrix.mul_apply, map_sum, map_mul]
  exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun j _ =>
    Ideal.mul_mem_right _ _ (hL _ _))

theorem isNil_lift {A B O ι : Type} [CommRing A] [CommRing B] [CommRing O] [Fintype ι]
    (θB : B →+* O) (σB : B →+* B) (θA : A →+* O) (φ : A →+* A) (a : A →+* B) (I : Ideal B)
    (hθ : ∀ x, θB (a x) = θA x) (hσ : ∀ x, σB (a x) = a (φ x)) (hI : ∀ x ∈ I, θB x = 0)
    (hσI : ∀ x ∈ I, σB x ∈ I) (K : Matrix ι ι B) (KA : Matrix ι ι A)
    (hK : ∀ i j, K i j - a (KA i j) ∈ I) (h : IsNil θB σB K) : IsNil θA φ KA := by
  obtain ⟨n, hn⟩ := h
  have key : ∀ (m : ℕ) (v : ι → A) (i : ι),
      (fun w : ι → B => K.mulVec fun j => σB (w j))^[m] (fun j => a (v j)) i -
        a ((fun w : ι → A => KA.mulVec fun j => φ (w j))^[m] v i) ∈ I := by
    intro m v
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      set w := (fun w : ι → B => K.mulVec fun j => σB (w j))^[m] (fun j => a (v j))
      set u := (fun w : ι → A => KA.mulVec fun j => φ (w j))^[m] v
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun j _ => ?_
      have e : K i j * σB (w j) - a (KA i j) * a (φ (u j)) =
          (K i j - a (KA i j)) * σB (w j) + a (KA i j) * σB (w j - a (u j)) := by
        rw [map_sub, hσ]; ring
      rw [e]
      exact I.add_mem (I.mul_mem_right _ (hK i j)) (I.mul_mem_left _ (hσI _ (ih j)))
  refine ⟨n, fun v i => ?_⟩
  have h1 := hn (fun j => a (v j)) i
  have h2 := hI _ (key n v i)
  rw [map_sub, sub_eq_zero, hθ] at h2
  rwa [h2] at h1

end Nil

section Frame

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} (F : BFrame ε)

theorem p_cancel {x y : F.B} (h : (p : F.B) * x = p * y) : x = y := by
  apply F.frame.inj
  have h' := congrArg (algebraMap F.B F.Q) h
  simp only [map_mul, map_natCast] at h'
  exact F.frame.unit_p.mul_left_cancel h'

theorem σ_τ : F.σ F.τ = p * F.τ := by
  apply p_cancel F
  have h1 : (p : F.B) * F.σ F.τ = F.σ (p * F.τ) := by rw [map_mul, map_natCast]
  rw [h1, F.p_τ, F.σ_a]
  set x : Ainf p O := WittVector.teichmuller p ε
  have hφ : WittVector.frobenius (Sandwich.mu ε) = (∑ i ∈ Finset.range p, x ^ i) * (x - 1) := by
    rw [geom_sum_mul, Sandwich.mu, map_sub, map_one, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_def, map_pow]
  have hd : x - 1 ∣ (∑ i ∈ Finset.range p, x ^ i) - p := by
    have : (∑ i ∈ Finset.range p, x ^ i) - p = ∑ i ∈ Finset.range p, (x ^ i - 1 ^ i) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    exact Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow x 1 i
  obtain ⟨w, hw⟩ := hd
  have hS : (∑ i ∈ Finset.range p, x ^ i) = p + (x - 1) * w := by rw [← hw]; ring
  rw [hφ, hS, map_mul, map_add, map_mul, map_natCast, show x - 1 = Sandwich.mu ε from rfl, ← F.p_τ]
  linear_combination ((p : F.B) * p * F.a w) * F.τ_sq

theorem θ_τ (hε : IsPrimitiveSystem ε) : F.θ F.τ = 0 := by
  apply F.frame.sat
  rw [← map_natCast F.θ p, ← map_mul, F.p_τ, F.θ_a, Sandwich.mu, map_sub, map_one,
    WittVector.fontaineTheta_teichmuller]
  have := hε.zeta_zero
  simp only [zeta, Function.iterate_zero, id] at this
  rw [this, sub_self]

end Frame

end GlobalTheory.WindowIso

namespace GlobalTheory.WindowIso

theorem window_iso : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U U' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsUnit U' → (∀ i j, F.τ ∣ U i j - U' i j) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → ∃ X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) ∧ X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U U' hU _ hUU' hnil
  classical
  haveI : Nontrivial O := ⟨⟨p, 1, fun h => (Fact.out : ¬IsUnit (p : O)) (h ▸ isUnit_one)⟩⟩
  haveI : IsLocalRing O := by
    refine IsLocalRing.of_nonunits_add fun x y hx hy => ?_
    rw [mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one] at hx hy ⊢
    have hx' := lt_of_le_of_ne (hv.map_le_one x) hx
    have hy' := lt_of_le_of_ne (hv.map_le_one y) hy
    rw [map_add]
    exact ne_of_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt hx' hy'))
  set P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B := blk d k (p : F.B) 1 with hP
  set Pd : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B := blk d k 1 (p : F.B) with hPd
  have hPP : Pd * P = (p : F.B) • 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hP, hPd, blk, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
  have hUi : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U ((Matrix.isUnit_iff_isUnit_det U).1 hU)
  choose E hE using hUU'
  set M := U * P with hM
  set N := Pd * U⁻¹ with hN
  set c := Matrix.of E * U⁻¹ with hc
  set K := kron M N with hK
  set I : Ideal F.B := Ideal.span {F.τ} with hI
  have hσI : ∀ x ∈ I, F.σ x ∈ I := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, σ_τ F]
    exact Ideal.mem_span_singleton'.2 ⟨F.σ y * p, by ring⟩
  have hθI : ∀ x ∈ I, F.θ x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, θ_τ F hε, mul_zero]
  have hτI : ∀ x ∈ I, F.τ * x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    linear_combination y * F.τ_sq
  choose g h hg using F.gen
  have hgI : ∀ b, b - F.a (g b) ∈ I := fun b => by
    rw [show b - F.a (g b) = F.a (h b) * F.τ by linear_combination hg b]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  set KA : Matrix (_ × _) (_ × _) (Ainf p O) := Matrix.of fun x y => g (K x y) with hKA
  have hnilA : IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) KA :=
    isNil_lift F.θ F.σ _ _ F.a I F.θ_a F.σ_a hθI hσI K KA (fun i j => hgI _)
      (isNil_kron F.θ F.σ M N hnil)
  obtain ⟨vA, hvA⟩ := (GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε _ KA hnilA).1 (fun y => g (c y.1 y.2))
  set Z : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B := Matrix.of fun j m => F.a (vA (j, m)) with hZ
  have hΔ : ∀ i l, (Z - M * Z.map F.σ * N - c) i l ∈ I := by
    intro i l
    have h1 := congrArg F.a (hvA (i, l))
    have h2 : F.a ((KA.mulVec fun j => WittVector.frobenius (vA j)) (i, l)) =
        (KA.map F.a).mulVec (fun j => F.σ (F.a (vA j))) (i, l) := by
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul, F.σ_a]
    have h3 : (M * Z.map F.σ * N) i l = K.mulVec (fun y => F.σ (F.a (vA y))) (i, l) :=
      (kron_mulVec F.σ M N Z (i, l)).symm
    rw [map_sub, h2] at h1
    have e : (Z - M * Z.map F.σ * N - c) i l =
        (F.a (vA (i, l)) - (KA.map F.a).mulVec (fun j => F.σ (F.a (vA j))) (i, l) - F.a (g (c i l)))
          - (K - KA.map F.a).mulVec (fun j => F.σ (F.a (vA j))) (i, l) + (F.a (g (c i l)) - c i l) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, h3, Matrix.sub_mulVec, Pi.sub_apply]
      simp only [hZ, Matrix.of_apply]
      ring
    rw [e, h1, sub_self, zero_sub]
    refine I.add_mem (I.neg_mem ?_) ?_
    · simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun y _ => I.mul_mem_right _ (by simpa [hKA] using hgI (K (i, l) y))
    · have := I.neg_mem (hgI (c i l))
      rwa [neg_sub] at this
  set R := Z * (U * P) - (p : F.B) • (M * Z.map F.σ) - Matrix.of E * P with hR
  have hDR : (Z - M * Z.map F.σ * N - c) * (U * P) = R := by
    have hN' : N * (U * P) = (p : F.B) • 1 := by
      rw [hN, Matrix.mul_assoc, ← Matrix.mul_assoc U⁻¹ U P, hUi, Matrix.one_mul, hPP]
    have hc' : c * (U * P) = Matrix.of E * P := by
      rw [hc, Matrix.mul_assoc, ← Matrix.mul_assoc U⁻¹ U P, hUi, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc (M * Z.map F.σ), hN', hc', Matrix.mul_smul,
      Matrix.mul_one]
  have hR0 : F.τ • R = 0 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, ← hDR]
    apply hτI
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun m _ => I.mul_mem_right _ (hΔ i m)
  refine ⟨1 + F.τ • Z, fun i j => ⟨Z i j, by simp⟩, ?_⟩
  have hU' : U' = U - F.τ • Matrix.of E := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination -(hE i j)
  have hXσ : (1 + F.τ • Z).map F.σ = 1 + ((p : F.B) * F.τ) • Z.map F.σ := by
    ext i j
    simp [Matrix.one_apply, apply_ite F.σ, σ_τ F]
  rw [hU', hXσ, ← sub_eq_zero]
  have e : (1 + F.τ • Z) * ((U - F.τ • Matrix.of E) * P) - U * P * (1 + ((p : F.B) * F.τ) • Z.map F.σ) =
      F.τ • R - (F.τ * F.τ) • (Z * (Matrix.of E * P)) := by
    simp only [hR, hM, mul_add, add_mul, mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, smul_sub, smul_smul]
    module
  rw [e, hR0, F.τ_sq, zero_smul, sub_zero]

end GlobalTheory.WindowIso
