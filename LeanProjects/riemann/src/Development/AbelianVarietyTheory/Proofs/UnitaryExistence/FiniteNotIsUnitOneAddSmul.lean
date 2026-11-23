import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdmissibleHarmonicLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPowLeHalfPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsForallAbvSubLt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenusSelfDual

open NumberField IsDedekindDomain Polynomial
open scoped Matrix

section Cayley

variable {M : Type*} [Ring M] [StarRing M]

theorem cayley_skew {u w : M} (hu : star u * u = 1) (hw : (1 + u) * w = 1) (hw' : w * (1 + u) = 1) :
    star ((1 - u) * w) = -((1 - u) * w) ∧ (1 + (1 - u) * w) * (1 + u) = 2 := by
  have e : (1 - u) * w * (1 + u) = 1 - u := by rw [mul_assoc, hw', mul_one]
  refine ⟨?_, by rw [add_mul, e, one_mul, add_add_sub_cancel, one_add_one_eq_two]⟩
  have e' : (1 + star u) * star ((1 - u) * w) = 1 - star u := by
    simpa only [star_mul ((1 - u) * w), star_add, star_sub, star_one] using congrArg star e
  have hs : star w * (1 + star u) = 1 := by
    simpa only [star_mul, star_add, star_one] using congrArg star hw
  have key : (1 + star u) * (star ((1 - u) * w) + (1 - u) * w) * (1 + u) = 0 := by
    rw [mul_add (1 + star u) (star _), e', add_mul, mul_assoc (1 + star u), e]
    calc (1 - star u) * (1 + u) + (1 + star u) * (1 - u) = (1 - star u * u) + (1 - star u * u) := by noncomm_ring
      _ = 0 := by rw [hu, sub_self, add_zero]
  rw [eq_neg_iff_add_eq_zero]
  calc star ((1 - u) * w) + (1 - u) * w
      = (star w * (1 + star u)) * (star ((1 - u) * w) + (1 - u) * w) * ((1 + u) * w) := by
        rw [hs, hw, one_mul, mul_one]
    _ = star w * ((1 + star u) * (star ((1 - u) * w) + (1 - u) * w) * (1 + u)) * w := by
        simp only [mul_assoc]
    _ = 0 := by rw [key, mul_zero, zero_mul]

theorem cayley_unitary {S t : M} (hS : star S = -S) (ht : (1 + S) * t = 1) :
    star (2 * t - 1) * (2 * t - 1) = 1 := by
  have hs : star t * (1 - S) = 1 := by
    simpa only [star_mul, star_add, star_one, hS, ← sub_eq_add_neg] using congrArg star ht
  have e : star (2 * t - 1) = 2 * star t - 1 := by
    rw [two_mul, two_mul, star_sub, star_add, star_one]
  rw [e]
  calc (2 * star t - 1) * (2 * t - 1)
      = 2 * (star t * ((1 + S) * t)) + 2 * (star t * (1 - S) * t) - 2 * star t - 2 * t + 1 := by noncomm_ring
    _ = 1 := by rw [ht, hs]; noncomm_ring

theorem cayley_perturb (N : Subring M) {u γ S D : M} {p k : ℕ} (h2 : ∀ x : M, 2 • x = 0 → x = 0)
    (hu : star u * u = 1) (hS : (1 + S) * (1 + u) = 2) (hγ : (1 + γ) * (1 + (S + (2 * p * k * k) • D)) = 2)
    (hD : D ∈ N) (h₁ : k • (1 + u) ∈ N) (h₂ : k • (1 + star u) ∈ N)
    (hJ : ∀ z ∈ N, ∃ w ∈ N, (1 + p • z) * w = 1) : star u * γ ∈ N := by
  set z := k • (D * (k • (1 + u))) with hz
  have hzN : z ∈ N := nsmul_mem (mul_mem hD h₁) k
  obtain ⟨w, hw, hw1⟩ := hJ z hzN
  have e1 : (1 + γ) * (1 + p • z) = 1 + u := by
    refine sub_eq_zero.1 (h2 _ ?_)
    have a : (1 + (S + (2 * p * k * k) • D)) * (1 + u) = 2 • (1 + p • z) := by
      rw [← add_assoc, add_mul, hS, hz, smul_add, mul_smul_comm, smul_smul, smul_smul, smul_smul, smul_mul_assoc]
      simp
    rw [smul_sub, ← mul_smul_comm, ← a, ← mul_assoc, hγ, two_mul, two_smul, sub_self]
  have e2 : (star u * γ) * (1 + p • z) = 1 + p • z - p • ((k • (1 + star u)) * (D * (k • (1 + u)))) := by
    have b : (k • (1 + star u)) * (D * (k • (1 + u))) = (1 + star u) * z := by
      rw [hz, smul_mul_assoc, mul_smul_comm (k) (1 + star u)]
    rw [b, ← mul_smul_comm]
    generalize p • z = y at e1 ⊢
    calc (star u * γ) * (1 + y) = star u * ((1 + γ) * (1 + y)) - star u * (1 + y) := by noncomm_ring
      _ = star u * u - star u * y := by rw [e1]; noncomm_ring
      _ = _ := by rw [hu]; noncomm_ring
  have e3 : star u * γ = 1 - p • ((k • (1 + star u)) * (D * (k • (1 + u)))) * w := by
    rw [← mul_one (star u * γ), ← congrArg (star u * γ * ·) hw1, ← mul_assoc, e2, sub_mul, hw1]
  rw [e3]
  exact sub_mem (one_mem _) (mul_mem (nsmul_mem (mul_mem h₂ (mul_mem hD h₁)) p) hw)

end Cayley

section Matrices

variable {n : Type} [Fintype n] [DecidableEq n]

theorem exists_inv_one_add_smul {A : Type*} [CommRing A] (O : Subring A) {p : ℕ}
    (hJ : ∀ z ∈ O, ∃ w ∈ O, (1 + p • z) * w = 1) (Z : Matrix n n A) (hZ : Z ∈ O.matrix) :
    ∃ W ∈ (O.matrix : Subring (Matrix n n A)), (1 + p • Z) * W = 1 := by
  let Z' : Matrix n n O := Matrix.of fun i j => ⟨Z i j, hZ i j⟩
  have hd : IsUnit (1 + (p : O) • Z').det := by
    rw [Matrix.det_one_add_smul, add_assoc, sq, ← mul_assoc, ← add_mul, mul_comm, ← nsmul_eq_mul]
    generalize Z'.trace + _ = y
    obtain ⟨w, hw, h⟩ := hJ y y.2
    exact IsUnit.of_mul_eq_one (⟨w, hw⟩ : O) (Subtype.ext h)
  refine ⟨O.subtype.mapMatrix (1 + (p : O) • Z')⁻¹, fun i j => ((1 + (p : O) • Z')⁻¹ i j).2, ?_⟩
  have := congrArg O.subtype.mapMatrix (Matrix.mul_nonsing_inv _ hd)
  rw [map_mul, map_one, Nat.cast_smul_eq_nsmul, map_add, map_one, map_nsmul] at this
  rw [Nat.cast_smul_eq_nsmul]
  exact this

theorem exists_unitary_approx {E : Type*} [Field E] [CharZero E] [StarRing E] {ι : Type*} {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, StarRing (A i)] (φ : ∀ i, E →+* A i) (hφ : ∀ i x, φ i (star x) = star (φ i x))
    (O : ∀ i, Subring (A i)) (hO : ∀ i, ∀ z ∈ O i, star z ∈ O i) {p : ℕ} (hp : p ≠ 0)
    (hJ : ∀ i, ∀ z ∈ O i, ∃ w ∈ O i, (1 + p • z) * w = 1)
    (happ : ∀ z : ∀ i, A i, ∃ x : E, ∀ i, φ i x - z i ∈ O i)
    (hden : ∀ x : E, ∃ k : ℕ, k ≠ 0 ∧ ∀ i, k • φ i x ∈ O i)
    (hdef : ∀ S : Matrix n n E, star S = -S → IsUnit (1 + S))
    (u : ∀ i, Matrix n n (A i)) (hu : ∀ i, star (u i) * u i = 1) (hu1 : ∀ i, IsUnit (1 + u i)) :
    ∃ γ : Matrix n n E, star γ * γ = 1 ∧ ∀ i, star (u i) * γ.map (φ i) ∈ (O i).matrix := by
  have hO' : ∀ i, ∀ Z ∈ ((O i).matrix : Subring (Matrix n n (A i))), star Z ∈ (O i).matrix :=
    fun i Z hZ a b => hO i _ (hZ b a)
  have happ' : ∀ Z : ∀ i, Matrix n n (A i), ∃ X : Matrix n n E, ∀ i, (φ i).mapMatrix X - Z i ∈ (O i).matrix := by
    intro Z
    choose X hX using fun a b => happ fun i => Z i a b
    exact ⟨Matrix.of X, fun i a b => hX a b i⟩
  have hφ' : ∀ i (X : Matrix n n E), (φ i).mapMatrix (star X) = star ((φ i).mapMatrix X) :=
    fun i X => Matrix.ext fun a b => hφ i _
  obtain ⟨k, hk, hku⟩ : ∃ k : ℕ, k ≠ 0 ∧ ∀ i, k • u i ∈ (O i).matrix := by
    obtain ⟨X, hX⟩ := happ' u
    choose d hd hdX using fun ab : n × n => hden (X ab.1 ab.2)
    refine ⟨∏ ab, d ab, Finset.prod_ne_zero_iff.2 fun ab _ => hd ab, fun i => ?_⟩
    rw [← sub_sub_cancel ((φ i).mapMatrix X) (u i), smul_sub]
    refine sub_mem (fun a b => ?_) (nsmul_mem (hX i) _)
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ (a, b))
    rw [hc, mul_comm, mul_smul]
    exact nsmul_mem (hdX (a, b) i) c
  choose w hw using fun i => (hu1 i).exists_right_inv
  have hc := fun i => cayley_skew (hu i) (hw i) (mul_eq_one_comm.1 (hw i))
  set m := 2 * p * k * k with hm
  have hm0 : ((2 * m : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  obtain ⟨Y, hY⟩ := happ' fun i => φ i ((2 * m : ℕ) : E)⁻¹ • ((1 - u i) * w i)
  have hS : star (m • (Y - star Y)) = -(m • (Y - star Y)) := by
    rw [star_nsmul, star_sub, star_star, ← smul_neg, neg_sub]
  obtain ⟨t, ht⟩ := (hdef _ hS).exists_right_inv
  refine ⟨2 * t - 1, cayley_unitary hS ht, fun i => ?_⟩
  have h2 : ∀ x : Matrix n n (A i), 2 • x = 0 → x = 0 := fun x hx => by
    have : φ i 2⁻¹ • 2 • x = x := by
      rw [← Nat.cast_smul_eq_nsmul (A i), smul_smul, ← map_natCast (φ i), ← map_mul]
      simp
    rw [← this, hx, smul_zero]
  refine cayley_perturb (O i).matrix (p := p) (k := k) h2 (hu i) (hc i).2 ?_
    (sub_mem (hY i) (hO' i _ (hY i))) (by rw [smul_add]; exact add_mem (nsmul_mem (one_mem _) _) (hku i))
    (by rw [smul_add, ← star_nsmul]; exact add_mem (nsmul_mem (one_mem _) _) (hO' i _ (hku i)))
    (exists_inv_one_add_smul (O i) (hJ i))
  have e : (1 + (2 * t - 1)) * (1 + m • (Y - star Y)) = 2 := by
    rw [add_sub_cancel, mul_assoc, mul_eq_one_comm.1 ht, mul_one]
  have e' := congrArg (φ i).mapMatrix e
  rw [map_mul, map_add, map_add, map_one, map_ofNat, map_nsmul, map_sub _ Y, hφ'] at e'
  rw [← e']
  congr 2
  rw [star_sub, star_smul, (hc i).1, ← hφ, star_inv₀, star_natCast, ← hm]
  generalize (1 - u i) * w i = S
  have : (2 * m) • φ i ((2 * m : ℕ) : E)⁻¹ • S = S := by
    rw [← Nat.cast_smul_eq_nsmul (A i), smul_smul, ← map_natCast (φ i), ← map_mul, mul_inv_cancel₀ hm0, map_one,
      one_smul]
  rw [← this, this, smul_neg]
  nth_rw 1 [← this]
  generalize φ i ((2 * m : ℕ) : E)⁻¹ • S = T
  rw [two_mul, add_smul]
  simp only [smul_sub, smul_neg]
  abel

theorem finite_not_isUnit_eval {K A : Type*} [Field K] [CommRing A] [IsArtinianRing A] (φ : K →+* A) (f : A[X])
    (hf : f.eval 0 = 1) : {x : K | ¬ IsUnit (f.eval (φ x))}.Finite := by
  refine ((IsArtinianRing.setOf_isMaximal_finite A).biUnion
    (t := fun m => {x : K | f.eval (φ x) ∈ m}) fun m hm => ?_).subset fun x hx => ?_
  · haveI : m.IsMaximal := hm
    have h0 : f.map (Ideal.Quotient.mk m) ≠ 0 := fun h => by
      have := congrArg (eval (Ideal.Quotient.mk m 0)) h
      rw [eval_map_apply, hf, map_one, eval_zero] at this
      exact one_ne_zero this
    refine ((finite_setOf_isRoot h0).preimage
      ((Ideal.Quotient.mk m).comp φ).injective.injOn).subset fun x hx => ?_
    change eval (Ideal.Quotient.mk m (φ x)) _ = 0
    rw [eval_map_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  · obtain ⟨m, hm, h⟩ := exists_max_ideal_of_mem_nonunits hx
    exact Set.mem_biUnion hm h

theorem finite_not_isUnit_one_add_smul {K A : Type*} [Field K] [CommRing A] [IsArtinianRing A] (φ : K →+* A)
    (h : Matrix n n A) : {x : K | ¬ IsUnit (1 + φ x • h)}.Finite := by
  have e : ∀ a : A, (1 + (X : A[X]) • h.map C).det.eval a = (1 + a • h).det := fun a => by
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.one_apply, apply_ite (eval a), mul_comm a]
  simpa only [e, Matrix.isUnit_iff_isUnit_det] using finite_not_isUnit_eval φ _ ((e 0).trans (by simp))

end Matrices

section Local

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus IsLocalRing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_imaginary_integer (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ θ : 𝓞 E, (θ : E) ≠ 0 ∧ cc (θ : E) = -θ := by
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, (x : E) - cc (x : E) ≠ 0 := by
    by_contra h
    push Not at h
    refine IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => ?_)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    have e : ∀ a : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E a :=
      fun a => (sub_eq_zero.1 (h a)).symm
    rw [map_div₀, e, e]; rfl
  refine ⟨x - IsCMField.ringOfIntegersComplexConj E x, by simpa [cc] using hx, ?_⟩
  simp [cc]

theorem exists_sub_mem_locOrder (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (z : ∀ v : T, LocAlg v.1) : ∃ x : E, ∀ v : T, locEmb v.1 x - z v ∈ locOrder v.1 := by
  have app : ∀ a : ∀ v : T, v.1.adicCompletion (maximalRealSubfield E), ∃ x : maximalRealSubfield E, ∀ v : T,
      locEmb v.1 (x : E) - algebraMap _ (LocAlg v.1) (a v) ∈ locOrder v.1 := by
    intro a
    obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 (LocalQuad.denseRange_finite_real (maximalRealSubfield E) T)
      (a, 0) 1 one_pos
    refine ⟨x, fun v => ?_⟩
    have h := (dist_le_pi_dist _ _ v).trans ((le_max_left _ _).trans hx.le)
    rw [dist_comm, dist_eq_norm] at h
    rw [locEmb_coe, ← map_sub]
    exact (locOrder v.1).algebraMap_mem ⟨_, Valued.toNormedField.norm_le_one_iff.1 h⟩
  obtain ⟨θ, h0, hθ⟩ := exists_imaginary_integer E
  choose a b hab using fun v : T => exists_coord v.1 h0 hθ (z v)
  obtain ⟨x, hx⟩ := app a
  obtain ⟨y, hy⟩ := app b
  refine ⟨x + y * θ, fun v => ?_⟩
  convert add_mem (hx v) (mul_mem (hy v) (locEmb_mem_locOrder v.1 θ)) using 1
  rw [hab v, map_add, map_mul]
  ring

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

theorem exists_inv_one_add {p : ℕ} (hp : (p : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal) (z : LocAlg v)
    (hz : z ∈ locOrder v) : ∃ w ∈ locOrder v, (1 + p • z) * w = 1 := by
  haveI : Algebra.IsIntegral (v.adicCompletionIntegers (maximalRealSubfield E)) (locOrder v) :=
    ⟨fun x => (isIntegral_algHom_iff (locOrder v).val Subtype.val_injective).1 (isIntegral_of_mem_locOrder v x.2)⟩
  have : IsUnit (1 + p • (⟨z, hz⟩ : locOrder v)) := by
    by_contra h
    obtain ⟨m, hm, h⟩ := exists_max_ideal_of_mem_nonunits h
    have h1 := eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (R := v.adicCompletionIntegers (maximalRealSubfield E)) m)
    have h2 : (p : v.adicCompletionIntegers (maximalRealSubfield E)) ∈ maximalIdeal _ := by
      rw [mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap (𝓞 (maximalRealSubfield E)) _),
        isUnit_algebraMap_iff]
      exact fun h => h hp
    rw [← h1, Ideal.mem_comap, map_natCast] at h2
    rw [nsmul_eq_mul] at h
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 ((Ideal.add_mem_iff_left _ (m.mul_mem_right _ h2)).1 h))
  obtain ⟨w, hw⟩ := this.exists_right_inv
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

theorem exists_norm_one_isUnit {p : ℕ} (hp0 : p ≠ 0) (hp : (p : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal)
    (h : Matrix (Fin n) (Fin n) (LocAlg v)) :
    ∃ ζ ∈ locOrder v, locConj v ζ * ζ = 1 ∧ IsUnit (1 + ζ • h) := by
  haveI : IsArtinianRing (LocAlg v) := IsArtinianRing.of_finite (v.adicCompletion (maximalRealSubfield E)) _
  obtain ⟨θ, h0, hθ⟩ := exists_imaginary_integer E
  have hc : ∀ k : ℤ, IsCMField.complexConj E (1 + p * (k * θ : E)) = 1 - p * (k * θ) := fun k => by
    rw [map_add, map_one, map_mul, map_mul, map_natCast, map_intCast, show IsCMField.complexConj E θ = -θ from hθ]
    ring
  have hne : ∀ k : ℤ, 1 + p * (k * θ : E) ≠ 0 := fun k hk => by
    have := hc k
    rw [hk, map_zero] at this
    exact two_ne_zero (α := E) (by linear_combination hk - this)
  have hne' : ∀ k : ℤ, 1 - p * (k * θ : E) ≠ 0 := fun k => by
    rw [← hc]; exact (_root_.map_ne_zero _).2 (hne k)
  let f : ℤ → E := fun k => (1 - p * (k * θ)) / (1 + p * (k * θ))
  have hf : Function.Injective f := fun a b hab => by
    rw [div_eq_div_iff (hne a) (hne b)] at hab
    have : (2 * p * θ : E) * (a - b) = 0 := by linear_combination -hab
    have h1 : (2 * p * θ : E) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hp0)) h0
    exact_mod_cast sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h1)
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := (Set.infinite_range_of_injective hf).exists_notMem_finite
    (finite_not_isUnit_one_add_smul (locEmb v) h)
  refine ⟨locEmb v (f k), ?_, ?_, not_not.1 hk⟩
  · have hz : locEmb v (k * θ : E) ∈ locOrder v := by simpa using locEmb_mem_locOrder v (k * θ)
    obtain ⟨w, hw, e⟩ := exists_inv_one_add v hp _ hz
    have : locEmb v (f k) = (1 - p • locEmb v (k * θ : E)) * w := by
      have e' : locEmb v (f k) * (1 + p • locEmb v (k * θ : E)) = 1 - p • locEmb v (k * θ : E) := by
        simpa using congrArg (locEmb v) (div_mul_cancel₀ (1 - p * (k * θ : E)) (hne k))
      rw [← e', mul_assoc, e, mul_one]
    rw [this]
    exact mul_mem (sub_mem (one_mem _) (nsmul_mem hz p)) hw
  · rw [locConj_locEmb, ← map_mul, ← map_one (locEmb v)]
    congr 1
    have := hc (-k)
    simp only [Int.cast_neg, neg_mul, mul_neg, ← sub_eq_add_neg, sub_neg_eq_add] at this
    simp only [cc, f, map_div₀, hc, this]
    rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hne' k) (hne k))]

@[reducible] def locStar : StarRing (LocAlg v) where
  star := locConj v
  star_involutive := locConj_locConj v
  star_mul x y := by rw [map_mul, mul_comm]
  star_add := map_add _

theorem isUnit_one_add_of_skew (S : Matrix (Fin n) (Fin n) E) (hS : star S = -S) : IsUnit (1 + S) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 : (τ.mapMatrix S)ᴴ = -τ.mapMatrix S := by
    rw [← map_neg, ← hS]
    exact Matrix.ext fun i j => (IsCMField.complexEmbedding_complexConj E τ _).symm
  open scoped ComplexOrder in
  have h2 := (Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self (τ.mapMatrix S))).isUnit
  have h3 : 1 + (τ.mapMatrix S)ᴴ * τ.mapMatrix S = τ.mapMatrix (1 + S) * τ.mapMatrix (1 - S) := by
    rw [h1, map_add, map_sub, map_one]; noncomm_ring
  rw [h3, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, ← RingHom.map_det] at h2
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← _root_.map_ne_zero τ]
  exact left_ne_zero_of_mul h2.ne_zero

theorem exists_unitary_near {p : ℕ} (hp : p ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Matrix (Fin n) (Fin n) (LocAlg v))
    (hh : ∀ v, ((h v).map (locConj v))ᵀ * h v = 1) :
    ∃ γ : Matrix (Fin n) (Fin n) E, (γ.map cc)ᵀ * γ = 1 ∧
      ∀ v, (p : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal →
        ∀ i j, (((h v).map (locConj v))ᵀ * γ.map (locEmb v)) i j ∈ locOrder v := by
  have hT : {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) |
      (p : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal}.Finite := by
    simpa only [Ideal.dvd_span_singleton] using Ideal.finite_factors
      (I := Ideal.span {(p : 𝓞 (maximalRealSubfield E))}) (by simpa using hp)
  letI := fun v : hT.toFinset => locStar v.1
  have hv : ∀ v : hT.toFinset, (p : 𝓞 (maximalRealSubfield E)) ∈ v.1.asIdeal := fun v => hT.mem_toFinset.1 v.2
  choose ζ hζ hζ1 hζu using fun v : hT.toFinset => exists_norm_one_isUnit v.1 hp (hv v) (h v.1)
  obtain ⟨γ, hγ, hγ'⟩ := exists_unitary_approx (A := fun v : hT.toFinset => LocAlg v.1) (fun v => locEmb v.1)
    (fun v x => (locConj_locEmb v.1 x).symm) (fun v => (locOrder v.1).toSubring) (fun v z => locConj_mem v.1) hp
    (fun v => exists_inv_one_add v.1 (hv v)) (exists_sub_mem_locOrder _)
    (fun x => by
      obtain ⟨k, s, hk, hx⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
        (Algebra.IsAlgebraic.isAlgebraic x)).exists_nsmul_eq (𝓞 E)
      exact ⟨k, hk, fun v => by rw [← map_nsmul, hx]; exact locEmb_mem_locOrder v.1 s⟩)
    isUnit_one_add_of_skew (fun v => ζ v • h v.1)
    (fun v => by
      rw [star_smul, smul_mul_smul_comm]
      exact (congrArg₂ (· • ·) (hζ1 v) (hh v.1)).trans (one_smul _ _))
    hζu
  refine ⟨γ, hγ, fun v hv i j => ?_⟩
  let v' : hT.toFinset := ⟨v, hT.mem_toFinset.2 hv⟩
  have := mul_mem (hζ v') (hγ' v' i j)
  rw [star_smul, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (ζ v')] at this
  erw [hζ1 v', one_mul] at this
  exact this

end Local

section Genus

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_nsmul_mem {p : ℕ} (hp : p.Prime) (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (h : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (p : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal →
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) :
    ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ L := by
  by_contra hk
  push Not at hk
  let J : Ideal (𝓞 E) := L.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
  let I : Ideal (𝓞 (maximalRealSubfield E)) := J.comap (algebraMap _ _)
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by simpa using hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨Q, hIQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)}) I fun k hkI => by
    rw [Ideal.mem_span_singleton, Int.natCast_dvd]
    by_contra hd
    refine hk _ hd ?_
    have h1 : k • x ∈ L := by
      have : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (algebraMap ℤ _ k) • x ∈ L := hkI
      rwa [eq_intCast, map_intCast, Int.cast_smul_eq_zsmul] at this
    rw [← natCast_zsmul]
    rcases Int.natAbs_eq k with e | e
    · rwa [← e]
    · rwa [e, neg_smul, neg_mem_iff] at h1
  have hpQ : (p : 𝓞 (maximalRealSubfield E)) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ _) := hQp ▸ Ideal.mem_span_singleton_self _
    simpa using this
  obtain ⟨s, hs, hsx⟩ := h ⟨Q, hQ, fun e => hp.ne_zero (by simpa [e] using hpQ)⟩ hpQ
  exact hs (hIQ hsx)

theorem herm_one (x y : Fin n → E) : herm 1 x y = stdForm x y := by
  rw [herm_eq_dotProduct, Matrix.vecMul_one]
  rfl

theorem exists_smul_mem_stdMod (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) {y : Fin n → E}
    (hy : ∀ i, locEmb v (y i) ∈ locOrder v) :
    ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • y ∈ stdMod E n := by
  rw [← mem_span_semiLoc_iff, pi_eq_sum_univ' y]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _
    (⟨y j, (locEmb_mem_locOrder_iff v _).1 (hy j)⟩ : semiLoc v) (Submodule.subset_span (single_mem_stdMod j))

theorem inGenus_of_selfDual [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {Λ : Lat E n}
    (hΛ : Λ.SelfDual) : Λ.InGenus := by
  intro p hp
  have hL : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ.L := ⟨Λ.fg, Λ.span_top⟩
  choose h hh hhL using exists_orthonormal_frame (G := 1) (L := Λ.L)
    (fun a b => by simp [cc, Matrix.one_apply, apply_ite, eq_comm]) (by simp) hL
    (fun x => (hΛ x).trans (forall₂_congr fun y _ => by
      rw [herm_one]
      exact ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨_, h⟩, rfl⟩⟩))
  have hh' : ∀ v, ((h v).1.map (locConj v))ᵀ * (h v).1 = 1 := fun v => by
    have := congrArg Matrix.transpose (hh v)
    rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hinv : ∀ v, ((h v)⁻¹).1 = ((h v).1.map (locConj v))ᵀ := fun v =>
    Units.inv_eq_of_mul_eq_one_left (hh' v)
  obtain ⟨γ, hγ, hγ'⟩ := exists_unitary_near hp.ne_zero (fun v => (h v).1) hh'
  have hγ₂ : γ * (γ.map cc)ᵀ = 1 := mul_eq_one_comm.1 hγ
  have hmap : ∀ v (M : Matrix (Fin n) (Fin n) E) (x : Fin n → E),
      (fun i => locEmb v ((M *ᵥ x) i)) = M.map (locEmb v) *ᵥ fun i => locEmb v (x i) :=
    fun v M x => funext fun i => RingHom.map_mulVec (locEmb v) M x i
  refine ⟨Matrix.toLin'OfInv hγ hγ₂, fun x y => ?_, fun x hx => exists_nsmul_mem hp _ _ fun v hv => ?_,
    fun x hx => exists_nsmul_mem hp _ _ fun v hv => ?_⟩
  · change stdForm (γ *ᵥ x) (γ *ᵥ y) = _
    have := congrArg Matrix.transpose hγ
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
    rw [← herm_one, herm_mulVec, Matrix.mul_one, this, herm_one]
  · have h1 := (hhL v _).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
    have h2 : ∀ i j, (((γ.map cc)ᵀ).map (locEmb v) * (h v).1) i j ∈ locOrder v := fun i j => by
      convert locConj_mem v (hγ' v hv j i) using 1
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, locConj_locConj,
        locConj_locEmb, mul_comm]
    have h3 := mulVec_mem_locOrder v h2 h1
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← hmap] at h3
    obtain ⟨s, hs, h4⟩ := exists_smul_mem_stdMod v h3
    refine ⟨s, hs, _, h4, ?_⟩
    change γ *ᵥ _ = _
    rw [← algebraMap_smul E, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hγ₂, Matrix.one_mulVec, algebraMap_smul]
  · obtain ⟨y, hy, rfl⟩ := hx
    refine (locEmb_mem_locLattice_iff v hL _).1 ((hhL v _).2 ?_)
    change ∀ i, (_ *ᵥ fun i => locEmb v ((γ *ᵥ y) i)) i ∈ _
    rw [hmap, Matrix.mulVec_mulVec, hinv]
    refine mulVec_mem_locOrder v (hγ' v hv) fun i => ?_
    obtain ⟨a, ha⟩ := mem_stdMod.1 hy i
    exact ha ▸ locEmb_mem_locOrder v a

end Genus

end GlobalTheory.GenusSelfDual
