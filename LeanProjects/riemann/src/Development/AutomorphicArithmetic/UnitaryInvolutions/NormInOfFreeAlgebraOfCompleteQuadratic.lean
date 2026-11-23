import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.IsHerm
import Development.AutomorphicArithmetic.UnitaryInvolutions.ExistsMulInvolutionEqFixedUnitOfComplete
open Matrix Polynomial
open scoped TensorProduct

private lemma repr_sum {R T : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (e : Fin n → R) (i : Fin n) :
    B.repr (∑ j, e j • B j) i = e i :=
  congrFun (B.repr_sum_self e) i

private lemma coord_dvd {R T : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (ϖ : R) (m : ℕ) (y : T) :
    (∃ e, y = (algebraMap R T ϖ) ^ m * e) ↔ ∀ i, ∃ e, B.repr y i = ϖ ^ m * e := by
  constructor
  · rintro ⟨e, rfl⟩ i
    refine ⟨B.repr e i, ?_⟩
    rw [← map_pow, ← Algebra.smul_def, map_smul]
    simp
  · intro h
    choose e he using h
    refine ⟨∑ i, e i • B i, ?_⟩
    rw [← map_pow, ← Algebra.smul_def]
    apply B.ext_elem
    intro i
    rw [he, map_smul, Finsupp.smul_apply, repr_sum]
    simp

private lemma coord_reg {R T : Type} [CommRing R] [IsDomain R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (ϖ : R) (hϖ : ϖ ≠ 0) (x : T)
    (h : algebraMap R T ϖ * x = 0) : x = 0 := by
  apply B.ext_elem
  intro i
  have h1 : B.repr (ϖ • x) i = 0 := by
    rw [Algebra.smul_def, h]
    simp
  rw [map_smul] at h1
  simpa [hϖ] using h1

private lemma coord_complete {R T : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (ϖ : R)
    (hcomp : ∀ f : ℕ → R, (∀ m, ∃ e, f (m + 1) - f m = ϖ ^ m * e) →
      ∃ L, ∀ m, ∃ e, f m - L = ϖ ^ m * e)
    (f : ℕ → T) (hf : ∀ m, ∃ e, f (m + 1) - f m = (algebraMap R T ϖ) ^ m * e) :
    ∃ L, ∀ m, ∃ e, f m - L = (algebraMap R T ϖ) ^ m * e := by
  have h1 : ∀ i, ∃ L, ∀ m, ∃ e, B.repr (f m) i - L = ϖ ^ m * e := by
    intro i
    apply hcomp (fun m => B.repr (f m) i)
    intro m
    obtain ⟨e, he⟩ := (coord_dvd B ϖ m _).1 (hf m) i
    exact ⟨e, by simpa using he⟩
  choose L hL using h1
  refine ⟨∑ i, L i • B i, fun m => (coord_dvd B ϖ m _).2 fun i => ?_⟩
  obtain ⟨e, he⟩ := hL i m
  refine ⟨e, ?_⟩
  rw [map_sub, Finsupp.sub_apply, repr_sum]
  exact he

private lemma coord_sep {R T : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (ϖ : R)
    (hsep : ∀ x : R, (∀ m : ℕ, ∃ e, x = ϖ ^ m * e) → x = 0)
    (x : T) (h : ∀ m : ℕ, ∃ e, x = (algebraMap R T ϖ) ^ m * e) : x = 0 := by
  apply B.ext_elem
  intro i
  simpa using hsep _ fun m => (coord_dvd B ϖ m x).1 (h m) i

private lemma coord_finite {R T : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (B : Module.Basis (Fin n) R T) (ϖ : R) (hfin : Finite (R ⧸ Ideal.span {ϖ})) :
    Finite (T ⧸ Ideal.span {algebraMap R T ϖ}) := by
  let g : (Fin n → R ⧸ Ideal.span {ϖ}) → T ⧸ Ideal.span {algebraMap R T ϖ} := fun v =>
    Ideal.Quotient.mk _ (∑ i, (Quotient.out (v i) : R) • B i)
  refine Finite.of_surjective g fun y => ?_
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨fun i => Ideal.Quotient.mk _ (B.repr t i), ?_⟩
  refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ?_)
  have hd : ∃ e, (∑ i, (Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) (B.repr t i)) : R) • B i) - t
      = (algebraMap R T ϖ) ^ 1 * e := by
    refine (coord_dvd B ϖ 1 _).2 fun i => ?_
    have hm : (Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) (B.repr t i)) : R) - B.repr t i
        ∈ Ideal.span {ϖ} :=
      Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨e, ?_⟩
    rw [map_sub, Finsupp.sub_apply, repr_sum]
    simpa [mul_comm] using he.symm
  obtain ⟨e, he⟩ := hd
  exact ⟨e, by rw [he, pow_one, mul_comm]⟩

theorem UpperTheory.normIn_of_free_algebra_of_complete_quadratic :
    ∀ (k R : Type) [CommRing k] [CommRing R] [IsDomain R] [Algebra k R] (c : R ≃ₐ[k] R) (ϖ ω : R),
        UpperTheory.ConvolutionTheory.D.IsGal c 2 → c ϖ = ϖ → ϖ ≠ 0 →
        (∀ f : ℕ → R, (∀ m, ∃ e, f (m + 1) - f m = ϖ ^ m * e) → ∃ L, ∀ m, ∃ e, f m - L = ϖ ^ m * e) →
        (∀ x : R, (∀ m : ℕ, ∃ e, x = ϖ ^ m * e) → x = 0) →
        Finite (R ⧸ Ideal.span {ϖ}) → IsUnit (ω - c ω) →
        ∀ (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (_ : Module.Basis (Fin n) k A) (x : Aˣ), UpperTheory.ConvolutionTheory.D.NormIn c x := by
  intro k R _ _ _ _ c ϖ ω hG hcϖ hϖ hcomp hsep hfin hω A _ _ n b x
  have hc2 : ∀ r, c (c r) = r := fun r => by
    have h := DFunLike.congr_fun hG.pow r
    simpa [pow_two] using h
  have hio : ∀ (r : R) (a : A), UpperTheory.ConvolutionTheory.D.io c A (r ⊗ₜ[k] a) = (c r) ⊗ₜ[k] a := fun r a => by
    simp [UpperTheory.ConvolutionTheory.D.io]
  have hioalg : ∀ r : R, UpperTheory.ConvolutionTheory.D.io c A (algebraMap R (R ⊗[k] A) r)
      = algebraMap R (R ⊗[k] A) (c r) := fun r => by
    simp [Algebra.TensorProduct.algebraMap_apply, hio]
  let ι : (R ⊗[k] A) →+* (R ⊗[k] A) := (UpperTheory.ConvolutionTheory.D.io c A : (R ⊗[k] A) ≃ₐ[k] (R ⊗[k] A))
  have hιa : ∀ t, ι t = UpperTheory.ConvolutionTheory.D.io c A t := fun _ => rfl
  have hinv : ∀ t, ι (ι t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp only [hιa, hio, hc2]
    | add s t hs ht => simp only [map_add, hs, ht]
  have B := Algebra.TensorProduct.basis R b
  obtain ⟨z, hz⟩ := UpperTheory.exists_mul_involution_eq_fixed_unit_of_complete (R ⊗[k] A) ι (algebraMap R _ ϖ) (algebraMap R _ ω) hinv
    (by rw [hιa, hioalg, hcϖ]) (coord_reg B ϖ hϖ) (coord_complete B ϖ hcomp) (coord_sep B ϖ hsep)
    (coord_finite B ϖ hfin)
    (by
      rw [hιa, hioalg, ← map_sub]
      exact hω.map _)
    ((1 : R) ⊗ₜ[k] (x : A))
    (x.isUnit.map (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A))
    (by rw [hιa, hio, map_one])
  have hu : IsUnit ((1 : R) ⊗ₜ[k] (x : A)) :=
    x.isUnit.map (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A)
  have hzu : IsUnit z := isUnit_of_mul_isUnit_left (hz ▸ hu)
  exact ⟨hzu.unit, by simpa [hιa] using hz.symm⟩
