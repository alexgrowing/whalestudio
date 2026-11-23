import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

noncomputable section

open NumberField Matrix Polynomial

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.smulF (c : 𝓞 D.F) (x : D.La) : D.La := algebraMap (𝓞 D.F) D.O c • x

def Datum.skewFun (x y : D.La) : Module.Dual ℚ D.F :=
  (integralBasis D.F).constr ℚ fun k => ((D.EF (D.smulF (RingOfIntegers.basis D.F k) x) y : ℤ) : ℚ)

def Datum.skew (x y : D.La) : D.F :=
  ((Algebra.traceForm ℚ D.F).toDual (traceForm_nondegenerate ℚ D.F)).symm (D.skewFun x y)

theorem Datum.EF_smulF_eq_sum (c : 𝓞 D.F) (x y : D.La) :
    D.EF (D.smulF c x) y = ∑ k, (RingOfIntegers.basis D.F).repr c k *
      D.EF (D.smulF (RingOfIntegers.basis D.F k) x) y := by
  conv_lhs => rw [← (RingOfIntegers.basis D.F).sum_repr c]
  simp only [Datum.smulF, map_sum, Finset.sum_smul, LinearMap.sum_apply, map_zsmul, smul_assoc,
    LinearMap.smul_apply, smul_eq_mul]

theorem Datum.skewFun_apply (x y : D.La) (c : 𝓞 D.F) :
    D.skewFun x y (algebraMap (𝓞 D.F) D.F c) = (D.EF (D.smulF c x) y : ℚ) := by
  have hc : algebraMap (𝓞 D.F) D.F c =
      ∑ k, ((RingOfIntegers.basis D.F).repr c k : ℚ) • integralBasis D.F k := by
    conv_lhs => rw [← (RingOfIntegers.basis D.F).sum_repr c]
    simp only [map_sum, integralBasis_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  rw [hc, map_sum, D.EF_smulF_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Datum.skewFun, Module.Basis.constr_basis, smul_eq_mul]

theorem Datum.trace_skew_mul (x y : D.La) (c : 𝓞 D.F) :
    Algebra.trace ℚ D.F (D.skew x y * algebraMap (𝓞 D.F) D.F c) = (D.EF (D.smulF c x) y : ℚ) := by
  rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def (traceForm_nondegenerate ℚ D.F), Datum.skew,
    LinearEquiv.apply_symm_apply, Datum.skewFun_apply]

theorem eq_of_trace_mul {F : Type} [Field F] [NumberField F] {s t : F}
    (h : ∀ c : 𝓞 F, Algebra.trace ℚ F (s * algebraMap (𝓞 F) F c) = Algebra.trace ℚ F (t * algebraMap (𝓞 F) F c)) :
    s = t := by
  have key : ∀ z : F, Algebra.traceForm ℚ F (s - t) z = 0 := by
    intro z
    rw [← (integralBasis F).sum_repr z, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul, Algebra.traceForm_apply, integralBasis_apply, sub_mul, map_sub, h, sub_self, smul_zero]
  exact sub_eq_zero.1 ((traceForm_nondegenerate ℚ F).1 _ key)

theorem Datum.bar_bar (c : 𝓞 D.F) : D.bar (D.bar c) = c := by
  apply RingOfIntegers.ext
  rw [D.bar_eq, D.bar_eq, IsCMField.complexConj_apply_apply]

theorem Datum.EF_smulF_right (c : 𝓞 D.F) (x y : D.La) : D.EF x (D.smulF c y) = D.EF (D.smulF (D.bar c) x) y := by
  rw [Datum.smulF, Datum.smulF, D.adj, D.star_F, MulOpposite.unop_op, D.bar_bar]

theorem Datum.EF_swap (x y : D.La) : D.EF y x = - D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt, zero_add, add_zero] at h
  linarith

theorem Datum.skew_swap (x y : D.La) : D.skew y x = - IsCMField.complexConj D.F (D.skew x y) := by
  apply eq_of_trace_mul
  intro c
  rw [D.trace_skew_mul, neg_mul, map_neg]
  have hc : IsCMField.complexConj D.F (algebraMap (𝓞 D.F) D.F (D.bar c)) = algebraMap (𝓞 D.F) D.F c := by
    have := D.bar_eq (D.bar c)
    rw [D.bar_bar] at this
    exact this.symm
  have h1 : IsCMField.complexConj D.F (D.skew x y) * algebraMap (𝓞 D.F) D.F c =
      IsCMField.complexConj D.F (D.skew x y * algebraMap (𝓞 D.F) D.F (D.bar c)) := by
    rw [map_mul, hc]
  have htr : Algebra.trace ℚ D.F (IsCMField.complexConj D.F (D.skew x y * algebraMap (𝓞 D.F) D.F (D.bar c))) =
      Algebra.trace ℚ D.F (D.skew x y * algebraMap (𝓞 D.F) D.F (D.bar c)) :=
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj D.F).restrictScalars ℚ) _
  rw [h1, htr, D.trace_skew_mul, D.EF_swap, D.EF_smulF_right]
  push_cast; ring

theorem Datum.conj_ω : IsCMField.complexConj D.F (D.ω : D.F) = D.tr - D.ω := by
  have h := congrArg (fun z : 𝓞 D.F => (z : D.F)) D.tr_eq
  simp only [map_add, map_intCast] at h
  rw [← D.bar_eq]
  push_cast at h ⊢
  linear_combination h

theorem Datum.ω_sq : (D.ω : D.F) ^ 2 = D.tr * D.ω - D.nm := by
  have h := congrArg (fun z : 𝓞 D.F => (z : D.F)) D.nm_eq
  have h2 := D.conj_ω
  rw [← D.bar_eq] at h2
  have h3 : (D.ω : D.F) * ((D.bar D.ω : 𝓞 D.F) : D.F) = D.nm := by
    simpa only [map_mul, map_intCast] using h
  rw [h2] at h3
  linear_combination -h3

def Datum.del : D.F := if 0 < D.ρc.im then (D.tr : D.F) - 2 * D.ω else 2 * D.ω - D.tr

theorem Datum.conj_del : IsCMField.complexConj D.F D.del = - D.del := by
  unfold Datum.del
  split_ifs <;> simp only [map_sub, map_mul, map_intCast, map_ofNat, D.conj_ω] <;> ring

theorem Datum.del_sq : D.del ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : D.F) := by
  unfold Datum.del
  push_cast
  split_ifs <;> linear_combination 4 * D.ω_sq

def Datum.hermF (x y : D.La) : D.F := D.skew x y / D.del

theorem Datum.conj_hermF (x y : D.La) : IsCMField.complexConj D.F (D.hermF x y) = D.hermF y x := by
  rw [Datum.hermF, Datum.hermF, map_div₀, D.conj_del, D.skew_swap x y]
  ring

def Datum.IsFBasis (e : Fin D.n → D.La) : Prop :=
  (∀ c : Fin D.n → 𝓞 D.F, ∑ i, D.smulF (c i) (e i) = 0 → c = 0) ∧
    ∀ x : D.La, ∃ k : ℤ, k ≠ 0 ∧ ∃ c : Fin D.n → 𝓞 D.F, k • x = ∑ i, D.smulF (c i) (e i)

def Datum.gram (e : Fin D.n → D.La) : Matrix (Fin D.n) (Fin D.n) D.F := Matrix.of fun i j => D.hermF (e i) (e j)

theorem Datum.gram_herm (e : Fin D.n → D.La) :
    ((D.gram e).map (IsCMField.complexConj D.F : D.F →+* D.F))ᵀ = D.gram e := by
  ext i j
  simp [Datum.gram, D.conj_hermF]

def Datum.Kq : Subfield D.F := (IntermediateField.adjoin ℚ {(D.ω : D.F)}).toSubfield

theorem Datum.isIntegral_ω : IsIntegral ℚ (D.ω : D.F) := Algebra.IsIntegral.isIntegral _

def Datum.quadQ : ℚ[X] := X ^ 2 - C (D.tr : ℚ) * X + C (D.nm : ℚ)

theorem Datum.quadQ_natDegree : D.quadQ.natDegree = 2 := by
  unfold Datum.quadQ; compute_degree!

theorem Datum.quadQ_monic : D.quadQ.Monic := by
  unfold Datum.quadQ; monicity!

theorem Datum.aeval_quadQ : aeval (D.ω : D.F) D.quadQ = 0 := by
  simp only [Datum.quadQ, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_intCast, D.ω_sq]
  ring

theorem Datum.ω_ne_rat (q : ℚ) : (D.ω : D.F) ≠ algebraMap ℚ D.F q := by
  intro h
  have h1 := D.ω_sq
  rw [h] at h1
  have h2 : q ^ 2 = D.tr * q - D.nm := (algebraMap ℚ D.F).injective (by simpa using h1)
  have h3 : ((D.tr : ℚ)) ^ 2 - 4 * D.nm < 0 := by exact_mod_cast D.disc_neg
  nlinarith [sq_nonneg (2 * q - D.tr)]

theorem Datum.minpoly_ω : minpoly ℚ (D.ω : D.F) = D.quadQ := by
  have hdvd := minpoly.dvd ℚ _ D.aeval_quadQ
  have hdeg : 2 ≤ (minpoly ℚ (D.ω : D.F)).natDegree := by
    by_contra h
    have h1 : (minpoly ℚ (D.ω : D.F)).natDegree = 1 := by
      have := minpoly.natDegree_pos D.isIntegral_ω; omega
    obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.1 h1
    exact D.ω_ne_rat q hq.symm
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic D.isIntegral_ω) D.quadQ_monic hdvd
    (by rw [D.quadQ_natDegree]; exact hdeg)).symm

theorem Datum.hKq : Module.finrank ℚ D.Kq = 2 ∧ ∀ τ : D.F →+* ℂ, ∃ x ∈ D.Kq, (τ x).im ≠ 0 := by
  constructor
  · have h1 : Module.finrank ℚ (IntermediateField.adjoin ℚ {(D.ω : D.F)}) = 2 := by
      rw [IntermediateField.adjoin.finrank D.isIntegral_ω, D.minpoly_ω, D.quadQ_natDegree]
    rw [← h1]
    exact LinearEquiv.finrank_eq
      { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl, map_smul' := fun q x => Subtype.ext (by simp [Rat.smul_def]) }
  · intro τ
    refine ⟨D.ω, IntermediateField.mem_adjoin_simple_self ℚ _, fun him => ?_⟩
    have h := congrArg (fun z => (τ z).re) D.ω_sq
    simp only [map_pow, map_sub, map_mul, map_intCast, pow_two, Complex.mul_re, him, mul_zero, sub_zero,
      Complex.sub_re, Complex.intCast_re, Complex.intCast_im, zero_mul] at h
    have h3 : ((D.tr : ℝ)) ^ 2 - 4 * D.nm < 0 := by exact_mod_cast D.disc_neg
    nlinarith [sq_nonneg (2 * (τ D.ω).re - D.tr)]

def Datum.kqEquiv : D.Kq →+* IntermediateField.adjoin ℚ {(D.ω : D.F)} where
  toFun x := ⟨x.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def Datum.uOf (r : ℚ_[p]) (hr : r ^ 2 - D.tr * r + D.nm = 0) : D.Kq →+* ℚ_[p] :=
  ((IntermediateField.adjoin.powerBasis D.isIntegral_ω).lift r (by
      rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, D.minpoly_ω]
      simp only [Datum.quadQ, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_intCast]
      linear_combination hr)).toRingHom.comp D.kqEquiv

theorem Datum.uOf_ω (r : ℚ_[p]) (hr : r ^ 2 - D.tr * r + D.nm = 0) :
    D.uOf r hr ⟨D.ω, IntermediateField.mem_adjoin_simple_self ℚ _⟩ = r := by
  rw [Datum.uOf, RingHom.comp_apply]
  exact PowerBasis.lift_gen _ _ _

section Places

variable {F : Type} [Field F] [NumberField F] (Kq : Subfield F) (u : Kq →+* ℚ_[p])

def OverU : Type := {τ : F →+* PadicAlgCl p // GlobalTheory.LKTrip.LiesOver Kq u τ}

def placeSetoid : Setoid (OverU Kq u) where
  r τ τ' := ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
    ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp τ.1 = τ'.1
  iseqv := by
    refine ⟨fun τ => ⟨AlgEquiv.refl, by ext; rfl⟩, ?_, ?_⟩
    · rintro τ τ' ⟨σ, h⟩
      refine ⟨σ.symm, ?_⟩
      rw [← h]; ext x; simp
    · rintro τ τ' τ'' ⟨σ, h⟩ ⟨σ', h'⟩
      refine ⟨σ.trans σ', ?_⟩
      rw [← h', ← h]; ext x; simp

def PlacesU : Type := Quotient (placeSetoid Kq u)

instance : Finite (OverU Kq u) := Subtype.finite

instance : Finite (PlacesU Kq u) := Quotient.finite _

def nPlacesU : ℕ := Nat.card (PlacesU Kq u)

def placeRep (i : Fin (nPlacesU Kq u)) : F →+* PadicAlgCl p :=
  (Quotient.out ((Finite.equivFin (PlacesU Kq u)).symm i) : OverU Kq u).1

end Places

def iotaPOf (p : ℕ) [Fact p.Prime] : AlgebraicClosure ℚ →+* PadicAlgCl p :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p).toRingHom

def iotaCOf : AlgebraicClosure ℚ →+* ℂ :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom

section Examples

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

example (x y : D.La) : IsCMField.complexConj D.F (D.hermF x y) = D.hermF y x := D.conj_hermF x y

example (x : D.La) : D.skew x x = - IsCMField.complexConj D.F (D.skew x x) := D.skew_swap x x

example : D.del ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : D.F) := D.del_sq

example : Module.finrank ℚ D.Kq = 2 := D.hKq.1

end Examples

end GlobalTheory.UPel.HT
