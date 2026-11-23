import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.Columns.QthExistsBound

noncomputable section

namespace GlobalTheory.TwU.CongTwo

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem val_cong_of_mul_eq {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {ι : Type} [Fintype ι]
    [DecidableEq ι] {c : K} (hc0 : c ≠ 0) (hc : v c < 1) {A B H : Matrix ι ι K}
    (hA : ∀ i j, v (c⁻¹ * (A - 1) i j) ≤ 1) (hB : ∀ i j, v (c⁻¹ * (B - 1) i j) ≤ 1) (hAH : A * H = B) (i j : ι) :
    v (c⁻¹ * (H - 1) i j) ≤ 1 := by
  let S := v.integer
  let A0 : Matrix ι ι S := fun k l => ⟨c⁻¹ * (A - 1) k l, hA k l⟩
  let cS : S := ⟨c, hc.le⟩
  let AS : Matrix ι ι S := 1 + cS • A0
  have hAS : AS.map S.subtype = A := by
    ext k l
    show (((1 : Matrix ι ι S) k l : S) : K) + c * (c⁻¹ * (A - 1) k l) = A k l
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul, Matrix.sub_apply]
    by_cases h : k = l
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hdet : ∃ y : S, AS.det - 1 = y * cS := by
    let π := Ideal.Quotient.mk (Ideal.span {cS})
    have hπc : π cS = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    have hπ : π.mapMatrix AS = 1 := by
      ext k l
      simp only [AS, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, hπc,
        zero_mul, add_zero]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h1 : π AS.det = π 1 := by rw [RingHom.map_det, hπ, Matrix.det_one, map_one]
    exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1) |>.imp fun y hy => hy.symm
  obtain ⟨y, hy⟩ := hdet
  have hdA : A.det = (AS.det : K) := by
    rw [← hAS]
    exact (RingHom.map_det S.subtype AS).symm
  have hv1 : v A.det = 1 := by
    have e : A.det = 1 + (y : K) * c := by
      rw [hdA]
      have : ((AS.det - 1 : S) : K) = ((y * cS : S) : K) := congrArg Subtype.val hy
      push_cast at this
      linear_combination this
    rw [e]
    apply Valuation.map_one_add_of_lt
    rw [map_mul]
    calc v (y : K) * v c ≤ 1 * v c := mul_le_mul' y.2 le_rfl
      _ = v c := one_mul _
      _ < 1 := hc
  have hdet0 : A.det ≠ 0 := fun h => by rw [h, map_zero] at hv1; exact zero_ne_one hv1
  have hMA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.2 hdet0)
  have hH : H - 1 = A⁻¹ * (B - A) := by
    rw [Matrix.mul_sub, ← hAH, ← Matrix.mul_assoc, hMA, Matrix.one_mul]
  have hinv : ∀ k l, v ((A⁻¹) k l) ≤ 1 := by
    intro k l
    have hadj : A.adjugate = AS.adjugate.map S.subtype := by
      rw [← hAS]
      exact (RingHom.map_adjugate S.subtype AS).symm
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', map_mul, map_inv₀, hv1, inv_one, one_mul,
      hadj, Matrix.map_apply]
    exact (AS.adjugate k l).2
  have e : c⁻¹ * (H - 1) i j = ∑ k, A⁻¹ i k * (c⁻¹ * (B - 1) k j - c⁻¹ * (A - 1) k j) := by
    rw [hH, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.sub_apply]
    ring
  rw [e]
  exact Subring.sum_mem S fun k _ => Subring.mul_mem S (hinv i k) (Subring.sub_mem S (hB k j) (hA k j))

end GlobalTheory.TwU.CongTwo

namespace GlobalTheory.TwU.CongTwo

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open Formalism.L2.DIV (AfE)
open scoped TensorProduct

theorem intAt_inv_mul_of_nearAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g₁ g₂ : GL (Fin N) E) :
    0 < n → NearAt P n x g₁ → NearAt P n x g₂ → ∀ a b : Fin N,
      IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
  intro hn h1 h2 a b
  obtain ⟨ι, hι⟩ := exists_isAdIso F E
  let φ : AfE F E →+* P.adicCompletion E :=
    { toFun := fun z => ι z P
      map_one' := by rw [map_one]; rfl
      map_mul' := fun x y => by rw [map_mul]; rfl
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun x y => by rw [map_add]; rfl }
  have hφ : ∀ e : E, φ (iA F E e) = algebraMap E (P.adicCompletion E) e := fun e => by
    show ι (iA F E e) P = _
    rw [show ι (iA F E e) = algebraMap E _ e from hι.1 e]; rfl
  have hq0 : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have hqv : Valued.v (algebraMap E (P.adicCompletion E) ((qOf P : ℕ) : E)) < 1 := by
    show Valued.v (((((qOf P : ℕ) : E)) : P.adicCompletion E)) < 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← map_natCast (algebraMap (𝓞 E) E),
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 (Ideal.absNorm_mem _)
  set c : P.adicCompletion E := algebraMap E (P.adicCompletion E) ((((qOf P : ℕ) : E)) ^ n) with hc
  have hc0 : c ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hq0)
  have hcv : Valued.v c < 1 := by
    rw [hc, map_pow, map_pow]
    exact pow_lt_one' hqv (Nat.pos_iff_ne_zero.1 hn)
  have h1apply : ∀ k l : Fin N, φ ((1 : Matrix (Fin N) (Fin N) (AfE F E)) k l) = (1 : Matrix (Fin N) (Fin N) (P.adicCompletion E)) k l := by
    intro k l
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have htr : ∀ g : GL (Fin N) E, NearAt P n x g → ∀ k l,
      Valued.v (c⁻¹ * ((((x⁻¹ * ratA F g : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)).map φ) - 1) k l) ≤ 1 := by
    intro g hg k l
    have h := hι.val_le (hg k l)
    have e : ι (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (((x⁻¹ * ratA F g : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)) - 1) k l) P =
        c⁻¹ * ((((x⁻¹ * ratA F g : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)).map φ) - 1) k l := by
      show φ _ = _
      rw [map_mul, hφ, map_inv₀, Matrix.sub_apply, Matrix.sub_apply, map_sub, h1apply, Matrix.map_apply]
    rw [e] at h
    exact h
  have hrat : ∀ g : GL (Fin N) E, ((ratA F g : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)).map φ =
      (g : Matrix (Fin N) (Fin N) E).map (algebraMap E (P.adicCompletion E)) := by
    intro g
    exact Matrix.ext fun k l => hφ _
  have hmul : (((x⁻¹ * ratA F g₁ : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)).map φ) *
      ((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (algebraMap E (P.adicCompletion E)) =
      (((x⁻¹ * ratA F g₂ : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)).map φ) := by
    rw [← hrat, ← Matrix.map_mul, ← Units.val_mul]
    congr 2
    rw [map_mul, map_inv]
    group
  have key := val_cong_of_mul_eq Valued.v hc0 hcv (htr g₁ h1) (htr g₂ h2) hmul a b
  have e2 : c⁻¹ * (((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (algebraMap E (P.adicCompletion E)) - 1) a b =
      algebraMap E (P.adicCompletion E) ((((qOf P : ℕ) : E) ^ n)⁻¹ * (((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
    rw [map_mul, map_inv₀, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply]
    congr 2
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e2] at key
  letI : StarRing E := starRingOfComm
  rw [qth_intAt_iff]
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact key

end GlobalTheory.TwU.CongTwo
