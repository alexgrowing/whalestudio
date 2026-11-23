import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoDefs
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoHostA
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

namespace Biq

variable {F : Type} [Field F] [NumberField F] {m : ℕ} (B : Biq F m)

def W : 𝓞 F := ⟨B.w, B.integral_w⟩

def J : 𝓞 F := ⟨B.i, B.integral_i⟩

def mk4 (v : ℤ × ℤ × ℤ × ℤ) : 𝓞 F := v.1 + v.2.1 * B.W + v.2.2.1 * B.J + v.2.2.2 * (B.W * B.J)

theorem coe_W : algebraMap (𝓞 F) F B.W = B.w := rfl
theorem coe_J : algebraMap (𝓞 F) F B.J = B.i := rfl

theorem W_sq : B.W * B.W = B.W - m := RingOfIntegers.ext (by
  simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_natCast, coe_W] using B.w_sq)

theorem J_sq : B.J * B.J = -1 := RingOfIntegers.ext (by
  simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_neg, map_one, coe_J] using B.i_sq)

theorem coe_mk_quad (v : ℤ × ℤ × ℤ × ℤ) : algebraMap (𝓞 F) F (B.mk4 v) =
    v.1 + v.2.1 * B.w + v.2.2.1 * B.i + v.2.2.2 * (B.w * B.i) := by
  simp only [mk4, map_add, map_mul, map_intCast, coe_W, coe_J]

theorem mk_quad_injective : Function.Injective B.mk4 := fun v v' h => by
  have h' := congrArg (algebraMap (𝓞 F) F) h
  rw [coe_mk_quad, coe_mk_quad] at h'
  obtain ⟨h1, h2, h3, h4⟩ := B.indep (v.1 - v'.1) (v.2.1 - v'.2.1) (v.2.2.1 - v'.2.2.1) (v.2.2.2 - v'.2.2.2) (by
    push_cast; linear_combination h')
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact_mod_cast sub_eq_zero.1 h1
  · exact_mod_cast sub_eq_zero.1 h2
  · exact_mod_cast sub_eq_zero.1 h3
  · exact_mod_cast sub_eq_zero.1 h4

theorem mk_quad_surjective {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) : Function.Surjective B.mk4 := fun x => by
  obtain ⟨a, b, c, e, h⟩ := B.coords hd hp x.isIntegral_coe
  exact ⟨(a, b, c, e), RingOfIntegers.ext (by rw [RingOfIntegers.coe_eq_algebraMap, coe_mk_quad]; exact h.symm)⟩

theorem σ_σ (x : F) : B.σ (B.σ x) = x := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  simp only [map_add, map_mul, map_ratCast, B.σw, B.σi, map_neg, neg_neg]

def σO : 𝓞 F ≃+* 𝓞 F :=
  RingOfIntegers.mapRingEquiv (RingEquiv.ofRingHom B.σ B.σ (RingHom.ext B.σ_σ) (RingHom.ext B.σ_σ))

theorem sigma_W : B.σO B.W = B.W := RingOfIntegers.ext B.σw

theorem σO_J : B.σO B.J = -B.J := RingOfIntegers.ext B.σi

variable [IsCMField F]

theorem complexConj_eq (hm : 0 < m) (x : F) : IsCMField.complexConj F x = B.σ (B.τ x) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, B.conj_eq hm]

include B in
theorem unramified {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) :
    Algebra.Unramified (𝓞 (maximalRealSubfield F)) (𝓞 F) := by
  have hm : 0 < m := by omega
  let R := 𝓞 (maximalRealSubfield F)
  let δ := KaehlerDifferential.D R (𝓞 F)
  have h1 : (2 * B.J) • δ B.J = 0 := by
    have := congrArg δ B.J_sq
    rw [Derivation.leibniz, map_neg, Derivation.map_one_eq_zero, neg_zero] at this
    rw [two_mul, add_smul, this]
  have h2 : (2 * B.W - 1) • δ B.W = 0 := by
    have := congrArg δ B.W_sq
    rw [Derivation.leibniz, map_sub, Derivation.map_natCast, sub_zero] at this
    rw [two_mul, sub_smul, add_smul, this, one_smul, sub_self]
  have h3 : δ (B.J * (B.W + B.W - 1)) = 0 := by
    obtain ⟨r, hr⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff F (B.J * (B.W + B.W - 1))).1
      (RingOfIntegers.ext (by
        rw [IsCMField.coe_ringOfIntegersComplexConj, B.complexConj_eq hm]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_add, map_one, coe_W, coe_J, B.τi, B.τw,
          B.σi, B.σw]
        ring))
    rw [← hr, Derivation.map_algebraMap]
  rw [Derivation.leibniz, map_sub, map_add, Derivation.map_one_eq_zero, sub_zero] at h3
  have hJ : δ B.J = 0 := by
    have e : (1 : 𝓞 F) = -(2 * m * B.J) * (2 * B.J) + (2 * B.W - 1) * (B.W + B.W - 1) := by
      linear_combination (4 * m : 𝓞 F) * B.J_sq - 4 * B.W_sq
    have e2 : (2 * B.W - 1) • ((B.W + B.W - 1) • δ B.J) = 0 := by
      rw [eq_neg_of_add_eq_zero_right h3, smul_neg, smul_comm, smul_add, h2, add_zero, smul_zero, neg_zero]
    rw [← one_smul (𝓞 F) (δ B.J), e, add_smul, mul_smul, mul_smul (2 * B.W - 1), h1, e2, smul_zero, add_zero]
  have hW : δ B.W = 0 := by
    rw [hJ, smul_zero, add_zero, ← two_smul (𝓞 F), smul_smul] at h3
    have e : (1 : 𝓞 F) = -(2 * m * B.J) * (B.J * 2) + (2 * B.W - 1) * (2 * B.W - 1) := by
      linear_combination (4 * m : 𝓞 F) * B.J_sq - 4 * B.W_sq
    rw [← one_smul (𝓞 F) (δ B.W), e, add_smul, mul_smul, mul_smul (2 * B.W - 1), h3, h2, smul_zero, smul_zero, add_zero]
  have hall : ∀ x, δ x = 0 := fun x => by
    obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd hp x
    simp only [mk4, map_add, Derivation.leibniz, hW, hJ, Derivation.map_intCast, smul_zero, add_zero]
  have hs : Subsingleton (Ω[𝓞 F⁄R]) := by
    rw [← Submodule.subsingleton_iff (𝓞 F), ← subsingleton_iff_bot_eq_top, eq_comm,
      ← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨x, rfl⟩
    exact hall x
  have : Algebra.FormallyUnramified R (𝓞 F) := ⟨hs⟩
  have : Algebra.FiniteType R (𝓞 F) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ R (𝓞 F)
  exact {}

end Biq

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def mat (w : 𝓞 E) (v : ℤ × ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) (𝓞 E) :=
  !![v.1 + v.2.1 * w, -(v.2.2.1 + v.2.2.2 * w); v.2.2.1 + v.2.2.2 * w, v.1 + v.2.1 * w]

set_option maxHeartbeats 1600000 in

theorem exists_pairHost {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsCMField E') (H' : Host E'), Nonempty (PairHost H H') := by
  obtain ⟨m, hd⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hm : 0 < m := by omega
  obtain ⟨F, _, _, ⟨B⟩⟩ := exists_biq m (by rw [show 4 * m - 1 = H.d by omega]; exact H.d_prime)
  have := B.numberField
  have := B.isCMField hm
  have hdO : (H.d : 𝓞 F) + 1 = 4 * m := by exact_mod_cast hd
  let H' : Host F :=
    { d := H.d, d_mod := H.d_mod, d_prime := H.d_prime, rt := 2 * B.W - 1
      rt_sq := by linear_combination 4 * B.W_sq + hdO
      w0 := B.W, two_weight_eq_one_add_root := by ring
      bar := (IsCMField.ringOfIntegersComplexConj F).toRingEquiv
      bar_eq := fun _ => rfl
      unram := B.unramified hd H.d_prime
      rt0 := H.rt0, sqrt_neg_disc_sq := H.sqrt_neg_disc_sq }
  have hbW : H'.bar B.W = 1 - B.W := GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator H'
  have hbJ : H'.bar B.J = -B.J := RingOfIntegers.ext (by
    rw [H'.bar_eq, B.complexConj_eq hm]
    show B.σ (B.τ B.i) = -B.i
    rw [B.τi, B.σi])
  have hw : H.w0 * H.w0 = H.w0 - m := by
    have hdE : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hd
    have h1 := H.rt_sq
    rw [GlobalTheory.HostModel.rt_eq] at h1
    have : (4 : 𝓞 E) * (H.w0 * H.w0 - (H.w0 - m)) = 0 := by linear_combination h1 - hdE
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (by norm_num))
  let e := Equiv.ofBijective B.mk4 ⟨B.mk_quad_injective, B.mk_quad_surjective hd H.d_prime⟩
  have he : ∀ (x : 𝓞 F) v, x = B.mk4 v → mat H.w0 (e.symm x) = mat H.w0 v := by
    rintro _ v rfl
    rw [show e.symm (B.mk4 v) = v from e.symm_apply_apply v]
  let ψ : 𝓞 F →+* Matrix (Fin 2) (Fin 2) (𝓞 E) :=
    { toFun := fun x => mat H.w0 (e.symm x)
      map_one' := by
        rw [he 1 (1, 0, 0, 0) (by simp [Biq.mk4])]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
      map_zero' := by
        rw [he 0 (0, 0, 0, 0) (by simp [Biq.mk4])]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
      map_add' := fun x y => by
        obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
        obtain ⟨⟨a', b', c', f'⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime y
        rw [he _ _ rfl, he _ _ rfl, he _ (a + a', b + b', c + c', f + f') (by simp only [Biq.mk4]; push_cast; ring)]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
      map_mul' := fun x y => by
        obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
        obtain ⟨⟨a', b', c', f'⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime y
        rw [he _ _ rfl, he _ _ rfl, he _ (a * a' - m * b * b' - c * c' + m * f * f',
          a * b' + b * a' + b * b' - c * f' - f * c' - f * f', a * c' + c * a' - m * b * f' - m * f * b',
          a * f' + b * c' + b * f' + c * b' + f * a' + f * b') (by
            simp only [Biq.mk4]; push_cast
            linear_combination ((b * b' + (b * f' + f * b') * B.J - f * f' : 𝓞 F)) * B.W_sq +
              ((c + f * B.W) * (c' + f' * B.W) : 𝓞 F) * B.J_sq)]
        ext1 i j
        fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination (f * f' - b * b' : 𝓞 E) * hw
        · linear_combination (b * f' + f * b' : 𝓞 E) * hw
        · linear_combination (-(b * f' + f * b') : 𝓞 E) * hw
        · linear_combination (f * f' - b * b' : 𝓞 E) * hw }
  have hψ : ∀ (x : 𝓞 F) v, x = B.mk4 v → ψ x = mat H.w0 v := he
  clear_value ψ
  refine ⟨F, inferInstance, inferInstance, inferInstance, H', ⟨⟨ψ, B.σO, fun x i j => ?_, ?_, fun x => ?_, ?_,
    fun k _ _ τ τ' h => ?_⟩⟩⟩
  · obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
    rw [hψ _ _ rfl, hψ _ (a + b, -b, -c - f, f) (by
      simp only [Biq.mk4, map_add, map_mul, map_intCast, hbW, hbJ]; push_cast; ring)]
    fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
  · rw [hψ _ (0, 1, 0, 0) (by simp [Biq.mk4, H'])]
    ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
  · obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
    rw [hψ _ _ rfl, hψ _ (a, b, -c, -f) (by
      simp only [Biq.mk4, map_add, map_mul, map_intCast, B.sigma_W, B.σO_J]; push_cast; ring)]
    ext1 i j
    fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_diagonal, Matrix.diagonal_mul] <;> ring
  · show B.σO (2 * B.W - 1) = 2 * B.W - 1
    rw [map_sub, map_mul, map_ofNat, map_one, B.sigma_W]
  · have hW : τ' B.W = τ B.W := by
      change τ (2 * B.W - 1) = τ' (2 * B.W - 1) at h
      simp only [map_sub, map_mul, map_ofNat, map_one] at h
      linear_combination (-1 / 2 : k) * h
    have h1 := congrArg τ B.J_sq
    have h2 := congrArg τ' B.J_sq
    simp only [map_mul, map_neg, map_one] at h1 h2
    have : (τ' B.J - τ B.J) * (τ' B.J + τ B.J) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.1 this with h3 | h3
    · refine Or.inl (RingHom.ext fun x => ?_)
      obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
      simp only [Biq.mk4, map_add, map_mul, map_intCast, hW, sub_eq_zero.1 h3]
    · refine Or.inr (RingHom.ext fun x => ?_)
      obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
      show _ = τ (B.σO _)
      simp only [Biq.mk4, map_add, map_mul, map_intCast, hW, eq_neg_of_add_eq_zero_left h3, B.sigma_W, B.σO_J, map_neg]

end PositivityTheory.HtPt.Kftwo
