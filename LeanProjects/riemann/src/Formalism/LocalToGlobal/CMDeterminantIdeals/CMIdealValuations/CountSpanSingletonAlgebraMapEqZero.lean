import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementP
import Formalism.LocalToGlobal.CMDeterminantIdeals.CmNumbersLink

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

section counts

variable {F : Type} [Field F] [NumberField F]

private lemma count_coeIdeal_eq_zero_of_not_le (v : HeightOneSpectrum (𝓞 F)) {J : Ideal (𝓞 F)} (h : ¬ J ≤ v.asIdeal) :
    FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
  have hJ : J ≠ 0 := fun h0 => h (h0 ▸ bot_le)
  rw [FractionalIdeal.count_coe F v hJ]
  by_contra hne
  have hne' : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 := by exact_mod_cast hne
  exact h (Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd hJ v.irreducible).mp hne'))

lemma count_coeIdeal_eq_zero (v : HeightOneSpectrum (𝓞 F)) {J : Ideal (𝓞 F)} (h : ¬ J ≤ v.asIdeal) :
    FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) = 0 := count_coeIdeal_eq_zero_of_not_le v h

lemma not_le_of_count_eq_zero (v : HeightOneSpectrum (𝓞 F)) {J : Ideal (𝓞 F)} (hJ : J ≠ ⊥)
    (h : FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) = 0) : ¬ J ≤ v.asIdeal := by
  intro hle
  have hne : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 :=
    (Associates.count_ne_zero_iff_dvd hJ v.irreducible).mpr (Ideal.dvd_iff_le.mpr hle)
  rw [FractionalIdeal.count_coe F v hJ] at h
  exact hne (by exact_mod_cast h)

lemma exists_split_of_isLocGen (v : HeightOneSpectrum (𝓞 F)) {c : F} {I : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0)
    (hc : IsLocGen v c I) :
    ∃ A B : Ideal (𝓞 F), ¬ A ≤ v.asIdeal ∧ ¬ B ≤ v.asIdeal ∧
      I * (B : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ c * (A : FractionalIdeal (𝓞 F)⁰ F) := by
  set C := FractionalIdeal.spanSingleton (𝓞 F)⁰ c with hCdef
  have hC : C ≠ 0 := spanSingleton_ne_zero' hc.1
  set D := C⁻¹ * I with hD
  have hD0 : D ≠ 0 := mul_ne_zero (inv_ne_zero hC) hI
  have hDc : FractionalIdeal.count F v D = 0 := by
    rw [hD, FractionalIdeal.count_mul F v (inv_ne_zero hC) hI, FractionalIdeal.count_inv, hc.2]; ring
  obtain ⟨b, J, hb, hDJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul D
  have hbK : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hb
  set S := FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F b) with hS
  have hS0 : S ≠ 0 := spanSingleton_ne_zero' hbK
  have hJ0 : (J : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hDJ; exact hD0 hDJ
  rw [← FractionalIdeal.spanSingleton_inv] at hDJ
  set P : FractionalIdeal (𝓞 F)⁰ F := (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) with hP
  have hP0 : P ≠ 0 := by rw [hP, Ne, FractionalIdeal.coeIdeal_eq_zero]; exact v.ne_bot
  set k := FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) with hk
  have hSk : FractionalIdeal.count F v S = k := by
    have := hDc
    rw [hDJ, FractionalIdeal.count_mul F v (inv_ne_zero hS0) hJ0, FractionalIdeal.count_inv] at this
    omega
  have hSnn : ∀ w : HeightOneSpectrum (𝓞 F), 0 ≤ FractionalIdeal.count F w S := by
    intro w; rw [hS, ← FractionalIdeal.coeIdeal_span_singleton]; exact FractionalIdeal.count_coe_nonneg F w _
  have hPw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → FractionalIdeal.count F w P = 0 := fun w hw =>
    FractionalIdeal.count_maximal_coprime F w (Ne.symm hw)
  have hPk0 : P ^ (-k) ≠ 0 := zpow_ne_zero _ hP0
  have cnt : ∀ (X : FractionalIdeal (𝓞 F)⁰ F), X ≠ 0 → (∀ w, 0 ≤ FractionalIdeal.count F w X) →
      FractionalIdeal.count F v X = k →
      ∃ Y : Ideal (𝓞 F), (Y : FractionalIdeal (𝓞 F)⁰ F) = P ^ (-k) * X ∧ ¬ Y ≤ v.asIdeal := by
    intro X hX hXnn hXk
    have hY0 : P ^ (-k) * X ≠ 0 := mul_ne_zero hPk0 hX
    have hcnt : ∀ w, FractionalIdeal.count F w (P ^ (-k) * X) =
        -k * FractionalIdeal.count F w P + FractionalIdeal.count F w X := by
      intro w; rw [FractionalIdeal.count_mul F w hPk0 hX, FractionalIdeal.count_zpow]
    have hle : P ^ (-k) * X ≤ 1 := by
      refine le_one_of_count_nonneg hY0 (fun w => ?_)
      rw [hcnt w]
      by_cases hw : w = v
      · subst hw; rw [hP, FractionalIdeal.count_self, hXk]; ring_nf; exact le_refl _
      · rw [hPw w hw]; simpa using hXnn w
    obtain ⟨Y, hY⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
    refine ⟨Y, hY, not_le_of_count_eq_zero v ?_ ?_⟩
    · intro hbot; rw [hbot, FractionalIdeal.coeIdeal_bot] at hY; exact hY0 hY.symm
    · rw [hY, hcnt v, hP, FractionalIdeal.count_self, hXk]; ring
  obtain ⟨A, hA, hAv⟩ := cnt _ hJ0 (fun w => FractionalIdeal.count_coe_nonneg F w J) rfl
  obtain ⟨B, hB, hBv⟩ := cnt _ hS0 hSnn hSk
  refine ⟨A, B, hAv, hBv, ?_⟩
  have hI : I = C * D := by rw [hD, ← mul_assoc, mul_inv_cancel₀ hC, one_mul]
  rw [hA, hB, hI, hDJ]
  have h1 : S⁻¹ * S = 1 := inv_mul_cancel₀ hS0
  calc C * (S⁻¹ * ↑J) * (P ^ (-k) * S) = C * (P ^ (-k) * ↑J) * (S⁻¹ * S) := by ring
    _ = C * (P ^ (-k) * ↑J) := by rw [h1, mul_one]

end counts

section bc

variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]

lemma algebraMap_int_tower (a : 𝓞 K) :
    algebraMap (𝓞 K1) K1 (algebraMap (𝓞 K) (𝓞 K1) a) = algebraMap K K1 (algebraMap (𝓞 K) K a) := by
  first
  | rfl
  | rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

lemma algebraMap_int_injective : Function.Injective (algebraMap (𝓞 K) (𝓞 K1)) := by
  intro a b h
  have h1 := congrArg (algebraMap (𝓞 K1) K1) h
  rw [algebraMap_int_tower, algebraMap_int_tower] at h1
  exact IsFractionRing.injective (𝓞 K) K ((algebraMap K K1).injective h1)

lemma nzd_le : (𝓞 K)⁰ ≤ Submonoid.comap (algebraMap (𝓞 K) (𝓞 K1)) (𝓞 K1)⁰ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Formalism.L2.LamCM.algebraMap_int_injective (K := K) (K1 := K1))

def bcI (I : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 K1)⁰ K1 :=
  FractionalIdeal.extended K1 (nzd_le (K := K) (K1 := K1)) I

lemma locMap_eq :
    IsLocalization.map K1 (algebraMap (𝓞 K) (𝓞 K1)) (nzd_le (K := K) (K1 := K1)) = algebraMap K K1 := by
  apply IsLocalization.ringHom_ext (𝓞 K)⁰
  rw [IsLocalization.map_comp]
  ext a
  exact algebraMap_int_tower a

lemma coe_bcI (I : FractionalIdeal (𝓞 K)⁰ K) :
    ((bcI (K1 := K1) I : FractionalIdeal (𝓞 K1)⁰ K1) : Submodule (𝓞 K1) K1) =
      Submodule.span (𝓞 K1) (algebraMap K K1 '' {x | x ∈ I}) := by
  rw [bcI, FractionalIdeal.coe_extended_eq_span, locMap_eq]
  rfl

lemma eq_bcI {L : MLine K} {L1 : MLine K1} (h : IsBaseChangeLine L L1) : L1.I = bcI L.I := by
  unfold IsBaseChangeLine at h
  exact FractionalIdeal.coeToSubmodule_injective (h.1.trans (coe_bcI L.I).symm)

lemma bcI_ne_zero {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) : bcI (K1 := K1) I ≠ 0 := FractionalIdeal.extended_ne_zero _ _ (Formalism.L2.LamCM.algebraMap_int_injective (K := K) (K1 := K1)) hI
  (fun h => (mem_nonZeroDivisors_iff_ne_zero.mp h) rfl)

lemma bcI_mul (I J : FractionalIdeal (𝓞 K)⁰ K) : bcI (K1 := K1) (I * J) = bcI I * bcI J := FractionalIdeal.extended_mul ..

lemma bcI_spanSingleton (x : K) :
    bcI (K1 := K1) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 K1)⁰ (algebraMap K K1 x) := by
  rw [bcI, FractionalIdeal.extended_spanSingleton, locMap_eq]

lemma bcI_coeIdeal (J : Ideal (𝓞 K)) :
    bcI (K1 := K1) (J : FractionalIdeal (𝓞 K)⁰ K) = ((J.map (algebraMap (𝓞 K) (𝓞 K1)) : Ideal (𝓞 K1)) :
      FractionalIdeal (𝓞 K1)⁰ K1) := FractionalIdeal.extended_coeIdeal_eq_map _ _ _

lemma absNorm_coeIdeal' {F : Type} [Field F] [NumberField F] (J : Ideal (𝓞 F)) :
    FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) = (Ideal.absNorm J : ℚ) := FractionalIdeal.coeIdeal_absNorm J

lemma finrank_int_eq : Module.finrank (𝓞 K) (𝓞 K1) = Module.finrank K K1 := by
  have h1 := IsLocalization.finrank_eq (R := 𝓞 K) K (N := K1) (𝓞 K)⁰ le_rfl
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K1) (𝓞 K)⁰) K1 :=
    IsIntegralClosure.isLocalization (𝓞 K) K K1 (𝓞 K1)
  haveI : IsLocalizedModule (𝓞 K)⁰ (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K1) K1).toLinearMap :=
    (isLocalizedModule_iff_isLocalization).mpr hloc
  have h2 := IsLocalizedModule.finrank_eq (𝓞 K)⁰ (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K1) K1).toLinearMap le_rfl
  rw [h1, h2]

lemma norm_algebraMap_tower (x : K) :
    Algebra.norm ℚ (algebraMap K K1 x) = (Algebra.norm ℚ x) ^ Module.finrank K K1 := by
  rw [← Algebra.norm_norm (R := ℚ) (S := K) (a := algebraMap K K1 x), Algebra.norm_algebraMap, map_pow]

lemma absNorm_bcI (I : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.absNorm (bcI (K1 := K1) I) = (FractionalIdeal.absNorm I) ^ Module.finrank K K1 := by
  have hJ : ∀ J : Ideal (𝓞 K), FractionalIdeal.absNorm (bcI (K1 := K1) (J : FractionalIdeal (𝓞 K)⁰ K)) =
      FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) ^ Module.finrank K K1 := by
    intro J
    rw [bcI_coeIdeal, absNorm_coeIdeal', absNorm_coeIdeal']
    have h3 := Ideal.absNorm_relNorm (𝓞 K) (𝓞 K1) (J.map (algebraMap (𝓞 K) (𝓞 K1)))
    rw [Ideal.relNorm_algebraMap, map_pow, finrank_int_eq] at h3
    rw [← h3, Nat.cast_pow]
  have hx : ∀ x : K, FractionalIdeal.absNorm (bcI (K1 := K1) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) =
      FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) ^ Module.finrank K K1 := by
    intro x
    rw [bcI_spanSingleton, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.absNorm_span_singleton,
      norm_algebraMap_tower, abs_pow]
  have e := FractionalIdeal.den_mul_self_eq_num' (𝓞 K)⁰ K I
  have e1 := congrArg (fun J => FractionalIdeal.absNorm (bcI (K1 := K1) J)) e
  have e0 := congrArg FractionalIdeal.absNorm e
  simp only [bcI_mul, map_mul] at e1 e0
  rw [hx, hJ, ← e0, mul_pow] at e1
  have hne : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰
      (algebraMap (𝓞 K) K (I.den : 𝓞 K))) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  exact mul_left_cancel₀ (pow_ne_zero _ hne) e1

lemma card_fibre (σ : K →+* ℂ) :
    Nat.card {σ1 : K1 →+* ℂ // σ1.comp (algebraMap K K1) = σ} = Module.finrank K K1 := by
  letI : Algebra K ℂ := σ.toAlgebra
  have e : {σ1 : K1 →+* ℂ // σ1.comp (algebraMap K K1) = σ} ≃ (K1 →ₐ[K] ℂ) :=
    { toFun := fun s => { s.1 with commutes' := fun r => congrArg (fun g : K →+* ℂ => g r) s.2 }
      invFun := fun f => ⟨f.toRingHom, by ext r; exact f.commutes r⟩
      left_inv := fun s => by ext; rfl
      right_inv := fun f => by ext; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card]

lemma sum_comp_algebraMap (f : (K →+* ℂ) → ℝ) :
    ∑ σ1 : K1 →+* ℂ, f (σ1.comp (algebraMap K K1)) = (Module.finrank K K1 : ℝ) * ∑ σ : K →+* ℂ, f σ := by
  classical
  have h1 : ∀ σ : K →+* ℂ, (∑ σ1 : K1 →+* ℂ, if σ1.comp (algebraMap K K1) = σ then f σ else 0) =
      (Module.finrank K K1 : ℝ) * f σ := by
    intro σ
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have h := card_fibre (K1 := K1) σ
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    exact_mod_cast h
  calc ∑ σ1 : K1 →+* ℂ, f (σ1.comp (algebraMap K K1))
      = ∑ σ1 : K1 →+* ℂ, ∑ σ : K →+* ℂ, if σ1.comp (algebraMap K K1) = σ then f σ else 0 := by
        refine Finset.sum_congr rfl (fun σ1 _ => ?_)
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ σ : K →+* ℂ, ∑ σ1 : K1 →+* ℂ, if σ1.comp (algebraMap K K1) = σ then f σ else 0 := Finset.sum_comm
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => h1 σ)

end bc

theorem nondegenerate_base_change : NdegBaseChange := by
  intro K K1 _ _ _ _ _ L L1 hG hB
  have hI := eq_bcI hB
  have hn : ∀ σ, L1.n σ = L.n (σ.comp (algebraMap K K1)) := by
    unfold IsBaseChangeLine at hB
    exact hB.2
  unfold MLine.Good at hG ⊢
  refine ⟨⟨by rw [hI]; exact bcI_ne_zero hG.1, fun σ => by rw [hn]; exact hG.2 _⟩, ?_⟩
  unfold MLine.ndeg MLine.deg
  rw [hI, absNorm_bcI]
  simp only [hn]
  rw [show (∑ σ : K1 →+* ℂ, Real.log (L.n (σ.comp (algebraMap K K1)))) =
      (Module.finrank K K1 : ℝ) * ∑ σ : K →+* ℂ, Real.log (L.n σ) from
      sum_comp_algebraMap (fun σ => Real.log (L.n σ))]
  have hd : Module.finrank ℚ K1 = Module.finrank ℚ K * Module.finrank K K1 :=
    (Module.finrank_mul_finrank ℚ K K1).symm
  have hpos : (0:ℝ) < Module.finrank K K1 := by exact_mod_cast Module.finrank_pos
  have hpos2 : (0:ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [Rat.cast_pow, Real.log_pow, hd, Nat.cast_mul, div_eq_div_iff (mul_pos hpos2 hpos).ne' hpos2.ne']
  ring

theorem local_generator_base_change : LocGenBaseChange := by
  intro K K1 _ _ _ _ _ L L1 p p1 c hI hB hp hc
  obtain ⟨A, B, hA, hB', hAB⟩ := exists_split_of_isLocGen p hI hc
  have hc1 : algebraMap K K1 c ≠ 0 := (map_ne_zero _).mpr hc.1
  have hmap : ∀ X : Ideal (𝓞 K), ¬ X ≤ p.asIdeal → ¬ X.map (algebraMap (𝓞 K) (𝓞 K1)) ≤ p1.asIdeal := by
    intro X hX hle
    obtain ⟨x, hxX, hxp⟩ := SetLike.not_le_iff_exists.mp hX
    exact hxp ((hp x).mpr (hle (Ideal.mem_map_of_mem _ hxX)))
  have hne : ∀ X : Ideal (𝓞 K), ¬ X ≤ p.asIdeal →
      ((X.map (algebraMap (𝓞 K) (𝓞 K1)) : Ideal (𝓞 K1)) : FractionalIdeal (𝓞 K1)⁰ K1) ≠ 0 := by
    intro X hX h0
    rw [FractionalIdeal.coeIdeal_eq_zero] at h0
    exact hmap X hX (h0 ▸ bot_le)
  have h1 := congrArg (bcI (K1 := K1)) hAB
  rw [bcI_mul, bcI_mul, bcI_spanSingleton, bcI_coeIdeal, bcI_coeIdeal, ← eq_bcI hB] at h1
  have h2 := congrArg (FractionalIdeal.count K1 p1) h1
  rw [FractionalIdeal.count_mul K1 p1 (by rw [eq_bcI hB]; exact bcI_ne_zero hI) (hne B hB'),
    FractionalIdeal.count_mul K1 p1 (spanSingleton_ne_zero' hc1) (hne A hA),
    count_coeIdeal_eq_zero p1 (hmap A hA), count_coeIdeal_eq_zero p1 (hmap B hB')] at h2
  exact ⟨hc1, by omega⟩

end Formalism.L2.LamCM
