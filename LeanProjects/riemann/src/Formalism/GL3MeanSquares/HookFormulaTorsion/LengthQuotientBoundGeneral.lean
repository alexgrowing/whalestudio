import Mathlib
import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourierCommutesHeckeScalar
import Formalism.LogVandermondeBounds.LogVandermondeProofs.LengthQuotientLeOfLatticeSandwich

namespace Formalism.HermitianLattices.RamifiedHeckeModels

open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate

theorem cauchy_schwarz_bound : CauchySchwarzUnitModulus := by
  intro V _ _ y y' T ε hT hy hy'
  have he : ‖y'‖ = ‖y‖ :=
    (pow_left_inj₀ (norm_nonneg y') (norm_nonneg y) two_ne_zero).1 (hy'.trans hy.symm)
  refine ⟨?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hT.le]
    calc T * ‖inner ℂ y y'‖ ≤ T * (‖y‖ * ‖y'‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm y y') hT.le
      _ = 1 := by rw [he, ← sq, hy]; field_simp
  · intro hε h
    have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'

    rcases hε with rfl | rfl
    · have hi : inner ℂ y y' = ((1 / T : ℝ) : ℂ) := by
        push_cast; field_simp; rw [mul_comm]; exact h
      have hi' : inner ℂ y' y = ((1 / T : ℝ) : ℂ) := by
        rw [← inner_conj_symm, hi, Complex.conj_ofReal]
      have h0 : ‖y' - y‖ ^ 2 = 0 := by
        rw [@norm_sub_sq ℂ, hi', hy, hy']
        simp only [RCLike.re_to_complex, Complex.ofReal_re]
        ring
      rw [one_smul]
      exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))
    · have hi : inner ℂ y y' = ((-(1 / T) : ℝ) : ℂ) := by
        push_cast; field_simp; rw [mul_comm]; exact h
      have hi' : inner ℂ y' y = ((-(1 / T) : ℝ) : ℂ) := by
        rw [← inner_conj_symm, hi, Complex.conj_ofReal]
      have h0 : ‖y' + y‖ ^ 2 = 0 := by
        rw [@norm_add_sq ℂ, hi', hy, hy']
        simp only [RCLike.re_to_complex, Complex.ofReal_re]
        ring
      rw [neg_one_smul, ← sub_eq_zero, sub_neg_eq_add]
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)

theorem exponent_bounds : TableauExponentRange := by
  intro μ T j
  classical
  calc (μ.cells.filter (fun c => T c.1 c.2 = j)).card
      ≤ (Finset.range (μ.rowLen 0)).card := by

        apply Finset.card_le_card_of_injOn (fun c => c.2)
        · intro c hc
          simp only [Finset.coe_filter, Set.mem_setOf_eq, YoungDiagram.mem_cells] at hc
          simp only [Finset.coe_range, Set.mem_Iio]
          rw [← YoungDiagram.mem_iff_lt_rowLen]
          exact μ.up_left_mem (Nat.zero_le _) le_rfl hc.1
        · rintro ⟨a, k⟩ hc ⟨b, k'⟩ hd (hk : k = k')
          subst hk
          simp only [Finset.coe_filter, Set.mem_setOf_eq, YoungDiagram.mem_cells] at hc hd
          rcases lt_trichotomy a b with hab | rfl | hab
          · have := T.col_strict hab hd.1
            omega
          · rfl
          · have := T.col_strict hab hc.1
            omega
    _ = μ.rowLen 0 := Finset.card_range _

theorem ramified_decomposition : HeckeKernelPreservesRamified := by
  intro q _ n n' w ph hph fW
  simp only [kerK, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp_rw [Matrix.smul_vecMul]
  rw [← Finset.mul_sum, hph, mul_zero]

theorem logarithmic_bound : LogRatioAtMostOne := by
  intro q hq
  have h3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  rw [div_le_one (by linarith)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < q - 1 by linarith)
  linarith

theorem coprime_case_decomposition : ConjRatioPowUnitModulus := by
  intro z g hz
  have hc : conj z ≠ 0 := (map_ne_zero _).2 hz
  refine ⟨by rw [norm_pow, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hz), one_pow], ?_⟩
  rw [← mul_pow, pow_mul, Complex.normSq_eq_conj_mul_self]
  congr 1
  field_simp

theorem imprimitive_case_count : ImprimitiveOrbitCondition := by
  intro q _ n f e xz he hl ⟨z, hz, hz1⟩
  refine ⟨fun hall => ?_, fun j => ?_⟩
  ·
    choose a ha using hall
    have hz' : (z : ℚ) = ((q * ∑ j, a j * e j : ℤ) : ℚ) := by
      rw [← hz]
      push_cast
      simp [ha]
    have hz'' : z = q * ∑ j, a j * e j := by exact_mod_cast hz'
    rw [hz''] at hz1
    push_cast at hz1
    simp at hz1
  · have h := hl (Pi.single j (q : ℤ)) ?_
    · have hs : (∑ i, xz i * ((Pi.single j (q : ℤ) : Fin n → ℤ) i : ℚ)) = (q : ℚ) * xz j := by
        rw [Finset.sum_eq_single j]
        · simp [mul_comm]
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · simp
      rwa [hs] at h
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp

theorem prime_order_element : RationalMatrixPrimeOrderBound := by
  intro n p hp A hA h1
  classical
  haveI := Fact.mk hp
  have hint : IsIntegral ℚ A := Algebra.IsIntegral.isIntegral A
  have hm0 : minpoly ℚ A ≠ 0 := minpoly.ne_zero hint
  have hdvd : minpoly ℚ A ∣ Polynomial.cyclotomic p ℚ * (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_prime_mul_X_sub_one ℚ p]
    apply minpoly.dvd
    simp [hA]
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) := Polynomial.cyclotomic.irreducible_rat hp.pos

  have hcd : Polynomial.cyclotomic p ℚ ∣ minpoly ℚ A := by
    by_contra hnd
    have hcop : IsCoprime (Polynomial.cyclotomic p ℚ) (minpoly ℚ A) := hirr.coprime_iff_not_dvd.2 hnd
    have hX : minpoly ℚ A ∣ Polynomial.X - 1 := hcop.symm.dvd_of_dvd_mul_left hdvd
    apply h1
    have h0 := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hX (minpoly.aeval ℚ A)
    simpa [sub_eq_zero] using h0
  have hle1 := Polynomial.natDegree_le_of_dvd hcd hm0
  have hle2 : (minpoly ℚ A).natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly A) (Matrix.charpoly_monic A).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp] at hle1
  omega

theorem column_decomposition : LatticeColumnOperatorBound := by
  intro O L _ _ _ M _ _ _ _ S U K c ϖ e1 w h1 h2 h3
  classical
  set ϖL := algebraMap O L ϖ with hϖL
  have hsm : ∀ (i k : ℕ) (x : M i), ϖ ^ k • x = (ϖL ^ k) • x := by
    intro i k x
    rw [hϖL, ← map_pow, algebraMap_smul]

  have hG : ∀ m (x : M 0), U m (chainK L M K m x) =
      (∏ j ∈ range m, (c j : L)) • chainK L M K m (U 0 x) := by
    intro m
    induction m with
    | zero => intro x; simp [chainK]
    | succ m ih =>
      intro x
      have h := LinearMap.congr_fun (h1 m) (chainK L M K m x)
      simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
      show U (m + 1) (K m (chainK L M K m x)) = _ • K m (chainK L M K m (U 0 x))
      rw [h, ih, map_smul, smul_smul, Finset.prod_range_succ, mul_comm]
  have hQ : ∀ m, ∀ s ∈ S 0, ((ϖL ^ (m * e1)) * ∏ j ∈ range m, (c j : L) ^ (m - j)) •
      chainK L M K m ((U 0 ^ m) s) ∈ S m := by
    intro m
    induction m with
    | zero => intro s hs; simpa [chainK] using hs
    | succ m ih =>
      intro s hs
      have h := h2 m _ (ih s hs)
      rw [hsm] at h
      have hstep : ∀ y, U (m + 1) (K m (chainK L M K m y)) =
          (∏ j ∈ range (m + 1), (c j : L)) • chainK L M K (m + 1) (U 0 y) := fun y => hG (m + 1) y
      rw [map_smul, map_smul, hstep, smul_smul, smul_smul] at h
      convert h using 2
      · have hP : ∏ j ∈ range (m + 1), (c j : L) ^ (m + 1 - j) =
            (∏ j ∈ range m, (c j : L) ^ (m - j)) * ∏ j ∈ range (m + 1), (c j : L) := by
          rw [Finset.prod_range_succ (fun j => (c j : L) ^ (m + 1 - j)),
            Finset.prod_range_succ (fun j => (c j : L))]
          have hh : ∏ j ∈ range m, (c j : L) ^ (m + 1 - j) =
              (∏ j ∈ range m, (c j : L) ^ (m - j)) * ∏ j ∈ range m, (c j : L) := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun j hj => ?_
            rw [Finset.mem_range] at hj
            rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ]
          rw [hh, show m + 1 - m = 1 by omega, pow_one]
          ring
        rw [hP]
        ring
      · rw [pow_succ', Module.End.mul_apply]
  intro m s hs
  choose r hr using h3
  have hfin := (S m).smul_mem (∏ j ∈ range m, r j ^ (m - j)) (hQ m s hs)
  convert hfin using 1
  rw [hsm, ← algebraMap_smul L (∏ j ∈ range m, r j ^ (m - j)), smul_smul]
  congr 1
  rw [map_prod]
  simp only [map_pow, hr]
  rw [pow_add, ← Finset.prod_pow_eq_pow_sum]
  have hh : (∏ j ∈ range m, ((((c j)⁻¹ : Lˣ) : L) * ϖL ^ w j) ^ (m - j)) *
      ∏ j ∈ range m, (c j : L) ^ (m - j) = ∏ j ∈ range m, ϖL ^ ((m - j) * w j) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [mul_pow, mul_right_comm, ← mul_pow, Units.inv_mul, one_pow, one_mul, ← pow_mul, mul_comm (w j)]
  rw [← hh]
  ring

section LemmaC

open Formalism.LogVandermondeBounds.product_first_zeroth_parts Module

section
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {M : Type} [AddCommGroup M] [Module R M]

set_option maxHeartbeats 800000 in

theorem length_quotient_bound_general (ϖ : R) (hϖ : Irreducible ϖ) (S S0 B : Submodule R M) (U D : M →ₗ[R] M)
    (e : ℕ) (hSB : S0 ≤ B) (hU : B.map U ≤ S) (hD : S.map D ≤ B)
    (hUD : ∀ s ∈ S, U (D s) = ϖ ^ e • s) [Module.Free R S] [Module.Finite R S] :
    Module.length R (S ⧸ (S0.map U).comap S.subtype) ≤
      Module.length R (B ⧸ S0.comap B.subtype) + (e * Module.finrank R S : ℕ) := by
  classical
  set T1 : Submodule R S := (S0.map U).comap S.subtype with hT1
  set T2 : Submodule R S := (B.map U).comap S.subtype with hT2
  have h12 : T1 ≤ T2 := Submodule.comap_mono (Submodule.map_mono hSB)
  set Q : Submodule R (S ⧸ T1) := T2.map T1.mkQ with hQ

  have hsplit : Module.length R (S ⧸ T1) = Module.length R Q + Module.length R ((S ⧸ T1) ⧸ Q) :=
    Module.length_eq_add_of_exact Q.subtype Q.mkQ Q.injective_subtype Q.mkQ_surjective
      (LinearMap.exact_subtype_mkQ Q)
  rw [(Submodule.quotientQuotientEquivQuotient T1 T2 h12).length_eq] at hsplit

  have hlen2 : Module.length R (S ⧸ T2) ≤ (e * Module.finrank R S : ℕ) := by
    apply length_quot_le_of_pow_smul ϖ hϖ S T2 e
    intro x
    rw [hT2, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
    exact ⟨D x, hD (Submodule.mem_map_of_mem x.2), hUD x x.2⟩

  have hlen1 : Module.length R Q ≤ Module.length R (B ⧸ S0.comap B.subtype) := by
    let uB : B →ₗ[R] S := (U.domRestrict B).codRestrict S (fun b => hU (Submodule.mem_map_of_mem b.2))
    have huB : ∀ b : B, uB b ∈ T2 := fun b => by
      rw [hT2, Submodule.mem_comap]
      exact ⟨b, b.2, rfl⟩
    let ψ : B →ₗ[R] Q := (T1.mkQ ∘ₗ uB).codRestrict Q (fun b => Submodule.mem_map_of_mem (huB b))
    have hψ : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      rw [hT2, Submodule.mem_comap] at hx
      obtain ⟨b, hb, hbx⟩ := Submodule.mem_map.1 hx
      refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
      show T1.mkQ (uB ⟨b, hb⟩) = T1.mkQ x
      congr 1
      exact Subtype.ext hbx
    have hker : S0.comap B.subtype ≤ LinearMap.ker ψ := by
      intro b hb
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      show T1.mkQ (uB b) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hT1, Submodule.mem_comap]
      exact Submodule.mem_map_of_mem hb
    let φ := (S0.comap B.subtype).liftQ ψ hker
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨b, rfl⟩ := hψ y
      exact ⟨Submodule.Quotient.mk b, rfl⟩
    exact Module.length_le_of_surjective φ hφ
  rw [hsplit]
  exact add_le_add hlen1 hlen2

end

theorem lemma_c_under_twist : LemmaC_twist := by
  intro R _ _ _ ϖ hϖ M _ _ S B U D e b hSB hU hD hUD _ _
  have hmap : (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).map U = S.map ((ϖ ^ b) • U) := by
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  rw [← hmap]
  exact length_quotient_bound_general ϖ hϖ S _ B U D e hSB hU hD hUD

end LemmaC

end Formalism.HermitianLattices.RamifiedHeckeModels
