import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDlog
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDlogCoef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelEmbeddingInjectiveRangeAdjoinRootsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvOfFintype
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgZpOfPow
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.SiegLoc

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

section Coef

open Polynomial GlobalTheory.K5.DlogCoef GlobalTheory.K5.DlogUniq

theorem deriv_sum' {n N M : ℕ} (J : Ideal (On p n)) (D : Derivation (O0 p) (On p n) (On p n ⧸ J))
    (cx cy : On p n) (hx : D (xn p n) = Ideal.Quotient.mk J (cx * xn p n))
    (hy : D (yn p n) = Ideal.Quotient.mk J (cy * yn p n)) (a : Fin N → Fin M → O0 p) :
    D (∑ i : Fin N, ∑ j : Fin M,
        algebraMap (O0 p) (On p n) (a i j) * xn p n ^ (i : ℕ) * yn p n ^ (j : ℕ)) =
      Ideal.Quotient.mk J (∑ i : Fin N, ∑ j : Fin M,
        ((i : ℕ) * cx + (j : ℕ) * cy) * algebraMap (O0 p) (On p n) (a i j) * xn p n ^ (i : ℕ) *
          yn p n ^ (j : ℕ)) := by
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, Derivation.leibniz, Derivation.map_algebraMap, deriv_pow J D _ _ hx,
    deriv_pow J D _ _ hy, smul_zero, add_zero, smul_mk, smul_mk, smul_mk, ← map_add]
  congr 1
  ring

theorem coef {N M : ℕ} (m : ℕ) (a : Fin N → Fin M → O0 p) (w α β : On p (m + 1))
    (hsum : w = ∑ i : Fin N, ∑ j : Fin M,
      algebraMap (O0 p) (On p (m + 1)) (a i j) * xn p (m + 1) ^ (i : ℕ) * yn p (m + 1) ^ (j : ℕ))
    (h : IsDlog p (m + 1) w α β) :
    w * α - ∑ i : Fin N, ∑ j : Fin M, ((j : ℕ) : On p (m + 1)) * algebraMap (O0 p) (On p (m + 1)) (a i j) *
        xn p (m + 1) ^ (i : ℕ) * yn p (m + 1) ^ (j : ℕ) ∈ Ideal.span {(p : On p (m + 1)) ^ (m + 1)} ∧
    (w * β - ∑ i : Fin N, ∑ j : Fin M, ((i : ℕ) : On p (m + 1)) * algebraMap (O0 p) (On p (m + 1)) (a i j) *
        xn p (m + 1) ^ (i : ℕ) * yn p (m + 1) ^ (j : ℕ)) * (xn p (m + 1) ^ (p ^ m) - 1) ∈
      Ideal.span {(p : On p (m + 1)) ^ (m + 1)} := by
  have hxy : IsUnit (xn p (m + 1) * yn p (m + 1)) := (isUnit_xn p m).mul (isUnit_yn p (m + 1))
  constructor
  · obtain ⟨D, hx, hy⟩ := exists_derivation (cyclotomic (p ^ (m + 1)) (O0 p)) (p ^ (m + 1)) (qO p)
      (towerIdeal p (m + 1)) rfl (On p (m + 1) ⧸ Ideal.span {(p : On p (m + 1)) ^ (m + 1)}) 0
      (Ideal.Quotient.mk _ (yn p (m + 1))) (mul_zero _) (by
        have h0 := natCast_pow_quot (A := On p (m + 1)) p (m + 1)
        rw [mul_one] at h0
        rw [h0, zero_mul])
    change D (xn p (m + 1)) = 0 at hx
    change D (yn p (m + 1)) = _ at hy
    have hx' : D (xn p (m + 1)) = Ideal.Quotient.mk _ (0 * xn p (m + 1)) := by
      rw [zero_mul, map_zero]; exact hx
    have hy' : D (yn p (m + 1)) = Ideal.Quotient.mk _ (1 * yn p (m + 1)) := by
      rw [one_mul]; exact hy
    have hDw := deriv_sum' _ D 0 1 hx' hy' a
    rw [← hsum] at hDw
    simp only [mul_zero, zero_add, mul_one] at hDw
    have e2 := congrArg D.liftKaehlerDifferential h
    simp only [map_add, map_smul, Derivation.liftKaehlerDifferential_comp_D] at e2
    rw [hDw, hx', hy', smul_mk, smul_mk, smul_mk, ← map_add, Ideal.Quotient.eq] at e2
    refine (Ideal.unit_mul_mem_iff_mem _ hxy).1 ?_
    convert (Ideal.neg_mem_iff _).2 e2 using 1
    ring
  · obtain ⟨D, hx, hy⟩ := exists_derivation (cyclotomic (p ^ (m + 1)) (O0 p)) (p ^ (m + 1)) (qO p)
      (towerIdeal p (m + 1)) rfl
      (On p (m + 1) ⧸ Ideal.span {aeval (xn p (m + 1)) (derivative (cyclotomic (p ^ (m + 1)) (O0 p)))})
      (Ideal.Quotient.mk _ (xn p (m + 1))) 0 (by
        rw [Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) (mul_zero _)
    change D (xn p (m + 1)) = _ at hx
    change D (yn p (m + 1)) = 0 at hy
    have hx' : D (xn p (m + 1)) = Ideal.Quotient.mk _ (1 * xn p (m + 1)) := by
      rw [one_mul]; exact hx
    have hy' : D (yn p (m + 1)) = Ideal.Quotient.mk _ (0 * yn p (m + 1)) := by
      rw [zero_mul, map_zero]; exact hy
    have hDw := deriv_sum' _ D 1 0 hx' hy' a
    rw [← hsum] at hDw
    simp only [mul_zero, mul_one, add_zero] at hDw
    have e2 := congrArg D.liftKaehlerDifferential h
    simp only [map_add, map_smul, Derivation.liftKaehlerDifferential_comp_D] at e2
    rw [hDw, hx', hy', smul_mk, smul_mk, smul_mk, ← map_add, Ideal.Quotient.eq] at e2
    have e3 : (xn p (m + 1) * yn p (m + 1)) * (w * β - ∑ i : Fin N,
        ∑ j : Fin M, ((i : ℕ) : On p (m + 1)) * algebraMap (O0 p) (On p (m + 1)) (a i j) *
          xn p (m + 1) ^ (i : ℕ) * yn p (m + 1) ^ (j : ℕ)) ∈
        Ideal.span {aeval (xn p (m + 1)) (derivative (cyclotomic (p ^ (m + 1)) (O0 p)))} := by
      convert (Ideal.neg_mem_iff _).2 e2 using 1
      ring
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((Ideal.unit_mul_mem_iff_mem _ hxy).1 e3)
    rw [← hc, mul_assoc, derivative_cyclotomic_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

end Coef

theorem emb_int (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (z : On p L) : IsInt p (ι z) := by
  obtain ⟨b, -⟩ := GlobalTheory.K5.OnFree.on_free p L
  haveI : Module.Finite (O0 p) (On p L) := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral (O0 p) (On p L) := Algebra.IsIntegral.of_finite _ _
  exact IsIntegral.map ι (Algebra.IsIntegral.isIntegral z)

theorem isUnit_of_inv {L : ℕ} (ι : On p L →ₐ[O0 p] Ω) (hι : Function.Injective ι) (w : On p L) (h0 : ι w ≠ 0)
    (hi : IsInt p (ι w)⁻¹) : IsUnit w := by
  letI : Algebra (On p L) Ω := ι.toRingHom.toAlgebra
  haveI : IsScalarTower (O0 p) (On p L) Ω := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  have hi' : IsIntegral (On p L) (ι w)⁻¹ := IsIntegral.tower_top hi
  haveI : FaithfulSMul (On p L) (integralClosure (On p L) Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b hab => hι (congrArg Subtype.val hab)
  have hu : IsUnit (algebraMap (On p L) (integralClosure (On p L) Ω) w) :=
    IsUnit.of_mul_eq_one ⟨_, hi'⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  haveI : IsLocalHom (algebraMap (On p L) (integralClosure (On p L) Ω)) :=
    Algebra.IsIntegral.isLocalHom _ _
  exact isUnit_of_map_unit _ _ hu

theorem isAlgZp_int (u : ℤ) : IsAlgZp p (u : Ω) :=
  ⟨Polynomial.X - Polynomial.C (u : ℤ_[p]), Polynomial.X_sub_C_ne_zero _, by simp⟩

theorem zeta_one (T : GlobalTheory.K5.Tower p Ω) (k : ℕ) : T.ζ (k + 1) ^ p ^ k = T.ζ 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, T.ζpow, ih]

theorem zpow_emod {z : Ω} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) (r : ℤ) : z ^ r = z ^ (r % (N : ℤ)).toNat := by
  have h0 : 0 ≤ r % (N : ℤ) := Int.emod_nonneg r (by exact_mod_cast hN.ne')
  have hne : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hz
    exact zero_ne_one hz
  rw [← zpow_natCast z, Int.toNat_of_nonneg h0]
  conv_lhs => rw [← Int.emod_add_mul_ediv r (N : ℤ)]
  rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hz, one_zpow, mul_one]

theorem coeff_mul_finsum (C D : HahnSeries ℤ Ω) (r : ℤ) :
    (C * D).coeff r = ∑ᶠ i : ℤ, C.coeff i * D.coeff (r - i) := by
  classical
  rw [HahnSeries.coeff_mul, finsum_eq_sum_of_support_subset
    (s := (Finset.addAntidiagonal C.isPWO_support D.isPWO_support r).image Prod.fst)]
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun ij hij => ?_
      replace hij := Finset.mem_addAntidiagonal.1 hij
      rw [← hij.2.2, add_sub_cancel_left]
    · intro a ha b hb hab
      replace ha := Finset.mem_addAntidiagonal.1 (Finset.mem_coe.1 ha)
      replace hb := Finset.mem_addAntidiagonal.1 (Finset.mem_coe.1 hb)
      refine Prod.ext hab ?_
      have := ha.2.2.trans hb.2.2.symm
      rw [hab] at this
      exact add_left_cancel this
  · intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨(i, r - i), Finset.mem_addAntidiagonal.2 ⟨left_ne_zero_of_mul hi, right_ne_zero_of_mul hi, by simp⟩, rfl⟩

def ofInt (f : ℤ → ℤ) (r0 : ℤ) (hf : ∀ r, r < r0 → f r = 0) : Lau p where
  coeff r := (f r : ℤ_[p])
  isPWO_support' := Set.IsWF.isPWO (BddBelow.wellFoundedOn_lt ⟨r0, fun j hj => not_lt.1 fun h => hj (by simp [hf j h])⟩)

theorem ofInt_coeff (f : ℤ → ℤ) (r0 : ℤ) (hf : ∀ r, r < r0 → f r = 0) (r : ℤ) :
    (ofInt (p := p) f r0 hf).coeff r = (f r : ℤ_[p]) := rfl

theorem ev_cyc (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) (ψ : O0 p →+* Ω) (c : ℤ → Ω) (h0 : ∀ r : ℤ, r < 0 → c r = 0)
    (hc : ∀ r : ℤ, c r ∈ Subring.closure {T.ζ L}) : ∃ z z', Ev ψ c z z' := by
  have hN : 0 < p ^ L := pow_pos hp.out.pos L
  have hζ : T.ζ L ^ p ^ L = 1 := (T.prim L).pow_eq_one
  have key : ∀ r : ℤ, ∃ n : Fin (p ^ L) → ℤ, c r = ∑ m : Fin (p ^ L), T.ζ L ^ (m : ℕ) * (n m : Ω) ∧ (r < 0 → n = 0) := by
    intro r
    by_cases hr : r < 0
    · exact ⟨0, by simp [h0 r hr], fun _ => rfl⟩
    · have h1 : c r ∈ Algebra.adjoin ℤ {T.ζ L} :=
        (Subring.closure_le (t := (Algebra.adjoin ℤ {T.ζ L}).toSubring)).2 Algebra.subset_adjoin (hc r)
      rw [Algebra.adjoin_singleton_eq_range_aeval] at h1
      obtain ⟨f, hf⟩ := h1
      have hm : (Polynomial.X ^ (p ^ L) - Polynomial.C 1 : Polynomial ℤ).Monic := Polynomial.monic_X_pow_sub_C _ hN.ne'
      have hd : (f %ₘ (Polynomial.X ^ (p ^ L) - Polynomial.C 1)).natDegree < p ^ L := by
        have := Polynomial.natDegree_modByMonic_lt f hm (by
          intro h
          have := congrArg Polynomial.natDegree h
          rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_one] at this
          exact hN.ne' this)
        rwa [Polynomial.natDegree_X_pow_sub_C] at this
      refine ⟨fun m => (f %ₘ (Polynomial.X ^ (p ^ L) - Polynomial.C 1)).coeff m, ?_, fun h => absurd h hr⟩
      have e : Polynomial.aeval (T.ζ L) (f %ₘ (Polynomial.X ^ (p ^ L) - Polynomial.C 1)) = Polynomial.aeval (T.ζ L) f := by
        conv_rhs => rw [← Polynomial.modByMonic_add_div f (Polynomial.X ^ (p ^ L) - Polynomial.C 1)]
        simp [hζ]
      rw [← hf]
      show Polynomial.aeval (T.ζ L) f = _
      rw [← e, Polynomial.aeval_eq_sum_range' hd, Finset.sum_range]
      exact Finset.sum_congr rfl fun m _ => by rw [zsmul_eq_mul, mul_comm]
  choose n hn hn0 using key
  have hz : ∀ i : ℕ, (T.ζ L ^ i) ^ p ^ L = 1 := fun i => by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  refine ⟨_, _, EvRing.ev_of_fintype ψ c _ _ (fun m : Fin (p ^ L) => T.ζ L ^ (m : ℕ))
    (fun m => ofInt (fun r => n r m) 0 fun r hr => by rw [hn0 r hr]; rfl)
    (fun m => ⟨EvTwist.isInt_of_pow hN (hz _), EvTwist.isAlgZp_of_pow hN (hz _)⟩) (fun r => ?_) rfl rfl⟩
  rw [hn r]
  exact Finset.sum_congr rfl fun m _ => by rw [ofInt_coeff, EvRing.zp_eq, map_intCast]

theorem psi_part {T : GlobalTheory.K5.Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T n ψ) (i : ℕ) (a : Lau p) :
    ∃ b : O0 p, ψ (algebraMap (Lau p) (O0 p) (EvTwist.part ((p ^ n : ℕ) : ℤ) (i : ℤ) a)) =
      T.qq n ^ i * algebraMap (O0 p) Ω b := by
  set c := EvTwist.part ((p ^ n : ℕ) : ℤ) (i : ℤ) a with hc
  set B : Lau p := HahnSeries.single (-(i : ℤ)) 1 * c with hB
  have hcB : c = HahnSeries.single (1 : ℤ) (1 : ℤ_[p]) ^ i * B := by
    rw [hB, ← mul_assoc, HahnSeries.single_pow, HahnSeries.single_mul_single]
    simp [HahnSeries.single_zero_one]
  have hBc : ∀ r : ℤ, B.coeff r = c.coeff (r + i) := fun r => by
    have := HahnSeries.coeff_single_mul_add (r := (1 : ℤ_[p])) (x := c) (a := r + i) (b := -(i : ℤ))
    rw [one_mul, add_neg_cancel_right] at this
    exact this
  have hpos : (0 : ℤ) < (p : ℤ) ^ n := pow_pos (by exact_mod_cast hp.out.pos) n
  have hs := hψ.sub (EvTwist.contr ((p : ℤ) ^ n) hpos B) B (fun _ => rfl) (fun r hr => by
    rw [hBc, hc, EvTwist.part_coeff, if_neg]
    intro h
    apply hr
    have := Int.emod_add_mul_ediv (r + i) ((p ^ n : ℕ) : ℤ)
    rw [h] at this
    push_cast at this
    exact ⟨(r + i) / (p : ℤ) ^ n, by linarith⟩)
  have hq : ψ (algebraMap (Lau p) (O0 p) (HahnSeries.single (1 : ℤ) (1 : ℤ_[p]))) = T.qq n := hψ.par
  exact ⟨_, by rw [hcB, map_mul, map_mul, map_pow, map_pow, hq, hs]⟩

theorem rep {T : GlobalTheory.K5.Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (g : ℤ) (θ : ℤ → ℤ → ℤ) (S : ℤ → Finset ℤ)
    (r0 : ℤ) (h0 : ∀ k r : ℤ, r < r0 → θ k r = 0) :
    ∃ a : Fin (p ^ L) → Fin (p ^ L) → O0 p, ∀ u : ℕ → ℕ → ℤ, ∃ y',
      Ev ψ (fun r => ∑ k ∈ S r, (u (g * k % ((p ^ L : ℕ) : ℤ)).toNat (r % ((p ^ L : ℕ) : ℤ)).toNat : Ω) * (θ k r : Ω) *
          T.ζ L ^ (g * k))
        (∑ m : Fin (p ^ L), ∑ j : Fin (p ^ L),
          (u m j : Ω) * algebraMap (O0 p) Ω (a m j) * T.ζ L ^ (m : ℕ) * T.qq L ^ (j : ℕ)) y' := by
  have hN : 0 < p ^ L := pow_pos hp.out.pos L
  have hζ : T.ζ L ^ p ^ L = 1 := (T.prim L).pow_eq_one
  have hz : ∀ i : ℕ, (T.ζ L ^ i) ^ p ^ L = 1 := fun i => by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  let b : Fin (p ^ L) → Lau p := fun m =>
    ofInt (fun r => ∑ k ∈ S r, if g * k % ((p ^ L : ℕ) : ℤ) = ((m : ℕ) : ℤ) then θ k r else 0) r0
      fun r hr => Finset.sum_eq_zero fun k _ => by simp [h0 k r hr]
  choose a ha using fun (m j : Fin (p ^ L)) => psi_part hψ j (b m)
  refine ⟨a, fun u => ⟨_, EvRing.ev_of_fintype (ι := Fin (p ^ L) × Fin (p ^ L)) ψ _ _ _
    (fun s => (u s.1 s.2 : Ω) * T.ζ L ^ (s.1 : ℕ)) (fun s => EvTwist.part ((p ^ L : ℕ) : ℤ) ((s.2 : ℕ) : ℤ) (b s.1))
    (fun s => ⟨IsIntegral.mul (Basic.isInt_intCast _) (EvTwist.isInt_of_pow hN (hz _)),
      EvRing.isAlgZp_mul (isAlgZp_int _) (EvTwist.isAlgZp_of_pow hN (hz _))⟩) (fun r => ?_) ?_ rfl⟩⟩
  · rw [Fintype.sum_prod_type]
    have h1 : ∀ m j : Fin (p ^ L), (u m j : Ω) * T.ζ L ^ (m : ℕ) *
        zp Ω ((EvTwist.part ((p ^ L : ℕ) : ℤ) ((j : ℕ) : ℤ) (b m)).coeff r) =
        if r % ((p ^ L : ℕ) : ℤ) = ((j : ℕ) : ℤ) then (u m j : Ω) * T.ζ L ^ (m : ℕ) * zp Ω ((b m).coeff r) else 0 := fun m j => by
      rw [EvTwist.part_coeff]
      split_ifs
      · rfl
      · rw [EvRing.zp_eq, map_zero, mul_zero]
    have h2 : ∀ m : Fin (p ^ L), ∑ j : Fin (p ^ L), (u m j : Ω) * T.ζ L ^ (m : ℕ) *
        zp Ω ((EvTwist.part ((p ^ L : ℕ) : ℤ) ((j : ℕ) : ℤ) (b m)).coeff r) =
        ∑ k ∈ S r, if g * k % ((p ^ L : ℕ) : ℤ) = ((m : ℕ) : ℤ) then
          (u m (r % ((p ^ L : ℕ) : ℤ)).toNat : Ω) * (θ k r : Ω) * T.ζ L ^ (m : ℕ) else 0 := fun m => by
      simp only [h1]
      rw [EvTwist.sum_ite (p ^ L) hN r (fun j => (u m j : Ω) * T.ζ L ^ (m : ℕ) * zp Ω ((b m).coeff r)),
        ofInt_coeff, EvRing.zp_eq, map_intCast, Int.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs
      · ring
      · simp
    simp only [h2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [EvTwist.sum_ite (p ^ L) hN (g * k)
      (fun m => (u m (r % ((p ^ L : ℕ) : ℤ)).toNat : Ω) * (θ k r : Ω) * T.ζ L ^ m), ← zpow_emod hN hζ]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ha]
    ring

theorem cong_sum {L : ℕ} (S : Finset ℤ) (v : ℤ → ℤ) (e : ℤ → Ω) (he : ∀ k, IsInt p (e k)) (hv : ∀ k, (p : ℤ) ^ L ∣ v k) :
    Cong p L (∑ k ∈ S, (v k : Ω) * e k) 0 := by
  choose c hc using hv
  refine ⟨∑ k ∈ S, (c k : Ω) * e k, IsIntegral.sum _ fun k _ => IsIntegral.mul (Basic.isInt_intCast _) (he k), ?_⟩
  rw [sub_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hc k]
  push_cast
  ring

theorem cong_val (hc : IsClo p Ω) {T : GlobalTheory.K5.Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (g A : ℤ)
    (θ v : ℤ → ℤ → ℤ) (S : ℤ → Finset ℤ) (cU cE : ℤ → Ω) (x x' z z' y y' : Ω)
    (hv : ∀ k r, θ k r ≠ 0 → (p : ℤ) ^ L ∣ v k r - A * k)
    (hE : ∀ r, ∑ k ∈ S r, ((k * θ k r : ℤ) : Ω) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i))
    (hx : Ev ψ cU x x') (hz : Ev ψ cE z z')
    (hy : Ev ψ (fun r => ∑ k ∈ S r, (v k r : Ω) * (θ k r : Ω) * T.ζ L ^ (g * k)) y y') :
    Cong p L (y + A * (z * x)) 0 := by
  have hN : 0 < p ^ L := pow_pos hp.out.pos L
  have hζ : T.ζ L ^ p ^ L = 1 := (T.prim L).pow_eq_one
  obtain ⟨R1, R2⟩ := EvRing.ev_ring p Ω hc T L ψ hψ
  obtain ⟨U, rfl⟩ := (R2 _ _ _ hx).2.2.1
  obtain ⟨E, rfl⟩ := (R2 _ _ _ hz).2.2.1
  obtain ⟨Y, hY⟩ := (R2 _ _ _ hy).2.2.1
  have h1 := (R2 _ _ _ (R1 E U _ _ _ _ hz hx).1).2.2.2.2.1 (A : Ω) (Basic.isInt_intCast _) (isAlgZp_int _)
  obtain ⟨V, hV⟩ := (R2 _ _ _ h1).2.2.1
  rw [← hV] at h1
  rw [← hY] at hy
  refine ((GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ω hc T L ψ hψ L _ _ _ (R1 Y V _ _ _ _ hy h1).2.1).1).2 fun r => ?_
  have e : (Y + V).coeff r = ∑ k ∈ S r, (((v k r - A * k) * θ k r : ℤ) : Ω) * T.ζ L ^ (g * k) := by
    rw [HahnSeries.coeff_add, hY, hV]
    simp only
    rw [coeff_mul_finsum, ← neg_eq_iff_eq_neg.2 (hE r), mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [e]
  refine cong_sum _ (fun k => (v k r - A * k) * θ k r) _ (fun k => ?_) fun k => ?_
  · rw [zpow_emod hN hζ]
    exact IsIntegral.pow (EvTwist.isInt_of_pow hN hζ) _
  · by_cases h : θ k r = 0
    · simp [h]
    · exact Dvd.dvd.mul_right (hv k r h) _

theorem local_coords : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (L : ℕ) (ψ : O0 p →+* Ωl) (ι : On p L →ₐ[O0 p] Ωl), 1 ≤ L → IsReb T L ψ → IsEmb T L ι →
  ∀ (A₁ g : ℤ) (θ : ℤ → ℤ → ℤ) (cU cE : ℤ → Ωl) (x x' : Ωl),
  (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) →
  (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) →
  (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) →
  (∀ r : ℤ, cU r = ∑ᶠ k : ℤ, (θ k r : Ωl) * T.ζ L ^ (g * k)) →
  (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ωl) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i)) →
  (∀ r : ℤ, r < 0 → cE r = 0) → (∀ r : ℤ, cE r ∈ Subring.closure {T.ζ L}) →
  Ev ψ cU x x' → x ≠ 0 → IsInt p x⁻¹ →
  ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = x ∧ Ev ψ cE z z' ∧
    Cong p L (ι α) (-(A₁ : Ωl) * z) ∧ Cong p L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
  intro p hp Ω _ _ hc T L ψ ι hL hψ hι A₁ g θ cU cE x x' hB ⟨r0, h0⟩ hdiv hU hE hE0 hEm hx hx0 hxi
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  choose B hB using hB
  let S : ℤ → Finset ℤ := fun r => Finset.Icc (-(B r : ℤ)) (B r)
  have hS : ∀ (r : ℤ) (f : ℤ → Ω), (∀ k, θ k r = 0 → f k = 0) → ∑ᶠ k, f k = ∑ k ∈ S r, f k := fun r f hf =>
    finsum_eq_sum_of_support_subset _ fun k hk => by
      rw [Finset.mem_coe, Finset.mem_Icc, ← abs_le]
      exact not_lt.1 fun h => hk (hf k (hB r k h))
  have hE' : ∀ r, ∑ k ∈ S r, ((k * θ k r : ℤ) : Ω) * T.ζ (m + 1) ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i) := fun r => by
    rw [← hE r, hS r _ fun k hk => by simp [hk]]
  obtain ⟨z, z', hz⟩ := ev_cyc T (m + 1) ψ cE hE0 hEm
  obtain ⟨a, ha⟩ := rep hψ g θ S r0 h0
  obtain ⟨y0, e0⟩ := ha fun _ _ => 1
  obtain ⟨y1, e1⟩ := ha fun _ j => j
  obtain ⟨y2, e2⟩ := ha fun i _ => i
  have hN : (0 : ℤ) < ((p ^ (m + 1) : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.out.pos _
  have hmod : ∀ r : ℤ, (p : ℤ) ^ (m + 1) ∣ ((r % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ) - r := fun r => by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg r hN.ne')]
    have := Int.emod_add_mul_ediv r ((p ^ (m + 1) : ℕ) : ℤ)
    push_cast at this ⊢
    exact ⟨-(r / (p : ℤ) ^ (m + 1)), by linarith⟩
  obtain ⟨c1, hc1, k1⟩ := cong_val hc hψ g A₁ θ (fun _ r => ((r % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ)) S cU cE x x' z z' _ _
    (fun k r h => by simpa using dvd_add (hmod r) (hdiv k r h)) hE' hx hz e1
  obtain ⟨c2, hc2, k2⟩ := cong_val hc hψ g g θ (fun k _ => ((g * k % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ)) S cU cE x x' z z' _ _
    (fun k r _ => hmod _) hE' hx hz e2
  have hcU : cU = fun r => ∑ k ∈ S r, ((1 : ℤ) : Ω) * (θ k r : Ω) * T.ζ (m + 1) ^ (g * k) := funext fun r => by
    rw [hU r, hS r _ fun k hk => by simp [hk]]
    simp
  rw [← hcU] at e0
  have hxe := (GlobalTheory.T.evalSeriesAndDeriv_unique_of_coefficients p Ω hc T (m + 1) ψ hψ _ _ _ _ _ hx e0).1
  set w0 : On p (m + 1) := ∑ i : Fin (p ^ (m + 1)), ∑ j : Fin (p ^ (m + 1)),
    algebraMap (O0 p) (On p (m + 1)) (a i j) * xn p (m + 1) ^ (i : ℕ) * yn p (m + 1) ^ (j : ℕ) with hw0
  have hw : ι w0 = x := by
    rw [hxe, hw0]
    simp only [map_sum, map_mul, map_pow, AlgHom.commutes, hι.1, hι.2, Int.cast_one, one_mul]
  obtain ⟨w, hwu⟩ := isUnit_of_inv ι (GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hc T (m + 1) hL ι hι).1 w0 (hw ▸ hx0) (hw ▸ hxi)
  obtain ⟨α, β, hd⟩ := GlobalTheory.K5.exists_isDlog p (m + 1) w
  obtain ⟨d1, d2⟩ := coef m a w α β (hwu.trans hw0) hd
  obtain ⟨f1, d1⟩ := Ideal.mem_span_singleton'.1 d1
  obtain ⟨f2, d2⟩ := Ideal.mem_span_singleton'.1 d2
  replace d1 := congrArg ι d1
  replace d2 := congrArg ι d2
  simp only [map_sum, map_mul, map_pow, map_sub, map_natCast, map_one, AlgHom.commutes, hι.1, hι.2, hwu, hw, zeta_one] at d1 d2
  simp only [Int.cast_natCast] at k1 k2
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  refine ⟨w, α, β, z, z', hd, hwu ▸ hw, hz, ⟨(ι f1 + c1) * x⁻¹,
    IsIntegral.mul (IsIntegral.add (emb_int _ ι _) hc1) hxi, ?_⟩, ?_⟩
  · linear_combination x⁻¹ * k1 - x⁻¹ * d1 - (ι α + A₁ * z) * hinv
  · have hζ1 : T.ζ 1 - 1 ≠ 0 := sub_ne_zero.2 ((T.prim 1).ne_one (by simpa using hp.out.one_lt))
    have hpd := GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T 1 1 le_rfl (Nat.totient_pos.2 (pow_pos hp.out.pos _))
    rw [pow_one, div_eq_mul_inv] at hpd
    have hinv2 : (T.ζ 1 - 1) * (T.ζ 1 - 1)⁻¹ = 1 := mul_inv_cancel₀ hζ1
    have hpi : IsInt p (p : Ω) := by simpa using Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    refine ⟨(ι f2 * ((p : Ω) * (T.ζ 1 - 1)⁻¹) + p * c2) * x⁻¹,
      IsIntegral.mul (IsIntegral.add (IsIntegral.mul (emb_int _ ι _) hpd) (IsIntegral.mul hpi hc2)) hxi, ?_⟩
    generalize (∑ i : Fin (p ^ (m + 1)), ∑ j : Fin (p ^ (m + 1)),
      ((i : ℕ) : Ω) * algebraMap (O0 p) Ω (a i j) * T.ζ (m + 1) ^ (i : ℕ) * T.qq (m + 1) ^ (j : ℕ)) = Y at k2 d2
    linear_combination (p * x⁻¹) * k2 - (p * x⁻¹ * (T.ζ 1 - 1)⁻¹) * d2 - (p * x⁻¹ * (x * ι β - Y)) * hinv2
      - (p * (ι β + g * z)) * hinv

end GlobalTheory.Glue.SiegLoc
