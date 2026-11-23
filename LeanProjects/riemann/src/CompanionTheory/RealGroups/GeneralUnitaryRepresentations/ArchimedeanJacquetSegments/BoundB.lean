import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary
import GroundTheory.AutomorphicForms.IwahoriFactorization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfFixedMemSpanTranslates
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvectorLiftOfSurjectionStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace CompanionTheory.RgGu.NR.BoundB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_one (t : kˣ) (h : nabs k t ≤ 1) : valuation k (t : k) ≤ 1 := by
  have hq : (1 : ℝ) < (resCard k : ℝ) := by exact_mod_cast one_lt_resCard k
  rw [GlobalTheory.LGrp.nabs_eq_zpow] at h
  have hord : 0 ≤ GlobalTheory.SmGL.ord k t := by
    by_contra hc
    push_neg at hc
    have : (1 : ℝ) < (resCard k : ℝ) ^ (-GlobalTheory.SmGL.ord k t) := one_lt_zpow₀ hq (by omega)
    linarith
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (t : k)) ≠ 0 := by simp
  have hl : WithZero.log (φ (valuation k (t : k))) ≤ 0 := by
    have : GlobalTheory.SmGL.ord k t = -WithZero.log (φ (valuation k (t : k))) := rfl
    omega
  have : φ (valuation k (t : k)) ≤ φ 1 := by
    rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    exact hl
  exact φ.strictMono.le_iff_le.1 this

def zd (d : ℕ) (t : kˣ) (i : Fin (d + d)) : kˣ := if blk (blk2 d) i = 0 then t else 1

def Zt (d : ℕ) (t : kˣ) : GL (Fin (d + d)) k := diagT k (Fin (d + d)) (zd d t)

theorem Zt_val (d : ℕ) (t : kˣ) : ((Zt d t : GL (Fin (d + d)) k) : Matrix (Fin (d + d)) (Fin (d + d)) k) =
    diagonal fun i => ((zd d t i : kˣ) : k) := by
  rw [Zt, val_diagT]

theorem Zt_inv_val (d : ℕ) (t : kˣ) :
    (((Zt d t)⁻¹ : GL (Fin (d + d)) k) : Matrix (Fin (d + d)) (Fin (d + d)) k) =
      diagonal fun i => (((zd d t i)⁻¹ : kˣ) : k) := by
  rw [Zt, ← map_inv, val_diagT]
  rfl

theorem Zt_mem (d : ℕ) (t : kˣ) : Zt d t ∈ parab k (blk2 d) := by
  show ((Zt d t : GL (Fin (d + d)) k) : Matrix (Fin (d + d)) (Fin (d + d)) k).BlockTriangular (blk (blk2 d))
  intro i j hij
  rw [Zt_val, diagonal_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

theorem leviProj_Zt (d : ℕ) (t : kˣ) :
    leviProj k (blk2 d) ⟨Zt d t, Zt_mem d t⟩ = ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] := by
  funext a
  ext i j
  rw [leviProj_apply]
  simp only [Zt_val, diagonal_apply, (blk2 d).injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and, zd,
    blk_apply]
  fin_cases a
  · simp [Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, Matrix.diagonal_apply]
  · simp [Matrix.one_apply]

theorem conj_mem (d : ℕ) (t : kˣ) (ht : valuation k (t : k) ≤ 1) {m : ℕ} {z : GL (Fin (d + d)) k}
    (hz : z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m)
    (hzo : z ∈ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k (d + d) (blk (blk2 d))) :
    ∀ i j, valuation k ((((Zt d t)⁻¹ * z * Zt d t : GL (Fin (d + d)) k) : Matrix _ _ k) i j -
        (1 : Matrix (Fin (d + d)) (Fin (d + d)) k) i j) ≤
          valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ m ∧
      (((Zt d t)⁻¹ * z * Zt d t : GL (Fin (d + d)) k) : Matrix _ _ k) i j ∈ 𝒪[k] := by
  intro i j
  obtain ⟨hzi, hzc⟩ := (GroundTheory.Automorphic.GLnLocal.mem_congruenceSubgroup_iff k (d + d)).1 hz
  obtain ⟨hzl, hzd⟩ := GroundTheory.Automorphic.Parabolic.mem_oppositeUnipotentRadical.1 hzo
  have hzint := ((GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff k (d + d)).1 hzi).1
  have e : (((Zt d t)⁻¹ * z * Zt d t : GL (Fin (d + d)) k) : Matrix _ _ k) i j =
      (((zd d t i)⁻¹ : kˣ) : k) * (z : Matrix _ _ k) i j * ((zd d t j : kˣ) : k) := by
    rw [Units.val_mul, Units.val_mul, Zt_inv_val, Zt_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [e]
  rcases lt_trichotomy (blk (blk2 d) i) (blk (blk2 d) j) with hlt | heq | hgt
  · rw [hzl i j hlt, mul_zero, zero_mul, Matrix.one_apply_ne (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)]
    simp
  · have hzz : zd d t i = zd d t j := by simp [zd, heq]
    rw [hzz, mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
    exact ⟨hzc i j, hzint i j⟩
  · have hi : blk (blk2 d) i = 1 := by
      have := (blk (blk2 d) i).isLt; have := (blk (blk2 d) j).isLt
      ext; simp only [Fin.lt_iff_val_lt_val] at hgt; omega
    have hj : blk (blk2 d) j = 0 := by
      have := (blk (blk2 d) j).isLt
      ext; simp only [Fin.lt_iff_val_lt_val] at hgt; omega
    have hij : i ≠ j := fun h => by rw [h] at hgt; exact lt_irrefl _ hgt
    rw [Matrix.one_apply_ne hij, sub_zero]
    simp only [zd, hi, hj, if_pos, one_ne_zero, if_false, inv_one, Units.val_one, one_mul]
    have h1 := hzc i j
    rw [Matrix.one_apply_ne hij, sub_zero] at h1
    refine ⟨?_, ?_⟩
    · rw [map_mul]
      calc valuation k ((z : Matrix _ _ k) i j) * valuation k (t : k)
          ≤ valuation k ((z : Matrix _ _ k) i j) * 1 := by gcongr
        _ = _ := mul_one _
        _ ≤ _ := h1
    · exact Subring.mul_mem _ (hzint i j) ((Valuation.mem_integer_iff _ _).2 ht)

theorem conj_mem' (d : ℕ) (t : kˣ) (ht : valuation k (t : k) ≤ 1) {m : ℕ} {z : GL (Fin (d + d)) k}
    (hz : z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m ⊓
      GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k (d + d) (blk (blk2 d))) :
    (Zt d t)⁻¹ * z * Zt d t ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m := by
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
  have hz1' := Subgroup.inv_mem _ hz1
  have hz2' := Subgroup.inv_mem _ hz2
  rw [GroundTheory.Automorphic.GLnLocal.mem_congruenceSubgroup_iff, GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff]
  refine ⟨⟨fun i j => (conj_mem d t ht hz1 hz2 i j).2, fun i j => ?_⟩, fun i j => (conj_mem d t ht hz1 hz2 i j).1⟩
  have e : ((Zt d t)⁻¹ * z * Zt d t)⁻¹ = (Zt d t)⁻¹ * z⁻¹ * Zt d t := by group
  rw [e]
  exact (conj_mem d t ht hz1' hz2' i j).2

section Rep

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def avL (π : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] : Module.End ℂ V :=
  ∑ q : K ⧸ H, π ((q.out : K) : G)

theorem avL_apply (π : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] (x : V) :
    avL π K H x = ∑ q : K ⧸ H, π ((q.out : K) : G) x := by
  simp [avL, LinearMap.sum_apply]

theorem avL_fixed (π : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] {x : V}
    (hx : ∀ h ∈ H, π ((h : K) : G) x = x) (κ : G) (hκ : κ ∈ K) : π κ (avL π K H x) = avL π K H x := by
  classical
  rw [avL_apply, map_sum]
  let κ' : K := ⟨κ, hκ⟩
  have key : ∀ q : K ⧸ H, π κ (π ((q.out : K) : G) x) = π (((κ' • q).out : K) : G) x := by
    intro q
    rw [← Module.End.mul_apply, ← map_mul]
    have : ((κ * ((q.out : K) : G)) : G) = ((κ' * q.out : K) : G) := rfl
    rw [this]
    apply GlobalTheory.HeckeAvg.fix_eq hx
    rw [QuotientGroup.out_eq']
    show ((κ' * q.out : K) : K ⧸ H) = κ' • q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [Finset.sum_congr rfl fun q _ => key q]
  exact Fintype.sum_equiv (MulAction.toPerm κ') _ _ (fun q => rfl)

end Rep

section Gen

variable {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X]

theorem hfixH (π : Representation ℂ G X) (K : Subgroup G) (Z : G) (x : X) (hx : ∀ κ ∈ K, π κ x = x)
    (h : K) (hh : h ∈ (K.map (MulAut.conj Z).toMonoidHom).subgroupOf K) :
    π (h : G) (π Z x) = π Z x := by
  have hm' : Z⁻¹ * (h : G) * Z ∈ K := GlobalTheory.HeckeAvg.mem_conj.1 hh
  have e : (h : G) * Z = Z * (Z⁻¹ * (h : G) * Z) := by group
  calc π (h : G) (π Z x) = π ((h : G) * Z) x := by rw [map_mul]; rfl
    _ = π (Z * (Z⁻¹ * (h : G) * Z)) x := by rw [e]
    _ = π Z (π (Z⁻¹ * (h : G) * Z) x) := by rw [map_mul]; rfl
    _ = π Z x := by rw [hx _ hm']

theorem ineq (π : Representation ℂ G X) (B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ)
    (hB1 : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hB2 : ∀ v, v ≠ 0 → 0 < (B v v).re)
    (hB3 : ∀ g v w, B (π g v) (π g w) = B v w) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] (Z : G)
    (v : X) (hv : v ≠ 0) (lam : ℂ)
    (hT : (Fintype.card (K ⧸ H) : ℂ)⁻¹ • avL π K H (π Z v) = lam • v)
    (hfix : ∀ κ ∈ K, π κ (lam • v) = lam • v) : ‖lam‖ ≤ 1 := by
  have hN : (Fintype.card (K ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hs1 : ∀ (r : ℂ) (x y : X), B (r • x) y = r * B x y := fun r x y => by
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hs2 : ∀ (r : ℂ) (x y : X), B x (r • y) = starRingEnd ℂ r * B x y := fun r x y => by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul]
  have hsub1 : ∀ x y z : X, B (x - y) z = B x z - B y z := fun x y z => by
    rw [map_sub, LinearMap.sub_apply]
  have hsub2 : ∀ x y z : X, B x (y - z) = B x y - B x z := fun x y z => map_sub _ _ _
  have hpair : B (avL π K H (π Z v)) (lam • v) = (Fintype.card (K ⧸ H) : ℂ) * B (π Z v) (lam • v) := by
    rw [avL_apply, map_sum, LinearMap.sum_apply]
    have : ∀ q : K ⧸ H, B (π ((q.out : K) : G) (π Z v)) (lam • v) = B (π Z v) (lam • v) := by
      intro q
      have h1 := hB3 ((q.out : K) : G) (π Z v) (lam • v)
      rw [hfix _ (q.out : K).2] at h1
      exact h1
    rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have haa : B (lam • v) (lam • v) = B (π Z v) (lam • v) := by
    have : B (lam • v) (lam • v) = B ((Fintype.card (K ⧸ H) : ℂ)⁻¹ • avL π K H (π Z v)) (lam • v) := by
      rw [hT]
    rw [this, hs1, hpair, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  have hreal : starRingEnd ℂ (B (lam • v) (lam • v)) = B (lam • v) (lam • v) := (hB1 _ _).symm
  have hay : B (lam • v) (π Z v) = B (lam • v) (lam • v) := by rw [hB1 (π Z v) (lam • v), ← haa, hreal]
  have hnn : 0 ≤ (B (π Z v - lam • v) (π Z v - lam • v)).re := by
    by_cases h0 : π Z v - lam • v = 0
    · rw [h0]; simp
    · exact (hB2 _ h0).le
  have hexp : B (π Z v - lam • v) (π Z v - lam • v) = B (π Z v) (π Z v) - B (lam • v) (lam • v) := by
    rw [hsub1, hsub2, hsub2, ← haa, hay]
    ring
  have hyy : B (π Z v) (π Z v) = B v v := hB3 _ _ _
  have haa' : B (lam • v) (lam • v) = (Complex.normSq lam : ℂ) * B v v := by
    rw [hs1, hs2, ← mul_assoc, Complex.mul_conj]
  have hvpos : 0 < (B v v).re := hB2 _ hv
  rw [hexp, hyy, haa'] at hnn
  simp only [Complex.sub_re, Complex.re_ofReal_mul] at hnn
  have hns : Complex.normSq lam ≤ 1 := by nlinarith
  rw [Complex.normSq_eq_norm_sq] at hns
  nlinarith [norm_nonneg lam]

end Gen

theorem fixval {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W) (K : Subgroup (GL (Fin (d + d)) k))
    (v : IndSp (blk2 d) τ) (hv : v ∈ fixed (parInd (blk2 d) τ) K) (g κ : GL (Fin (d + d)) k) (hκ : κ ∈ K) :
    v.1.1 (g * κ) = v.1.1 g := by
  have h := (GlobalTheory.LGrp.mem_fixed).1 hv κ hκ
  exact congrArg (fun f : IndSp (blk2 d) τ => f.1.1 g) h

theorem law {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W) (p : parab k (blk2 d)) (g : GL (Fin (d + d)) k)
    (f : IndSp (blk2 d) τ) : f.1.1 ((p : GL (Fin (d + d)) k) * g) =
      (deltaHalf k (fun _ : Fin 2 => Fin d) (leviProj k (blk2 d) p) : ℂ) • τ (leviProj k (blk2 d) p) (f.1.1 g) :=
  f.1.2 p g

theorem act {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W) (g x : GL (Fin (d + d)) k) (f : IndSp (blk2 d) τ) :
    (parInd (blk2 d) τ g f).1.1 x = f.1.1 (x * g) := rfl

theorem zval {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W) (t : kˣ) (c : ℂ) (htv : valuation k (t : k) ≤ 1)
    (hc : ∀ w, τ ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] w = c • w) {m : ℕ} (hm : 1 ≤ m)
    (v : IndSp (blk2 d) τ) (hv : v ∈ fixed (parInd (blk2 d) τ) (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m))
    (κ : GL (Fin (d + d)) k) (hκ : κ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m) :
    (parInd (blk2 d) τ (Zt d t) v).1.1 κ =
      ((deltaHalf k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] : ℂ) * c) • v.1.1 1 := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' (blk (blk2 d)) hm κ hκ
  obtain ⟨hxK, hxN⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hyK, hyL⟩ := Subgroup.mem_inf.1 hy
  have hxyK := Subgroup.mul_mem _ hxK hyK
  have hxyP : x * y ∈ parab k (blk2 d) := by
    have h1 := GroundTheory.Automorphic.Parabolic.unipotentRadical_le_blockUpper hxN
    have h2 := GroundTheory.Automorphic.Parabolic.levi_le_blockUpper hyL
    exact (GroundTheory.Automorphic.Iwasawa.blockUpper k (d + d) (blk (blk2 d))).mul_mem h1 h2
  have hzc := conj_mem' d t htv hz
  have e1 : x * y * z * Zt d t = (x * y) * Zt d t * ((Zt d t)⁻¹ * z * Zt d t) := by group
  rw [act, e1, fixval τ _ v hv _ _ hzc]
  have e2 : (x * y) * Zt d t = ((⟨x * y, hxyP⟩ : parab k (blk2 d)) : GL (Fin (d + d)) k) * Zt d t := rfl
  rw [e2, law]
  have e3 : v.1.1 (Zt d t) = ((deltaHalf k (fun _ : Fin 2 => Fin d)
      ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] : ℂ) * c) • v.1.1 1 := by
    have := law τ ⟨Zt d t, Zt_mem d t⟩ 1 v
    rw [mul_one] at this
    rw [this, leviProj_Zt, hc, smul_smul]
  rw [e3, map_smul, smul_comm, ← law, mul_one]
  have e4 : v.1.1 (x * y) = v.1.1 1 := by
    have := fixval τ _ v hv 1 (x * y) hxyK
    rwa [one_mul] at this
  rw [e4]

theorem modulus_scalar_block (d : ℕ) (t : kˣ) :
    modulus k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] = nabs k t ^ (d * d) := by
  rw [modulus, Fin.prod_univ_two]
  have h0 : modExp (fun _ : Fin 2 => Fin d) 0 = (d : ℤ) := by
    have c1 : (Finset.filter (fun b : Fin 2 => 0 < b) Finset.univ).card = 1 := by decide
    simp [modExp, c1]
  have hn : ∀ (x : kˣ) (j : ℕ), nabs k (x ^ j) = nabs k x ^ j := by
    intro x j; simp [nabs, map_pow]
  have h1 : nabs k (1 : kˣ) = 1 := by simp [nabs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_one, h1, _root_.one_zpow, mul_one,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hn, h0, zpow_natCast, ← pow_mul]

set_option maxHeartbeats 1000000 in
theorem bound_main : Bound k := by
  intro d W _ _ _ τ hτ hadm hunit t c ht hc
  classical
  obtain ⟨B, hB1, hB2, hB3⟩ := hunit
  have htv := val_le_one t ht

  have hnorm : ‖((deltaHalf k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] : ℂ) * c)‖ =
      ‖c‖ * nabs k t ^ (((d * d : ℕ) : ℝ) / 2) := by
    rw [norm_mul, val_deltaHalf, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), modulus_scalar_block,
      mul_comm, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (nabs_pos' k t).le]
    congr 2
    ring
  rw [← hnorm]
  set lam := ((deltaHalf k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] : ℂ) * c)
    with hlam
  by_cases hl0 : lam = 0
  · rw [hl0, norm_zero]; exact zero_le_one

  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨f0, hf01, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (blk2 d) τ hτ u
  have ho : IsOpen {g : GL (Fin (d + d)) k | ((parInd (blk2 d) τ g f0 : IndSp (blk2 d) τ) : _) = f0.1} := f0.2
  obtain ⟨m1, -, hm1⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k (d + d)).mem_iff.1
    (ho.mem_nhds (by simp))
  have hm : 1 ≤ max m1 1 := le_max_right _ _
  set K := GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) (max m1 1) with hK
  have hKo : IsOpen (K : Set (GL (Fin (d + d)) k)) := GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k _ _
  have hKc : IsCompact (K : Set (GL (Fin (d + d)) k)) :=
    GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k _ _
  have hf0K : f0 ∈ fixed (parInd (blk2 d) τ) K := by
    rw [GlobalTheory.LGrp.mem_fixed]
    intro κ hκ
    exact Subtype.ext (hm1 (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_antitone k (d + d) (le_max_left m1 1) hκ))
  haveI hfd : FiniteDimensional ℂ (fixed (parInd (blk2 d) τ) K) := hadm.2 K hKo hKc

  set H : Subgroup K := (K.map (MulAut.conj (Zt d t)).toMonoidHom).subgroupOf K with hH
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hHo : IsOpen (H : Set K) := by
    have : (H : Set K) = (fun x : K => (Zt d t)⁻¹ * (x : GL (Fin (d + d)) k) * Zt d t) ⁻¹' (K : Set _) := by
      ext x
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact GlobalTheory.HeckeAvg.mem_conj
    rw [this]
    exact hKo.preimage (by fun_prop)
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have hmaps : ∀ x ∈ fixed (parInd (blk2 d) τ) K,
      ((Fintype.card (K ⧸ H) : ℂ)⁻¹ • (avL (parInd (blk2 d) τ) K H ∘ₗ parInd (blk2 d) τ (Zt d t))) x ∈
        fixed (parInd (blk2 d) τ) K := by
    intro x hx
    rw [GlobalTheory.LGrp.mem_fixed]
    intro κ hκ
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
    rw [avL_fixed _ K H (fun h hh => hfixH _ K (Zt d t) x ((GlobalTheory.LGrp.mem_fixed).1 hx) h hh) κ hκ]
  let T := ((Fintype.card (K ⧸ H) : ℂ)⁻¹ • (avL (parInd (blk2 d) τ) K H ∘ₗ
    parInd (blk2 d) τ (Zt d t))).restrict hmaps
  let ev : IndSp (blk2 d) τ →ₗ[ℂ] W :=
    { toFun := fun f => f.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hevT : ∀ v : fixed (parInd (blk2 d) τ) K, ev (T v : IndSp (blk2 d) τ) = lam • ev v := by
    intro v
    have h1 : (T v : IndSp (blk2 d) τ) = (Fintype.card (K ⧸ H) : ℂ)⁻¹ •
        ∑ q : K ⧸ H, parInd (blk2 d) τ ((q.out : K) : GL (Fin (d + d)) k)
          (parInd (blk2 d) τ (Zt d t) (v : IndSp (blk2 d) τ)) := by
      show (Fintype.card (K ⧸ H) : ℂ)⁻¹ • avL (parInd (blk2 d) τ) K H
        (parInd (blk2 d) τ (Zt d t) (v : IndSp (blk2 d) τ)) = _
      rw [avL_apply]
    rw [h1, map_smul, map_sum]
    have hterm : ∀ q : K ⧸ H, ev (parInd (blk2 d) τ ((q.out : K) : GL (Fin (d + d)) k)
        (parInd (blk2 d) τ (Zt d t) (v : IndSp (blk2 d) τ))) = lam • ev v := by
      intro q
      show (parInd (blk2 d) τ ((q.out : K) : GL (Fin (d + d)) k)
        (parInd (blk2 d) τ (Zt d t) (v : IndSp (blk2 d) τ))).1.1 1 = lam • (v : IndSp (blk2 d) τ).1.1 1
      rw [act, one_mul]
      exact zval τ t c htv hc hm _ v.2 _ (q.out : K).2
    have hN : (Fintype.card (K ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ hN, one_smul]

  let R := LinearMap.range (ev ∘ₗ (fixed (parInd (blk2 d) τ) K).subtype)
  let f' : fixed (parInd (blk2 d) τ) K →ₗ[ℂ] R := (ev ∘ₗ (fixed (parInd (blk2 d) τ) K).subtype).rangeRestrict
  let S : R →ₗ[ℂ] R := lam • LinearMap.id
  have hcomm : f' ∘ₗ T = S ∘ₗ f' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact hevT v
  have hw' : f' ⟨f0, hf0K⟩ ≠ 0 := by
    intro h
    have h2 : ev f0 = 0 := congrArg Subtype.val h
    exact hu (hf01 ▸ h2)
  obtain ⟨v, hv0, hTv⟩ := GlobalTheory.T.eigenvector_lift_of_surjection _ _ T S f' (LinearMap.surjective_rangeRestrict _) hcomm lam
    (f' ⟨f0, hf0K⟩) hw' rfl hl0
  have hTv' : (Fintype.card (K ⧸ H) : ℂ)⁻¹ • avL (parInd (blk2 d) τ) K H (parInd (blk2 d) τ (Zt d t) v) =
      lam • (v : IndSp (blk2 d) τ) := congrArg Subtype.val hTv
  refine ineq (parInd (blk2 d) τ) B hB1 hB2 hB3 K H (Zt d t) v (fun h => hv0 (Subtype.ext h)) lam hTv' ?_
  rw [← hTv']
  exact (GlobalTheory.LGrp.mem_fixed).1 (T v).2

end CompanionTheory.RgGu.NR.BoundB

namespace CompanionTheory.RgGu.NR

theorem boundB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Bound k := BoundB.bound_main

end CompanionTheory.RgGu.NR
