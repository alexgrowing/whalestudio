import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import GroundTheory.AutomorphicForms.IwahoriFactorization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfFixedMemSpanTranslates
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvectorLiftOfSurjectionStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace PositivityTheory.RgGu.NR.BoundB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_one (t : kˣ) (h : nabs k t ≤ 1) : valuation k (t : k) ≤ 1 := by
  have h1 : nabs k 1 = 1 := (nabs_eq_one_iff (1 : kˣ)).2 (by simp)
  have h2 := (nabs_le_iff t 1).1 (h1 ▸ h)
  simpa using h2

def zd (d : ℕ) (t : kˣ) (i : Fin (d + d)) : kˣ := if blk (blk2 d) i = 0 then t else 1

def Zt (d : ℕ) (t : kˣ) : GL (Fin (d + d)) k := diagT k (Fin (d + d)) (zd d t)

theorem Zt_val (d : ℕ) (t : kˣ) : ((Zt d t : GL (Fin (d + d)) k) : Matrix (Fin (d + d)) (Fin (d + d)) k) =
    diagonal fun i => ((zd d t i : kˣ) : k) := by
  rw [Zt, val_diagT]

theorem Zt_inv_val (d : ℕ) (t : kˣ) :
    (((Zt d t)⁻¹ : GL (Fin (d + d)) k) : Matrix (Fin (d + d)) (Fin (d + d)) k) =
      diagonal fun i => (((zd d t i)⁻¹ : kˣ) : k) := by
  rw [Matrix.coe_units_inv, Zt_val]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  simp

theorem Zt_mem (d : ℕ) (t : kˣ) : Zt d t ∈ parab k (blk2 d) := by
  change ((Zt d t : GL (Fin (d + d)) k) : Matrix _ _ k).BlockTriangular (blk (blk2 d))
  rw [Zt_val]
  exact Matrix.blockTriangular_diagonal _

theorem leviProj_Zt (d : ℕ) (t : kˣ) :
    leviProj k (blk2 d) ⟨Zt d t, Zt_mem d t⟩ = ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] := by
  funext a
  ext i j
  simp only [leviProj, diagBlock, MonoidHom.pi_apply, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.submatrix_apply, Zt_val, Matrix.diagonal_apply]
  fin_cases a <;> simp [zd, blk, Matrix.diagonal_apply, Matrix.one_apply]

theorem conj_mem (d : ℕ) (t : kˣ) (ht : valuation k (t : k) ≤ 1) {m : ℕ} {z : GL (Fin (d + d)) k}
    (hz : z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m)
    (hzo : z ∈ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k (d + d) (blk (blk2 d))) :
    ∀ i j, valuation k ((((Zt d t)⁻¹ * z * Zt d t : GL (Fin (d + d)) k) : Matrix _ _ k) i j -
        (1 : Matrix (Fin (d + d)) (Fin (d + d)) k) i j) ≤
          valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ m ∧
      (((Zt d t)⁻¹ * z * Zt d t : GL (Fin (d + d)) k) : Matrix _ _ k) i j ∈ 𝒪[k] := by
  have hint := (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff k (d + d)).1
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_le k (d + d) m hz)
  have hcong := ((GroundTheory.Automorphic.GLnLocal.mem_congruenceSubgroup_iff k (d + d)).1 hz).2
  have hopp := GroundTheory.Automorphic.Parabolic.mem_oppositeUnipotentRadical.1 hzo
  intro i j
  have hent : (((Zt d t)⁻¹ * z * Zt d t : GL (Fin (d + d)) k) : Matrix _ _ k) i j =
      ((zd d t i)⁻¹ : kˣ) * (z : Matrix _ _ k) i j * (zd d t j : k) := by
    rw [Units.val_mul, Units.val_mul, Zt_inv_val, Zt_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hzij : valuation k ((z : Matrix _ _ k) i j) ≤ 1 := hint.1 i j
  rw [hent]
  rcases lt_trichotomy (blk (blk2 d) i) (blk (blk2 d) j) with h | h | h
  · have h0 := hopp.1 i j h
    have hne : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
    simp [h0, Matrix.one_apply_ne hne]
  · have hz' : zd d t i = zd d t j := by simp only [zd, h]
    rw [hz']
    have e : (((zd d t j)⁻¹ : kˣ) : k) * (z : Matrix _ _ k) i j * (zd d t j : k) = (z : Matrix _ _ k) i j := by
      rw [mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
    rw [e]
    exact ⟨hcong i j, hzij⟩
  · have hi : blk (blk2 d) i = 1 := by omega
    have hj : blk (blk2 d) j = 0 := by omega
    have hne : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
    have zi : zd d t i = 1 := by simp [zd, hi]
    have zj : zd d t j = t := by simp [zd, hj]
    rw [zi, zj, inv_one, Units.val_one, one_mul]
    have hv : valuation k ((z : Matrix _ _ k) i j * t) ≤ valuation k ((z : Matrix _ _ k) i j) := by
      rw [map_mul]; exact mul_le_of_le_one_right' ht
    refine ⟨?_, ?_⟩
    · rw [Matrix.one_apply_ne hne, sub_zero]
      have h2 := hcong i j
      rw [Matrix.one_apply_ne hne, sub_zero] at h2
      exact hv.trans h2
    · exact hv.trans hzij

theorem conj_mem' (d : ℕ) (t : kˣ) (ht : valuation k (t : k) ≤ 1) {m : ℕ} {z : GL (Fin (d + d)) k}
    (hz : z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m ⊓
      GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k (d + d) (blk (blk2 d))) :
    (Zt d t)⁻¹ * z * Zt d t ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m := by
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
  refine GroundTheory.Automorphic.Parabolic.mem_congruenceSubgroup_of_le (fun i j => (conj_mem d t ht hz1 hz2 i j).1) ?_
  intro i j
  have e : ((Zt d t)⁻¹ * z * Zt d t)⁻¹ = (Zt d t)⁻¹ * z⁻¹ * Zt d t := by group
  rw [e]
  exact (conj_mem d t ht (inv_mem hz1) (inv_mem hz2) i j).1

section Rep

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def avL (π : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] : Module.End ℂ V :=
  ∑ q : K ⧸ H, π ((q.out : K) : G)

theorem avL_apply (π : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] (x : V) :
    avL π K H x = ∑ q : K ⧸ H, π ((q.out : K) : G) x := by
  simp [avL, LinearMap.sum_apply]

theorem avL_fixed (π : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] {x : V}
    (hx : ∀ h ∈ H, π ((h : K) : G) x = x) (κ : G) (hκ : κ ∈ K) : π κ (avL π K H x) = avL π K H x := by
  rw [avL_apply, map_sum]
  let κ' : K := ⟨κ, hκ⟩
  refine Fintype.sum_equiv (MulAction.toPerm κ' : K ⧸ H ≃ K ⧸ H) _ _ ?_
  intro q
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (κ' * q.out)
  have e : (κ' • q : K ⧸ H) = ((κ' * q.out : K) : K ⧸ H) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  simp only [MulAction.toPerm_apply]
  rw [e, hh]
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  rw [hx h h.2]

end Rep

section Gen

variable {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X]

theorem hfixH (π : Representation ℂ G X) (K : Subgroup G) (Z : G) (x : X) (hx : ∀ κ ∈ K, π κ x = x)
    (h : K) (hh : h ∈ (K.map (MulAut.conj Z).toMonoidHom).subgroupOf K) :
    π (h : G) (π Z x) = π Z x := by
  obtain ⟨κ, hκ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hh)
  rw [← e]
  change π (Z * κ * Z⁻¹) (π Z x) = π Z x
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hx κ hκ]

theorem ineq (π : Representation ℂ G X) (B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ)
    (hB1 : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hB2 : ∀ v, v ≠ 0 → 0 < (B v v).re)
    (hB3 : ∀ g v w, B (π g v) (π g w) = B v w) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] (Z : G)
    (v : X) (hv : v ≠ 0) (lam : ℂ)
    (hT : (Fintype.card (K ⧸ H) : ℂ)⁻¹ • avL π K H (π Z v) = lam • v)
    (hfix : ∀ κ ∈ K, π κ (lam • v) = lam • v) : ‖lam‖ ≤ 1 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, x = π Z v := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = lam • v := ⟨_, rfl⟩
  rw [← hx, ← hw] at hT
  rw [← hw] at hfix
  have hKfix : ∀ q : K ⧸ H, π ((q.out : K) : G) w = w := fun q => hfix _ (q.out).2
  have hN : (Fintype.card (K ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hA : B w w = B x w := by
    have e0 : B w w = B ((Fintype.card (K ⧸ H) : ℂ)⁻¹ • avL π K H x) w := by rw [hT]
    have e1 : B w w = (Fintype.card (K ⧸ H) : ℂ)⁻¹ * ∑ q : K ⧸ H, B (π ((q.out : K) : G) x) w := by
      rw [e0, avL_apply, LinearMap.map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
    have e2 : ∀ q : K ⧸ H, B (π ((q.out : K) : G) x) w = B x w := by
      intro q
      conv_lhs => rw [← hKfix q]
      exact hB3 _ _ _
    rw [e1, Finset.sum_congr rfl (fun q _ => e2 q), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hxx : B x x = B v v := by rw [hx]; exact hB3 Z v v
  have hB : B w w = ((Complex.normSq lam : ℝ) : ℂ) * B v v := by
    rw [hw, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul]
    rw [← Complex.mul_conj]
    ring
  have hwx : B w x = starRingEnd ℂ (B x w) := hB1 x w
  have hpos : 0 ≤ (B (x - w) (x - w)).re := by
    by_cases h0 : x - w = 0
    · rw [h0]; simp
    · exact le_of_lt (hB2 _ h0)
  have hexp : B (x - w) (x - w) = B x x - B x w - B w x + B w w := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [hexp, hxx, hwx, ← hA, hB] at hpos
  rw [Complex.add_re, Complex.sub_re, Complex.sub_re, Complex.conj_re, Complex.re_ofReal_mul] at hpos
  have hv0 := hB2 v hv
  have hn : Complex.normSq lam ≤ 1 := by nlinarith
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [norm_nonneg lam]

end Gen

theorem fixval {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W) (K : Subgroup (GL (Fin (d + d)) k))
    (v : IndSp (blk2 d) τ) (hv : v ∈ fixed (parInd (blk2 d) τ) K) (g κ : GL (Fin (d + d)) k) (hκ : κ ∈ K) :
    v.1.1 (g * κ) = v.1.1 g := by
  have h2 : parInd (blk2 d) τ κ v = v := by
    have := hv ⟨κ, hκ⟩
    simpa using this
  have h3 : (parInd (blk2 d) τ κ v).1.1 g = v.1.1 (g * κ) := rfl
  rw [← h3, h2]

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
  obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hyK, hyL⟩ := Subgroup.mem_inf.1 hy
  have hxP : x ∈ parab k (blk2 d) := by
    change (x : Matrix _ _ k).BlockTriangular (blk (blk2 d))
    exact (GroundTheory.Automorphic.Iwasawa.mem_blockUpper k (d + d)).1
      (GroundTheory.Automorphic.Parabolic.mem_unipotentRadical.1 hxU).1
  have hyP : y ∈ parab k (blk2 d) := by
    change (y : Matrix _ _ k).BlockTriangular (blk (blk2 d))
    intro i j hij
    exact GroundTheory.Automorphic.Parabolic.mem_levi.1 hyL i j (ne_of_gt hij)
  have hzK : (Zt d t)⁻¹ * z * Zt d t ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m :=
    conj_mem' d t htv hz
  have hpK : x * y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m := mul_mem hxK hyK
  have step1 : (parInd (blk2 d) τ (Zt d t) v).1.1 (x * y * z) = v.1.1 (x * y * z * Zt d t) := rfl
  have step2 : x * y * z * Zt d t = (x * y * Zt d t) * ((Zt d t)⁻¹ * z * Zt d t) := by group
  rw [step1, step2, fixval τ _ v hv _ _ hzK]
  let p : parab k (blk2 d) := ⟨x * y, mul_mem hxP hyP⟩
  let q : parab k (blk2 d) := ⟨Zt d t, Zt_mem d t⟩
  have hlaw1 := law τ (p * q) 1 v
  have hlaw2 := law τ p 1 v
  have hfix1 : v.1.1 (x * y) = v.1.1 1 := by simpa using fixval τ _ v hv 1 (x * y) hpK
  have hpq : ((p * q : parab k (blk2 d)) : GL (Fin (d + d)) k) * 1 = x * y * Zt d t := by
    simp [p, q]
  have hp1 : ((p : parab k (blk2 d)) : GL (Fin (d + d)) k) * 1 = x * y := by simp [p]
  rw [hpq, map_mul, leviProj_Zt] at hlaw1
  rw [hp1, hfix1] at hlaw2
  rw [hlaw1, map_mul, map_mul, Module.End.mul_apply, hc, Units.val_mul, LinearMap.map_smul, smul_smul]
  conv_rhs => rw [hlaw2, smul_smul]
  congr 1
  ring

theorem modulus_scalar_block (d : ℕ) (t : kˣ) :
    modulus k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] = nabs k t ^ (d * d) := by
  have c0 : (Finset.univ.filter (fun b : Fin 2 => 0 < b)).card = 1 := by decide
  have c1 : (Finset.univ.filter (fun b : Fin 2 => 1 < b)).card = 0 := by decide
  have c2 : (Finset.univ.filter (fun b : Fin 2 => b = 0)).card = 1 := by decide
  have c3 : (Finset.univ.filter (fun b : Fin 2 => b < 0)).card = 0 := by decide
  have c4 : (Finset.univ.filter (fun b : Fin 2 => b < 1)).card = 1 := by decide
  have e0 : modExp (fun _ : Fin 2 => Fin d) 0 = d := by
    simp [modExp, c0, c3]
  have e1 : modExp (fun _ : Fin 2 => Fin d) 1 = -d := by
    simp [modExp, c1, c2, c4]
  have hn1 : nabs k 1 = 1 := (nabs_eq_one_iff (1 : kˣ)).2 (by simp)
  have hpow : ∀ n : ℕ, nabs k (t ^ n) = nabs k t ^ n := by
    intro n
    induction n with
    | zero => simpa using hn1
    | succ n ih => rw [pow_succ, nabs_mul', ih, pow_succ]
  have hdet : nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) t)) = nabs k t ^ d := by
    have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) t) = t ^ d := by
      ext
      simp
    rw [this, hpow]
  have h1 : nabs k (Matrix.GeneralLinearGroup.det (1 : GL (Fin d) k)) = 1 := by
    rw [map_one]; exact hn1
  simp only [modulus, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, e0, e1, hdet, h1]
  rw [_root_.one_zpow, mul_one, zpow_natCast, ← pow_mul]

set_option maxHeartbeats 1000000 in
theorem bound_main : Bound k := by
  classical
  intro d W _ _ _ τ hsm hadm hunit t c ht hc
  obtain ⟨B, hB1, hB2, hB3⟩ := hunit
  have htv := val_le_one t ht
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (blk2 d) τ hsm u
  have hopen : IsOpen {g : GL (Fin (d + d)) k | parInd (blk2 d) τ g f = f} := hadm.1 f
  obtain ⟨m0, -, hm0⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k (d + d)).mem_iff.1
    (hopen.mem_nhds (by simp))
  set K := GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) (m0 + 1) with hKdef
  have hKle : K ≤ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m0 :=
    GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_antitone k (d + d) (Nat.le_succ m0)
  have hfK : f ∈ fixed (parInd (blk2 d) τ) K := by
    intro h
    have := hm0 (hKle h.2)
    simpa using this
  have hKo : IsOpen (K : Set (GL (Fin (d + d)) k)) :=
    GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (d + d) (m0 + 1)
  have hKc : IsCompact (K : Set (GL (Fin (d + d)) k)) :=
    GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k (d + d) (m0 + 1)
  haveI hfd : FiniteDimensional ℂ (fixed (parInd (blk2 d) τ) K) := hadm.2 K hKo hKc
  set Z := Zt d t with hZ
  set H := (K.map (MulAut.conj Z).toMonoidHom).subgroupOf K with hH
  have hHo : IsOpen (H : Set K) := by
    have e : ((K.map (MulAut.conj Z).toMonoidHom : Subgroup _) : Set (GL (Fin (d + d)) k)) =
        (fun x => Z⁻¹ * x * Z) ⁻¹' (K : Set _) := by
      ext x
      simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨κ, hκ, rfl⟩
        simpa [mul_assoc] using hκ
      · intro hx
        exact ⟨Z⁻¹ * x * Z, hx, by group⟩
    have ho : IsOpen ((K.map (MulAut.conj Z).toMonoidHom : Subgroup _) : Set (GL (Fin (d + d)) k)) := by
      rw [e]
      exact hKo.preimage (by fun_prop)
    exact ho.preimage continuous_subtype_val
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have hfixV : ∀ y ∈ fixed (parInd (blk2 d) τ) K, ∀ κ ∈ K, parInd (blk2 d) τ κ y = y := by
    intro y hy κ hκ
    simpa using hy ⟨κ, hκ⟩
  let A : Module.End ℂ (IndSp (blk2 d) τ) :=
    (Fintype.card (K ⧸ H) : ℂ)⁻¹ • (avL (parInd (blk2 d) τ) K H ∘ₗ parInd (blk2 d) τ Z)
  have hAV : ∀ y ∈ fixed (parInd (blk2 d) τ) K, A y ∈ fixed (parInd (blk2 d) τ) K := by
    intro y hy h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, A, LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
    rw [avL_fixed (parInd (blk2 d) τ) K H
      (fun h' hh' => hfixH (parInd (blk2 d) τ) K Z y (hfixV y hy) h' hh') h h.2]
  let A' : Module.End ℂ (fixed (parInd (blk2 d) τ) K) := A.restrict hAV
  let evI : IndSp (blk2 d) τ →ₗ[ℂ] W :=
    { toFun := fun y => y.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let μ : ℂ := (deltaHalf k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] : ℂ) * c
  have hev : ∀ y ∈ fixed (parInd (blk2 d) τ) K, evI (A y) = μ • evI y := by
    intro y hy
    have e1 : ∀ q : K ⧸ H, evI (parInd (blk2 d) τ ((q.out : K) : GL (Fin (d + d)) k) (parInd (blk2 d) τ Z y)) =
        μ • evI y := by
      intro q
      have := zval τ t c htv hc (m := m0 + 1) (by omega) y hy _ (q.out).2
      simp only [evI, LinearMap.coe_mk, AddHom.coe_mk]
      rw [act, one_mul]
      exact this
    simp only [A, LinearMap.smul_apply, LinearMap.comp_apply, avL_apply, map_smul, map_sum]
    rw [Finset.sum_congr rfl (fun q _ => e1 q), Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
  let S : Module.End ℂ (fixed (parInd (blk2 d) τ) K) := A' - μ • 1
  have hSval : ∀ y : fixed (parInd (blk2 d) τ) K, ((S y : fixed (parInd (blk2 d) τ) K) : IndSp (blk2 d) τ) =
      A y - μ • (y : IndSp (blk2 d) τ) := by
    intro y
    rfl
  have hns : ¬ Function.Surjective S := by
    intro hs
    obtain ⟨y, hy⟩ := hs ⟨f, hfK⟩
    have h1 : evI ((S y : fixed (parInd (blk2 d) τ) K) : IndSp (blk2 d) τ) = 0 := by
      rw [hSval, map_sub, map_smul, hev _ y.2, sub_self]
    rw [hy] at h1
    exact hu (hf1.symm.trans h1)
  have hni : ¬ Function.Injective S := fun hi => hns (LinearMap.injective_iff_surjective.1 hi)
  rw [injective_iff_map_eq_zero] at hni
  push_neg at hni
  obtain ⟨y, hSy, hy0⟩ := hni
  have hAy : A y = μ • (y : IndSp (blk2 d) τ) := by
    have := congrArg Subtype.val hSy
    rw [hSval] at this
    exact sub_eq_zero.1 this
  have hμ := ineq (parInd (blk2 d) τ) B hB1 hB2 hB3 K H Z (y : IndSp (blk2 d) τ)
    (fun h => hy0 (Subtype.ext h)) μ (by simpa only [A, LinearMap.smul_apply, LinearMap.comp_apply] using hAy)
    (fun κ hκ => by rw [map_smul, hfixV y y.2 κ hκ])
  have hδ : ((deltaHalf k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] : ℂˣ) : ℂ) =
      ((Real.sqrt (nabs k t ^ (d * d)) : ℝ) : ℂ) := by
    rw [val_deltaHalf, modulus_scalar_block]
  have hs : Real.sqrt (nabs k t ^ (d * d)) = nabs k t ^ (((d * d : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (nabs_pos k t))]
    ring_nf
  simp only [μ] at hμ
  rw [norm_mul, hδ, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hs] at hμ
  rw [mul_comm]
  exact hμ

end PositivityTheory.RgGu.NR.BoundB

namespace PositivityTheory.RgGu.NR

theorem boundB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Bound k := BoundB.bound_main

end PositivityTheory.RgGu.NR
