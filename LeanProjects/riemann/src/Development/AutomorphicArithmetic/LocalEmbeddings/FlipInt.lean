import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
import Development.AutomorphicArithmetic.DivisorFrames.IntegralMemAddSubgroupOfRamifiedTwistedInvariant
import Development.AutomorphicArithmetic.DivisorFrames.ExistsMemKOEqStdFrameMulOfIsPrimFrame
import Development.AutomorphicArithmetic.DivisorFrames.IsIntegralUnitCharOfConductorLe
import Development.AutomorphicArithmetic.DivisorFrames.HaarVolSelfEqOneOfOpenSubgroupLeKO
import Development.AutomorphicArithmetic.DivisorFrames.FourierSumBlockTransposeInvEq
import Development.AutomorphicArithmetic.DivisorFrames.NuDetMulSliceBBlockAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensorStatement
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat

noncomputable section

namespace UpperTheory.FlipInt

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

def Lo (q n : ℕ) : AddSubgroup ℂ where
  carrier := {z | IsIntegral ℤ ((q : ℂ) ^ n * z)}
  add_mem' ha hb := by
    simp only [Set.mem_setOf_eq, mul_add] at *
    exact ha.add hb
  zero_mem' := by simpa using isIntegral_zero
  neg_mem' ha := by
    simp only [Set.mem_setOf_eq, mul_neg] at *
    exact ha.neg

theorem mem_Lo {q n : ℕ} {z : ℂ} : z ∈ Lo q n ↔ IsIntegral ℤ ((q : ℂ) ^ n * z) := Iff.rfl

theorem Lo_zero {q : ℕ} {z : ℂ} (h : IsIntegral ℤ z) : z ∈ Lo q 0 := by simpa [mem_Lo] using h

theorem Lo_mul {q a b : ℕ} {x y : ℂ} (hx : x ∈ Lo q a) (hy : y ∈ Lo q b) : x * y ∈ Lo q (a + b) := by
  rw [mem_Lo] at *
  have := hx.mul hy
  rwa [show (q : ℂ) ^ a * x * ((q : ℂ) ^ b * y) = (q : ℂ) ^ (a + b) * (x * y) by ring] at this

theorem Lo_mono {q a b : ℕ} {x : ℂ} (hx : x ∈ Lo q a) (h : a ≤ b) : x ∈ Lo q b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [mem_Lo] at *
  have h1 : IsIntegral ℤ ((q : ℂ) ^ c) := by
    have : IsIntegral ℤ (q : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (q : ℤ))
    exact this.pow c
  have := h1.mul hx
  rwa [show (q : ℂ) ^ c * ((q : ℂ) ^ a * x) = (q : ℂ) ^ (a + c) * x by ring] at this

theorem Lo_pow {q a : ℕ} {x : ℂ} (hx : x ∈ Lo q a) : ∀ n : ℕ, x ^ n ∈ Lo q (n * a)
  | 0 => by simpa using Lo_zero isIntegral_one
  | n + 1 => by rw [pow_succ, Nat.succ_mul]; exact Lo_mul (Lo_pow hx n) hx

theorem Lo_prod {q a : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, f i ∈ Lo q a) :
    ∏ i ∈ s, f i ∈ Lo q (s.card * a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lo_zero isIntegral_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.succ_mul, add_comm]
    exact Lo_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def chiZ (ν : kˣ →* ℂˣ) (z : ℂ) : kˣ →* ℂ where
  toFun x := (ν x : ℂ) * apow x z
  map_one' := by simp
  map_mul' x y := by rw [map_mul, apow_mul, Units.val_mul]; ring

theorem chiZ_apply (ν : kˣ →* ℂˣ) (z : ℂ) (x : kˣ) : chiZ ν z x = (ν x : ℂ) * apow x z := rfl

theorem chiZ_KO {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ} {e : ℕ} {ν : kˣ →* ℂˣ} (hϖ : IsUnif ϖ)
    (hν : CondLE ϖ e ν) (q : ℕ) (z : ℂ) {u : GL n k} (hu : u ∈ KO k n) : chiZ ν z (gdet u) ∈ Lo q 0 := by
  have h := valuation_gdet_of_mem_KO hu
  rw [chiZ_apply, apow_of_valuation_eq_one h, mul_one]
  exact Lo_zero (UpperTheory.isIntegral_unitChar_of_conductor_le ϖ e ν hϖ hν _ h)

theorem val_mul_le {a b c : Type} [Fintype b] {M : Matrix a b k} {N : Matrix b c k} {r : ValueGroupWithZero k}
    (hM : ∀ i j, valuation k (M i j) ≤ r) (hN : ∀ i j, N i j ∈ 𝒪[k]) (i : a) (j : c) :
    valuation k ((M * N) i j) ≤ r := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hN l j))).trans (hM i l)

theorem fourierSum_mem {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → IsIntegral ℤ (ψ x : ℂ))
    (hq : resCard k ≠ 0) {a : ℕ} {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ Lo (resCard k) a) (Y : Matrix A D k) :
    fourierSum ψ ϖ e P Φ Y ∈ Lo (resCard k) (e * Fintype.card A * P.card + a) := by
  classical
  rw [fourierSum_apply]
  split_ifs with h
  · refine Lo_mul ?_ (sum_mem fun T _ => Lo_mul (b := 0) (hΦ _) (Lo_zero (hψ _ ?_)))
    · rw [mem_Lo, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hq))]
      exact isIntegral_one
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    rw [pairCols, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Subring.mul_mem _ (liftRes_mem T i j) (h i j j.2)
  · exact zero_mem _

theorem invFourierSum_inv_mem {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → IsIntegral ℤ (ψ x : ℂ))
    {q a : ℕ} {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ Lo q a) (T : Matrix A D k) :
    invFourierSum ψ⁻¹ ϖ e P Φ T ∈ Lo q a := by
  classical
  rw [invFourierSum_inv_apply]
  split_ifs with h
  · refine sum_mem fun S _ => Lo_mul (b := 0) (hΦ _) (Lo_zero (hψ _ ?_))
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    have e1 : ((ϖ ^ e : kˣ) : k) * pairCols P T ((ϖ ^ e)⁻¹ • liftRes S) = ∑ i, ∑ j : P, liftRes S i j * T i j := by
      rw [pairCols, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
    rw [e1]
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (liftRes_mem S i j) (h i j j.2)
  · exact zero_mem _

variable [MeasurableSpace k] [BorelSpace k]

theorem smallF_mem {A D : Type} [Fintype A] [DecidableEq A] {n : ℕ} [Fintype D] [DecidableEq D]
    (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] {J : Subgroup (GL (Fin n) k)} (hJo : IsOpen (J : Set (GL (Fin n) k)))
    (hJK : J ≤ KO k (Fin n)) (hμ : μ (J : Set (GL (Fin n) k)) = 1)
    (σ : A ⊕ Fin n ≃ D) {ν : kˣ →* ℂˣ} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    {q C a : ℕ} (hC : chiZ ν ((Fintype.card D : ℂ) / 2) ϖ⁻¹ ∈ Lo q C) (c c' : D → kˣ) (hcc : ∀ j, c j * c' j = (ϖ ^ e)⁻¹)
    {Ψ : Matrix (Fin n) D k → ℂ} (hΨ : HasDepth ϖ e (diagLat c) Ψ) (hΨa : ∀ X, Ψ X ∈ Lo q a)
    (hinv : ∀ j ∈ J, ∀ Y, Ψ (j.val * Y) * (ν (gdet j) : ℂ) = Ψ Y) {u : GL D k} (hu : u ∈ KO k D) :
    smallF μ ν Ψ (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val) ∈ Lo q (a + n * (e * C)) := by
  have hu' := (mem_KO_iff u).1 hu
  have hY0 : ∀ i j, Y0 k σ i j ∈ 𝒪[k] := fun i j => by
    simp only [Y0, of_apply]; split_ifs <;> simp
  have hent : ∀ (g : Matrix (Fin n) (Fin n) k) i j, (g * (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val)) i j =
      (g * Y0 k σ * u.val) i j * (((c' j)⁻¹ : kˣ) : k) := fun g i j => by
    rw [Units.val_mul, diagGL_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_diagonal]
  have hv0 : ∀ x : kˣ, 0 < valuation k (x : k) := fun x => zero_lt_iff.2 (by simp)
  refine UpperTheory.integral_mem_addSubgroup_of_ramified_twisted_invariant μ J hJo hJK hμ ϖ ν e hϖ hram hν _
    (fun g => Ψ (g * (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val))) e ?_ ?_ ?_ _ ?_
  · intro g hg
    have h1 : g * (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val) ∈ matLat (Fin n) (diagLat c) := by
      by_contra h; exact hg (hΨ.1 _ h)
    have h2 : ∀ i j, valuation k ((g * Y0 k σ * u.val) i j) ≤ valuation k ((ϖ ^ (-(e : ℤ)) : kˣ) : k) := fun i j => by
      have h3 : valuation k ((g * (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val)) i j) ≤ valuation k (c j : k) := h1 i j
      rw [hent, map_mul, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_le_iff₀ (hv0 _), ← map_mul, ← Units.val_mul, hcc] at h3
      rwa [_root_.zpow_neg, _root_.zpow_natCast]
    intro i j
    have h4 := val_mul_le h2 hu'.2 i (σ (.inr j))
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h4
    simpa [Matrix.mul_apply, Y0] using h4
  · intro X Z hZ
    simp only [Matrix.add_mul]
    refine hΨ.2 _ _ fun i => ?_
    rw [smul_diagLat]
    intro j
    have h1 : valuation k ((Z * Y0 k σ * u.val) i j) ≤ 1 :=
      val_mul_le (val_mul_le (r := 1) (fun i j => by simpa using hZ i j) hY0) hu'.1 i j
    show valuation k ((Z * (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val)) i j) ≤ valuation k ((ϖ ^ e * c j : kˣ) : k)
    rw [hent, map_mul, show ϖ ^ e * c j = (c' j)⁻¹ by rw [eq_inv_iff_mul_eq_one, mul_assoc, hcc, mul_inv_cancel]]
    exact mul_le_of_le_one_left' h1
  · intro j hj g
    simp only [Matrix.mul_assoc]
    exact hinv j hj _
  · intro m hm g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
    rw [mul_assoc, ← chiZ_apply]
    refine Lo_mul (hΨa _) ?_
    rw [gdet_mul, gdet_mul, map_mul, map_mul]
    have h1 : chiZ ν ((Fintype.card D : ℂ) / 2) (gdet (diagGL fun i => ϖ ^ m i)) ∈ Lo q (n * (e * C)) := by
      rw [gdet, det_diagGL, map_prod]
      have := Lo_prod (q := q) (a := e * C) Finset.univ (fun i => chiZ ν ((Fintype.card D : ℂ) / 2) (ϖ ^ m i)) fun i _ => by
        obtain ⟨l, hl⟩ : ∃ l : ℕ, m i = -(l : ℤ) := ⟨(-m i).toNat, by have := hm i; omega⟩
        rw [hl, _root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, map_pow]
        exact Lo_mono (Lo_pow hC l) (Nat.mul_le_mul_right _ (by have := hm i; omega))
      simpa using this
    simpa using Lo_mul (Lo_mul (chiZ_KO hϖ hν q _ hx) h1) (chiZ_KO hϖ hν q _ hy)

theorem phiA_mem {A D : Type} [Fintype A] [DecidableEq A] {n : ℕ} [Fintype D] [DecidableEq D]
    (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] {J : Subgroup (GL (Fin n) k)} (hJo : IsOpen (J : Set (GL (Fin n) k)))
    (hJK : J ≤ KO k (Fin n)) (hμ : μ (J : Set (GL (Fin n) k)) = 1)
    (σ : A ⊕ Fin n ≃ D) {ν : kˣ →* ℂˣ} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    {q C a : ℕ} (hC : chiZ ν ((Fintype.card D : ℂ) / 2) ϖ⁻¹ ∈ Lo q C) (hC' : chiZ ν ((Fintype.card D : ℂ) / 2) ϖ ∈ Lo q C)
    (P : Finset D) {Ψ : Matrix (Fin n) D k → ℂ} (hΨ : HasDepth ϖ e (blockLat ϖ e P) Ψ) (hΨa : ∀ X, Ψ X ∈ Lo q a)
    (hinv : ∀ j ∈ J, ∀ Y, Ψ (j.val * Y) * (ν (gdet j) : ℂ) = Ψ Y) (X : Matrix A D k) :
    phiA μ σ ν ϖ e (blockLat ϖ e P) Ψ X ∈ Lo q (Fintype.card D * (e * C) + (a + n * (e * C))) := by
  classical
  unfold phiA
  split_ifs with hX
  swap
  · exact zero_mem _
  rw [latA_blockLat] at hX
  set g : GL D k := blockScale ϖ e Pᶜ with hg
  have h1 : ∀ x, x ᵥ* (g⁻¹).val ∈ stdLat k D ↔ x ∈ blockLat ϖ e Pᶜ := fun x => by
    rw [← vecMul_blockScale_mem ϖ e Pᶜ, vecMul_vecMul, Units.inv_mul, vecMul_one]
  obtain ⟨u, hu, hXu⟩ := UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame σ _ (GlobalTheory.SplitFlip.Model.isPrimFrame_mul hX g⁻¹ h1)
  have h2 : invT (diagGL fun j => (blockUnits ϖ e Pᶜ j)⁻¹) = g := by
    have : (diagGL fun j => (blockUnits ϖ e Pᶜ j)⁻¹) = g⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      refine Units.ext ?_
      rw [Units.val_mul, hg, blockScale, diagGL_val, diagGL_val, diagonal_mul_diagonal]
      simp
    refine Units.ext ?_
    rw [this, invT_val, inv_inv, hg, blockScale, diagGL_val, diagonal_transpose]
  have h3 : X = X0 k σ * (invT (u * diagGL fun j => (blockUnits ϖ e Pᶜ j)⁻¹)).val := by
    rw [map_mul, h2, Units.val_mul, ← Matrix.mul_assoc, ← hXu, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [h3, splitTheta_fFun_frameFirstBlock_mul, ← chiZ_apply]
  refine Lo_mul ?_ (smallF_mem μ hJo hJK hμ σ hϖ hν hram hC (blockUnits ϖ e P) (blockUnits ϖ e Pᶜ) (fun j => ?_) hΨ hΨa hinv hu)
  · rw [gdet_mul, map_mul, gdet, gdet, det_diagGL, map_prod]
    have := Lo_prod (q := q) (a := e * C) Finset.univ
      (fun j => chiZ ν ((Fintype.card D : ℂ) / 2) (blockUnits ϖ e Pᶜ j)⁻¹) fun j _ => by
        unfold blockUnits
        split_ifs
        · rw [inv_inv, map_pow]; exact Lo_pow hC' e
        · rw [inv_one, map_one]; exact Lo_mono (Lo_zero isIntegral_one) (Nat.zero_le _)
    simpa using Lo_mul (chiZ_KO hϖ hν q ((Fintype.card D : ℂ) / 2) hu) this
  · by_cases h : j ∈ P <;> simp [blockUnits, h]

omit [MeasurableSpace k] [BorelSpace k] in

theorem chiZ_unif {ν : kˣ →* ℂˣ} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hq : resCard k ≠ 0) {B : ℕ} (d : ℕ)
    (h1 : (ν ϖ : ℂ) ∈ Lo (resCard k) B) (h2 : (ν ϖ⁻¹ : ℂ) ∈ Lo (resCard k) B) :
    chiZ ν ((d : ℂ) / 2) ϖ⁻¹ ∈ Lo (resCard k) (B + d) ∧ chiZ ν ((d : ℂ) / 2) ϖ ∈ Lo (resCard k) (B + d) := by
  have hq' : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq
  have hi : IsIntegral ℤ (resCard k : ℂ) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (resCard k : ℤ))
  have hs : ((resCard k : ℂ) ^ ((d : ℂ) / 2)) ^ 2 = (resCard k : ℂ) ^ d := by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast]; congr 1; push_cast; ring
  have h3 : IsIntegral ℤ ((resCard k : ℂ) ^ ((d : ℂ) / 2)) := IsIntegral.of_pow two_pos (by rw [hs]; exact hi.pow d)
  refine ⟨Lo_mul h2 ?_, Lo_mul h1 ?_⟩
  · rw [apow_inv, hϖ.apow_eq, neg_neg]
    exact Lo_mono (Lo_zero h3) (Nat.zero_le _)
  · rw [hϖ.apow_eq, mem_Lo, ← hs, Complex.cpow_neg, sq, mul_assoc,
      mul_inv_cancel₀ ((Complex.cpow_ne_zero_iff).2 (Or.inl hq')), mul_one]
    exact h3

theorem flip_mem {G : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψc : HasConductor ψ 1)
    (hq : resCard k ≠ 0) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → IsIntegral ℤ (ψ x : ℂ)) {i j B N a : ℕ}
    (hν : CondLE ϖ e (G.nu i j)) (hram : ¬ IsUnram (G.nu i j)) (h1 : (G.nu i j ϖ : ℂ) ∈ Lo (resCard k) B)
    (h2 : (G.nu i j ϖ⁻¹ : ℂ) ∈ Lo (resCard k) B) (hr : G.rank (i + 1, j + 1) ≤ N) (St : G.PiLocalization₂)
    (hp : PassesThrough i j St.path) (hJ : IsOpen (St.level (i, j) : Set (GL (Fin (G.rank (i, j))) k)))
    (hK : St.level (i, j) ≤ KO k _) (hT : St.IsAdmissible .one ϖ e) (hTa : ∀ x, St.tensor x ∈ Lo (resCard k) a)
    (x : G.Args) : G.flipTensor .one ψ ϖ e i j St.level St.tensor x ∈ Lo (resCard k) (a + e * N * (3 * B + 8 * N)) := by
  have hJ' := isOpen_map_invT hJ hK
  haveI := isHaarMeasure_haarVol hJ'.1 hJ'.2
  have hsub := hp.subset
  have hN := GlobalTheory.FunObj.isNatDatum_sliceB hT.tensor (hsub (by simp)) (hsub (by simp)) x (i := i) (j := j)
  obtain ⟨c1, c2⟩ := chiZ_unif hϖ hq (Fintype.card (G.Cols i j)) h1 h2
  unfold Grid.flipTensor squareFlip
  refine invFourierSum_inv_mem ψ ϖ e _ hψ (fun X => Lo_mono (phiA_mem _ hJ hK (UpperTheory.haarVol_self_eq_one_of_openSubgroup_le_KO _ hJ hK) _ hϖ hν hram c1 c2 _
    ((GlobalTheory.SplitFlip.FourierDepth.fourier_exchange k _ _ ψ ϖ e _ hϖ hψc).1 _ hN)
    (fun Y => fourierSum_mem ψ ϖ e _ hψ hq (fun Z => hTa _) Y) (fun u hu Y => ?_) X) ?_) _
  · have h3 := UpperTheory.fourierSum_block_transpose_inv_eq ψ ϖ e hϖ hψc _ hN u⁻¹ (inv_mem (hK hu)) Y
    rw [inv_inv] at h3
    have h4 : G.sliceB i j St.tensor x = (G.nu i j (gdet u) : ℂ) • fun Z => G.sliceB i j St.tensor x
        (fromCols ((u⁻¹).valᵀ * Z.toCols₁) (u.val * Z.toCols₂)) := by
      funext Z
      have := UpperTheory.nu_det_mul_sliceB_block_action ϖ e St i j hp hT u⁻¹ (inv_mem hu) x Z
      rw [inv_inv] at this
      exact this.symm
    rw [← h3]
    conv_rhs => rw [h4, map_smul]
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  · have r1 : G.rank (i, j) ≤ N := le_trans (by simp only [Grid.rank]; gcongr <;> omega) hr
    have r2 : G.rank (i, j + 1) ≤ N := le_trans (by simp only [Grid.rank]; gcongr; omega) hr
    have r3 : G.rank (i + 1, j) ≤ N := le_trans (by simp only [Grid.rank]; gcongr; omega) hr
    have r4 : Fintype.card (G.Cols i j) ≤ 2 * N := by simp only [Fintype.card_sum, Fintype.card_fin]; omega
    have r5 : (Assignment.one.block (Fin (G.rank (i, j + 1))) (Fin (G.rank (i + 1, j)))).card ≤ 2 * N :=
      (Finset.card_le_univ _).trans r4
    rw [Fintype.card_fin]
    calc _ ≤ 2 * N * (e * (B + 2 * N)) + (e * N * (2 * N) + a + N * (e * (B + 2 * N))) := by gcongr
      _ = _ := by ring

theorem flips_mem {G : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψc : HasConductor ψ 1) (he : 1 ≤ e)
    (hq : resCard k ≠ 0) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → IsIntegral ℤ (ψ x : ℂ)) {B N : ℕ} :
    ∀ (l : List (ℕ × ℕ)) (S : G.PiLocalization₂) (a : ℕ),
      (∀ x ∈ l, CondLE ϖ e (G.nu x.1 x.2) ∧ ¬ IsUnram (G.nu x.1 x.2) ∧ (G.nu x.1 x.2 ϖ : ℂ) ∈ Lo (resCard k) B ∧
        (G.nu x.1 x.2 ϖ⁻¹ : ℂ) ∈ Lo (resCard k) B ∧ G.rank (x.1 + 1, x.2 + 1) ≤ N) →
      CanFlip S.path l → (∀ X, IsOpen (S.level X : Set (GL (Fin (G.rank X)) k)) ∧ S.level X ≤ KO k _) →
      S.IsAdmissible .one ϖ e → (∀ z, S.tensor z ∈ Lo (resCard k) a) →
      ∀ z, (S.flips .one ψ ϖ e l).tensor z ∈ Lo (resCard k) (a + l.length * (e * N * (3 * B + 8 * N))) := by
  intro l
  induction l with
  | nil => intro S a _ _ _ _ hF; simpa [Grid.PiLocalization₂.flips] using hF
  | cons x l ih =>
    intro S a hν hc hJ hT hF z
    obtain _ | ⟨hp, hc'⟩ := hc
    obtain ⟨x1, x2, x3, x4, x5⟩ := hν x List.mem_cons_self
    have := ih (S.flip .one ψ ϖ e x) _ (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (GlobalTheory.T.splitThetaGrid_isAdmissible_flipTensor ψ ϖ e hϖ hψc he S x x1 hp hJ hT)
      (flip_mem hϖ hψc hq hψ x1 x2 x3 x4 x5 S hp (hJ _).1 (hJ _).2 hT hF) z
    · rw [List.length_cons, Nat.succ_mul, add_comm (l.length * _), ← add_assoc]
      exact this
    change IsOpen (G.flipLevel x.1 x.2 S.level X : Set (GL (Fin (G.rank X)) k)) ∧ G.flipLevel x.1 x.2 S.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

end UpperTheory.FlipInt

end
