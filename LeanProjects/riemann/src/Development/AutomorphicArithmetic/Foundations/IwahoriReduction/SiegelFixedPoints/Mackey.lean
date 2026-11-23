import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.CoefQCmulMem
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IntCastEqZeroOfDvd
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Witalg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.DlgalMapMul
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsDlDivM
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.OrderOfTranslationMod
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.WcocEdge0
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLogDerivQExpansionModPrimePowOfTranslationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionFinsetProdZpowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowSlashTPow
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.Mk

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private lemma mem_topL (X : Tower Ω ε) {M : ℕ} {w : X.K} (hw : w ∈ topL X M) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma M) : X.sl (ofSL γ) w = w := by
  have h1 := (Subfield.mem_iInf.1 hw) γ
  have h2 := (Subfield.mem_iInf.1 h1) hγ
  exact h2

private lemma sl_eq_of_map (X : Tower Ω ε) {M : ℕ} {w : X.K} (hw : w ∈ topL X M) {u v : SL(2, ℤ)}
    (h : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) u =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) v) :
    X.sl (ofSL u) w = X.sl (ofSL v) w := by
  have hg : u * v⁻¹ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem']
    show Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (u * v⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have e : u = (u * v⁻¹) * v := by group
  conv_lhs => rw [e, map_mul, X.sl_mul, mem_topL X hw hg]

private lemma map_T_pow (M : ℕ) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (ModularGroup.T ^ M) = 1 := by
  have h : (ModularGroup.T ^ M : SL(2, ℤ)) = ModularGroup.T ^ (M : ℤ) := by rw [zpow_natCast]
  ext i j
  rw [h, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp

private lemma sl_mem_KT (X : Tower Ω ε) {M : ℕ} {w : X.K} (hw : w ∈ topL X M) (g : SL(2, ℤ)) :
    X.sl (ofSL g) w ∈ KT X M := by
  rw [KT.mem_def, ← X.sl_mul, ← map_mul]
  apply sl_eq_of_map X hw
  rw [map_mul, map_T_pow, mul_one]

private lemma entry_mul_T_pow (a : SL(2, ℤ)) (b : ℕ) : en (a * ModularGroup.T ^ b) 0 0 = en a 0 0 := by
  have h : (ModularGroup.T ^ b : SL(2, ℤ)) = ModularGroup.T ^ (b : ℤ) := by rw [zpow_natCast]
  unfold en
  rw [h, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  simp

private lemma T_mem_Gam (N l b : ℕ) : (ModularGroup.T ^ b : SL(2, ℤ)) ∈ Gam N l := by
  apply pow_mem
  refine ⟨?_, ?_⟩
  · show ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  · show ModularGroup.T ∈ CongruenceSubgroup.Gamma0 l
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.coe_T]

private lemma Gs_mul_Tm {N l M : ℕ} [NeZero M] {γ : SL(2, ZMod M)} (h : γ ∈ Gs N l M) (b : ℕ) :
    γ * Tm M b ∈ Gs N l M := by
  classical
  unfold Gs at *
  rw [Finset.mem_filter] at *
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 h.2
  exact Subgroup.mem_map.2 ⟨a * ModularGroup.T ^ b, mul_mem ha (T_mem_Gam N l b), map_mul _ _ _⟩

end UpperTheory.Kd.L.Mk

namespace UpperTheory.Kd.L.Mk

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private lemma FF_eq (X : Tower Ω ε) {l : ℕ} [Fact l.Prime] {n m N : ℕ} [NeZero N] {x : ZMod N} {c d w : ℕ}
    {gm : (ZMod l)ˣ → SL(2, ℤ)} (hp : Par l N c d gm) (hm : 1 ≤ m) (σ : Ω ≃ₐ[ℚ] Ω)
    {R : Finset SL(2, ZMod (topMu l n m N))} (hR : IsReps N l (topMu l n m N) R)
    (hw : wkMu X l n m N x c d σ ∈ topL X (topMu l n m N))
    (hrep : ∀ γ ∈ Gs N l (topMu l n m N),
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (topMu l n m N))) (liftSL (topMu l n m N) γ) = γ) :
    FF X l n m N x c d w gm σ = ∏ r₀ : (ZMod l)ˣ, ∏ γ ∈ R,
      nrmT X (topMu l n m N) (X.sl (ofSL (gm r₀ * liftSL _ γ)) (wkMu X l n m N x c d σ)) ^
        ex l n w (gm r₀ * liftSL _ γ) := by
  classical
  unfold FF
  refine Finset.prod_congr rfl fun r₀ _ => ?_
  have hbij : ∏ γ ∈ Gs N l (topMu l n m N), X.sl (ofSL (gm r₀ * liftSL _ γ)) (wkMu X l n m N x c d σ) ^
        ex l n w (gm r₀ * liftSL _ γ) =
      ∏ p ∈ R ×ˢ Finset.range (topMu l n m N),
        X.sl (ofSL (gm r₀ * liftSL _ (p.1 * Tm (topMu l n m N) p.2))) (wkMu X l n m N x c d σ) ^
          ex l n w (gm r₀ * liftSL _ (p.1 * Tm (topMu l n m N) p.2)) := by
    symm
    refine Finset.prod_bij (fun p _ => p.1 * Tm (topMu l n m N) p.2) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro p hp'
      exact Gs_mul_Tm (hR.1 (Finset.mem_product.1 hp').1) _
    · intro p hp' q hq e
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp'
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
      have hG := Gs_mul_Tm (hR.1 hp1) p.2
      have := (hR.2 _ hG).unique (y₁ := p) (y₂ := q) ⟨hp1, Finset.mem_range.1 hp2, rfl⟩
        ⟨hq1, Finset.mem_range.1 hq2, e⟩
      exact this
    · intro γ hγ
      obtain ⟨p, ⟨h1, h2, h3⟩, -⟩ := hR.2 γ hγ
      exact ⟨p, Finset.mem_product.2 ⟨h1, Finset.mem_range.2 h2⟩, h3.symm⟩
  rw [hbij, Finset.prod_product]
  refine Finset.prod_congr rfl fun γ hγ => ?_
  unfold nrmT
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun b _ => ?_
  have hmap : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (topMu l n m N)))
        (gm r₀ * liftSL _ (γ * Tm (topMu l n m N) b)) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (topMu l n m N)))
        (gm r₀ * liftSL _ γ * ModularGroup.T ^ b) := by
    rw [map_mul, map_mul, map_mul, hrep _ (Gs_mul_Tm (hR.1 hγ) b), hrep _ (hR.1 hγ), mul_assoc]
    rfl
  have hsl := sl_eq_of_map X hw hmap
  have hex : ex l n w (gm r₀ * liftSL _ (γ * Tm (topMu l n m N) b)) = ex l n w (gm r₀ * liftSL _ γ) := by
    have h00 := congrArg (fun g : SL(2, ZMod (topMu l n m N)) => g.1 0 0) hmap
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] at h00
    have hd : l ^ n ∣ topMu l n m N := by
      unfold topMu
      exact Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_left n m)) _
    have h2 := congrArg (ZMod.castHom hd (ZMod (l ^ n))) h00
    simp only [map_intCast] at h2
    unfold ex
    have h3 : en (gm r₀ * liftSL _ (γ * Tm (topMu l n m N) b)) 0 0 =
        ((gm r₀ * liftSL _ (γ * Tm (topMu l n m N) b) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := rfl
    have h4 := entry_mul_T_pow (gm r₀ * liftSL (topMu l n m N) γ) b
    rw [show ((en (gm r₀ * liftSL _ (γ * Tm (topMu l n m N) b)) 0 0 : ℤ) : ZMod (l ^ n)) =
      ((en (gm r₀ * liftSL (topMu l n m N) γ) 0 0 : ℤ) : ZMod (l ^ n)) by rw [← h4]; exact h2]
  rw [hsl, hex, map_mul, X.sl_mul]

end UpperTheory.Kd.L.Mk

namespace UpperTheory.Kd.L.Mk

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private lemma zt_prim (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (L : ℕ) : IsPrimitiveRoot (zt ε l L) (l ^ L) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have h := isPrimitiveRoot_eOm ε (m := l ^ L) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  unfold zt
  rwa [Nat.cast_pow] at h

private lemma zt_pow (ε : Ω →+* ℂ) (l L n : ℕ) [Fact l.Prime] : zt ε l n = zt ε l (L + n) ^ (l ^ L) := by
  unfold zt
  rw [← GlobalTheory.Glue.NrmT.eOm_nat_mul]
  congr 1
  have hl : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  push_cast
  field_simp
  ring

private lemma fix_of_inertial {A : ValuationSubring Ω} {l : ℕ} [Fact l.Prime] (hl : ((l : ℕ) : Ω) ∈ A.nonunits)
    {D : ℕ} (hD0 : 0 < D) (hD : ¬ l ∣ D) {s : Ω ≃ₐ[ℚ] Ω}
    (hs : ∀ y ∈ A, A.valuation (s y - y) < 1) {z : Ω} (hz : z ^ D = 1) : s z = z := by
  by_contra hne
  have hzA : z ∈ A := GlobalTheory.Glue.NrmT.mem_of_pow_eq_one A hD0 hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hD0.ne'] at hz
    exact zero_ne_one hz
  have hzi : z⁻¹ ∈ A := by
    have h1 : z ^ (D - 1) * z = 1 := by rw [← pow_succ, Nat.sub_add_cancel hD0, hz]
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact pow_mem hzA _
  have hmul : ∀ {a x : Ω}, a ∈ A → A.valuation x < 1 → A.valuation (a * x) < 1 := fun {a x} ha hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff a).2 ha)) hx
  set u : Ω := s z * z⁻¹ with hu
  have huD : u ^ D = 1 := by
    rw [hu, mul_pow, ← map_pow, hz, map_one, inv_pow, hz, inv_one, one_mul]
  have hu1 : u ≠ 1 := fun h => hne ((mul_inv_eq_one₀ hz0).1 h)
  have huA : u ∈ A := GlobalTheory.Glue.NrmT.mem_of_pow_eq_one A hD0 huD
  have hv : A.valuation (u - 1) < 1 := by
    have e : u - 1 = z⁻¹ * (s z - z) := by
      rw [hu]
      field_simp
    rw [e]
    exact hmul hzi (hs z hzA)
  have hk : ∀ k : ℕ, A.valuation (u ^ k - 1) < 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : u ^ (k + 1) - 1 = u ^ k * (u - 1) + (u ^ k - 1) := by ring
      rw [e]
      exact Valuation.map_add_lt _ (hmul (pow_mem huA k) hv) ih
  have hsum : ∑ k ∈ Finset.range D, u ^ k = 0 := by
    have h := geom_sum_mul u D
    rw [huD, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hu1)
  have hDv : A.valuation ((D : ℕ) : Ω) < 1 := by
    have e : ((D : ℕ) : Ω) = -∑ k ∈ Finset.range D, (u ^ k - 1) := by
      rw [Finset.sum_sub_distrib, hsum]
      simp
    rw [e, Valuation.map_neg]
    exact Valuation.map_sum_lt _ one_ne_zero fun k _ => hk k
  have hlv : A.valuation ((l : ℕ) : Ω) < 1 := hl
  have hcop : IsCoprime (l : ℤ) (D : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hD)
  obtain ⟨a, b, hab⟩ := hcop
  have e : (1 : Ω) = (a : Ω) * ((l : ℕ) : Ω) + (b : Ω) * ((D : ℕ) : Ω) := by
    have := congrArg (Int.cast : ℤ → Ω) hab
    push_cast at this
    exact this.symm
  have h1 : A.valuation (1 : Ω) < 1 := by
    rw [e]
    exact Valuation.map_add_lt _ (hmul (intCast_mem A a) hlv) (hmul (intCast_mem A b) hDv)
  rw [map_one] at h1
  exact lt_irrefl _ h1

private lemma mem_fixMu_of_inertial {A : ValuationSubring Ω} {l : ℕ} [Fact l.Prime]
    (hl : ((l : ℕ) : Ω) ∈ A.nonunits) {N L : ℕ} (hN : 0 < N) (hlN : ¬ l ∣ N) {s : Ω ≃ₐ[ℚ] Ω}
    (hs : ∀ y ∈ A, A.valuation (s y - y) < 1) (hzt : s (zt ε l L) = zt ε l L) :
    s ∈ fixMu Ω (l ^ L * (N * N)) := by
  rw [mem_fixMu_iff]
  intro z hz
  have hlp : l.Prime := Fact.out
  have hc1 : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
  have hcop : IsCoprime ((l ^ L : ℕ) : ℤ) ((N * N : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left L (Nat.Coprime.mul_right hc1 hc1))
  obtain ⟨a, b, hab⟩ := hcop
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.mul_ne_zero (pow_ne_zero _ hlp.ne_zero) (Nat.mul_ne_zero hN.ne' hN.ne'))] at hz
    exact zero_ne_one hz
  have hsplit : z = z ^ (a * ((l ^ L : ℕ) : ℤ)) * z ^ (b * ((N * N : ℕ) : ℤ)) := by
    rw [← zpow_add₀ hz0, hab, zpow_one]
  have hzi : ∀ k : ℤ, z ^ (((l ^ L * (N * N) : ℕ) : ℤ) * k) = 1 := fun k => by
    rw [zpow_mul, zpow_natCast, hz, one_zpow]
  have h2 : (z ^ (a * ((l ^ L : ℕ) : ℤ))) ^ (N * N) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, ← hzi a]
    congr 1
    push_cast
    ring
  have h1 : (z ^ (b * ((N * N : ℕ) : ℤ))) ^ (l ^ L) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, ← hzi b]
    congr 1
    push_cast
    ring
  have hs2 := fix_of_inertial hl (Nat.mul_pos hN hN)
    (fun h => ((hlp.dvd_mul).1 h).elim hlN hlN) hs h2
  obtain ⟨i, -, hi⟩ := (zt_prim ε l L).eq_pow_of_pow_eq_one h1
  have hs1 : s (z ^ (b * ((N * N : ℕ) : ℤ))) = z ^ (b * ((N * N : ℕ) : ℤ)) := by
    rw [← hi, map_pow, hzt]
  rw [hsplit, map_mul, hs2, hs1]

private lemma conj_apply (τ s : Ω ≃ₐ[ℚ] Ω) (x : Ω) : τ ((τ⁻¹ * s * τ) x) = s (τ x) := by
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply τ τ⁻¹, mul_inv_cancel]
  rfl

private lemma conj_fix (τ : Ω ≃ₐ[ℚ] Ω) {s : Ω ≃ₐ[ℚ] Ω} {M : ℕ} (hs : s ∈ fixMu Ω M) : τ⁻¹ * s * τ ∈ fixMu Ω M := by
  rw [mem_fixMu_iff] at hs ⊢
  intro z hz
  apply τ.injective
  rw [conj_apply]
  exact hs _ (by rw [← map_pow, hz, map_one])

private lemma conj_apply_zt_eq_of_apply_zt_eq (τ s : Ω ≃ₐ[ℚ] Ω) (l L n e : ℕ) [Fact l.Prime]
    (h : s (zt ε l (L + n)) = zt ε l n ^ e * zt ε l (L + n)) :
    (τ⁻¹ * s * τ) (zt ε l (L + n)) = zt ε l n ^ e * zt ε l (L + n) := by
  apply τ.injective
  rw [conj_apply]
  have hprim := zt_prim ε l (L + n)
  have hroot : (τ (zt ε l (L + n))) ^ (l ^ (L + n)) = 1 := by rw [← map_pow, hprim.pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hroot
  have hτu : τ (zt ε l n) = zt ε l n ^ i := by
    conv_lhs => rw [zt_pow ε l L n, map_pow, ← hi, ← pow_mul, mul_comm, pow_mul, ← zt_pow ε l L n]
  rw [← hi, map_pow, h, map_mul, map_pow, hτu, ← hi, mul_pow, ← pow_mul, ← pow_mul, mul_comm e i]

private lemma cycM_eq_one (ε : Ω →+* ℂ) {M : ℕ} [NeZero M] (hM : 1 < M) {s : Ω ≃ₐ[ℚ] Ω} (hs : s ∈ fixMu Ω M) :
    cycM M s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hfix := (mem_fixMu_iff s).1 hs
  have hv1 : (1 : ZMod M).val = 1 := by rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hM]
  have hspec := cycM_spec M s ⟨1, fun z hz => by rw [hfix z hz, Units.val_one, hv1, pow_one]⟩
  have hp := isPrimitiveRoot_eOm ε (m := M) (NeZero.ne M)
  have h1 := hspec _ hp.pow_eq_one
  rw [hfix _ hp.pow_eq_one] at h1
  have h2 : 1 = (cycM M s : ZMod M).val := hp.pow_inj hM (ZMod.val_lt _) (by rwa [pow_one])
  exact Units.ext (ZMod.val_injective M (by rw [← h2, Units.val_one, hv1]))

private lemma cgA_map {A : ValuationSubring Ω} (τ : Ω ≃ₐ[ℚ] Ω) {l n : ℕ} {a b : Ω}
    (h : CgA (A.comap (τ : Ω →+* Ω)) l n a b) : CgA A l n (τ a) (τ b) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨τ z, ValuationSubring.mem_comap.1 hz, by rw [← map_sub, e, map_mul, map_pow, map_natCast]⟩

private lemma cgA_sum {A : ValuationSubring Ω} {l n : ℕ} {ι : Type} (I : Finset ι) (k : ι → ℕ) (a b : ι → Ω)
    (h : ∀ i ∈ I, CgA A l n (a i) (b i)) :
    CgA A l n (∑ i ∈ I, (k i : Ω) * a i) (∑ i ∈ I, (k i : Ω) * b i) := by
  classical
  choose! z hz e using h
  refine ⟨∑ i ∈ I, (k i : Ω) * z i, sum_mem fun i hi => mul_mem (natCast_mem A _) (hz i hi), ?_⟩
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← mul_sub, e i hi]
  ring

private lemma wit_sum (X : Tower Ω ε) {l : ℕ} [Fact l.Prime] {N n : ℕ} [CharZero Ω] (hN : 1 ≤ N) {ι : Type} (S : Finset ι)
    (b : ι → X.Fn l) (f : ι → X.Kˣ) (h : ∀ i ∈ S, IsWit X N l n (b i) (f i)) :
    IsWit X N l n (∑ i ∈ S, b i) (∏ i ∈ S, f i) := by
  classical
  obtain ⟨hadd, hzero, -, -⟩ := UpperTheory.Kd.L.witalg ε X l N n hN
  induction S using Finset.induction_on with
  | empty => simpa using hzero
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact hadd _ _ _ _ (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end UpperTheory.Kd.L.Mk

namespace UpperTheory.Kd.L.Mk

private lemma cgA_trans {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {l n : ℕ} {a b c : Ω}
    (h : CgA A l n a b) (h' : CgA A l n b c) : CgA A l n a c := by
  obtain ⟨z, hz, e⟩ := h
  obtain ⟨z', hz', e'⟩ := h'
  exact ⟨z + z', add_mem hz hz', by rw [mul_add, ← e, ← e']; ring⟩

end UpperTheory.Kd.L.Mk

open UpperTheory.Kd.L.Mk in
theorem UpperTheory.Kd.L.mackey :
    ∀ (l : ℕ) [Fact l.Prime], ∃ cc : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (x : ZMod N) (w m n c₀ : ℕ), Odd w → 1 ≤ m → 1 ≤ n → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l, (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ)) → ∀ R, IsReps N l (topMu l n m N) R → ∀ z : (ZMod (l ^ (m + n)))ˣ, ∃ ξ : ℚ → Ω, (∀ r, ξ r ∈ A) ∧ ∀ s, Stab A s → (∀ y ∈ A, A.valuation (s y - y) < 1) → s (zt ε l (m + n)) = zt ε l (m + n) → ∀ t : ZMod (l ^ n), s (zt ε l (m + n + n)) = zt ε l n ^ t.val * zt ε l (m + n + n) → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n (bMid X l n m N bB s z) φ → ∀ r : ℚ, CgA A l n ((l : Ω) ^ cc * φ.coeff r) (s (ξ r) - ξ r + (l : Ω) ^ cc * ((l : Ω) ^ c₀ * Fsum ε l n m N x c d w gm R z r * (t.val : Ω)))  := by
  intro l _
  obtain ⟨cc, hone⟩ := UpperTheory.Kd.L.one l
  refine ⟨cc, ?_⟩
  intro Ω _ _ _ _ ε X N _ c d gm hp A hl x w m n c₀ hw hm hn bB hB R hR z
  simp only [bMid, bTop, Fsum]
  generalize repM (Ω := Ω) (topM l n m (N * N)) = ρ
  generalize (Finset.univ.filter fun y => redTop l n m N y = z) = S
  classical
  have hlp : l.Prime := Fact.out
  have hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := X.j_hol
    exact ⟨φ, h2, h1⟩
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hMpos : 0 < topMu l n m N := Nat.pos_of_ne_zero (NeZero.ne _)
  have hdvd : N * l ∣ topMu l n m N := by
    unfold topMu
    rw [Nat.mul_comm N l]
    exact mul_dvd_mul (dvd_pow_self l (by omega)) (Dvd.intro _ rfl)
  have hrp := fun γ hγ r₀ => (UpperTheory.Kd.L.reps l N c d gm hp (topMu l n m N) hdvd).2 γ hγ r₀
  have hrep : ∀ γ ∈ Gs N l (topMu l n m N),
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (topMu l n m N))) (liftSL (topMu l n m N) γ) = γ :=
    fun γ hγ => (hrp γ hγ 1).1
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hlA : ∀ y, ((l : ℕ) : Ω) ∈ (A.comap ((ρ y : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω)).nonunits := by
    intro y
    have hl' := hl
    rw [ValuationSubring.mem_nonunits_iff_or] at hl' ⊢
    refine Or.inr fun h => ?_
    have h2 := ValuationSubring.mem_comap.1 h
    rw [map_inv₀, map_natCast] at h2
    exact (hl'.resolve_left hl0) h2
  have hξ : ∀ y (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), ∃ ξ : ℚ → Ω, γ ∈ R →
      ((∀ r, ξ r ∈ A.comap ((ρ y : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω)) ∧ ∀ s ∈ fixMu Ω (topMu l n m N),
        Stab (A.comap ((ρ y : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω)) s → ∀ t : ZMod (l ^ n),
        s (zt ε l (m + n + n)) = zt ε l n ^ t.val * zt ε l (m + n + n) → ∀ φ : HahnSeries ℚ Ω,
        IsDl X (A.comap ((ρ y : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω)) l n ((topMu l n m N) : ℚ)
          (X.sl (ofSL (gm r₀ * liftSL _ γ)) (wkMu X l n m N x c d s)) φ → ∀ r : ℚ,
        CgA (A.comap ((ρ y : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω)) l n ((l : Ω) ^ cc * φ.coeff r)
          (s (ξ r) - ξ r + (l : Ω) ^ cc * ((N : Ω) ^ 3 * EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) r * (t.val : Ω)))) := by
    intro y r₀ γ
    by_cases hγ : γ ∈ R
    · obtain ⟨-, hg1, -, hg2, hg3⟩ := hrp γ (hR.1 hγ) r₀
      obtain ⟨-, ξ, h1, h2⟩ := hone ε X N c d gm hp _ (hlA y) x m n hm hn _ hg1 hg2 hg3
      exact ⟨ξ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hγ⟩
  choose ξ hξ using hξ
  obtain ⟨I, hI⟩ : ∃ I : Finset (_ × (ZMod l)ˣ × SL(2, ZMod (topMu l n m N))),
      I = S ×ˢ ((Finset.univ : Finset (ZMod l)ˣ) ×ˢ R) := ⟨_, rfl⟩
  have hIR : ∀ i ∈ I, i.2.2 ∈ R := fun i hi => by
    rw [hI] at hi
    exact (Finset.mem_product.1 (Finset.mem_product.1 hi).2).2
  obtain ⟨mx, hmx⟩ : ∃ mx : (_ × (ZMod l)ˣ × SL(2, ZMod (topMu l n m N))) → ℕ,
      ∀ i, mx i = ex l n w (gm i.2.1 * liftSL _ i.2.2) * l ^ c₀ := ⟨_, fun _ => rfl⟩
  refine ⟨fun r => if r.den = 1 then ∑ i ∈ I, (mx i : Ω) * ρ i.1 (ξ i.1 i.2.1 i.2.2 r) else 0, ?_, ?_⟩
  · intro r
    dsimp only
    split_ifs
    · exact sum_mem fun i hi => mul_mem (natCast_mem A _)
        (ValuationSubring.mem_comap.1 ((hξ i.1 i.2.1 i.2.2 (hIR i hi)).1 r))
    · exact zero_mem A
  intro s hStab hin hzt t ht φ hφ r
  have hsfix : s ∈ fixMu Ω (topMu l n m N) := mem_fixMu_of_inertial hl hN0 hp.cop hin hzt
  have hM1 : 1 < topM l n m (N * N) := by
    have h1 : l ∣ topM l n m (N * N) := by
      unfold topM
      exact Dvd.dvd.mul_right (dvd_pow_self l (by omega)) _
    exact lt_of_lt_of_le hlp.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) h1)
  have hcyc : cycM (topM l n m (N * N)) s = 1 := cycM_eq_one ε hM1 hsfix
  simp only [hcyc, inv_one, mul_one] at hφ
  obtain ⟨σ, hσd⟩ : ∃ σ : _ → (Ω ≃ₐ[ℚ] Ω), ∀ y, σ y = (ρ y)⁻¹ * s * ρ y := ⟨_, fun _ => rfl⟩
  simp only [← hσd] at hφ
  have hσ : ∀ y, σ y ∈ fixMu Ω (topMu l n m N) := fun y => by rw [hσd]; exact conj_fix _ hsfix
  have hσS : ∀ y, Stab (A.comap ((ρ y : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω)) (σ y) := fun y u => by
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    show ρ y (σ y u) ∈ A ↔ ρ y u ∈ A
    rw [hσd, conj_apply]
    exact hStab _
  have hσt : ∀ y, σ y (zt ε l (m + n + n)) = zt ε l n ^ t.val * zt ε l (m + n + n) := fun y => by
    rw [hσd]
    exact conj_apply_zt_eq_of_apply_zt_eq (ρ y) s l (m + n) n t.val ht
  have hwx : ∀ y, ∃ f : X.Kˣ, (f : X.K) = FF X l n m N x c d w gm (σ y) ^ l ^ c₀ ∧ IsWit X N l n (bB (σ y)) f :=
    fun y => UpperTheory.Kd.L.wit ε X l N c d gm hp x w m n c₀ hw hm (σ y) _ (hB _ (hσ y))
  choose f hf1 hf2 using hwx
  have hwc := fun σ' => (UpperTheory.Kd.L.wcoc ε X l N c d gm hp x m n hm).1 σ'
  have hFF := fun y => FF_eq (w := w) X hp hm (σ y) hR (hwc _).1 hrep
  have hψx : ∀ y (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), ∃ ψ : HahnSeries ℚ Ω,
      IsDl X (A.comap ((ρ y : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω)) l n ((topMu l n m N : ℕ) : ℚ)
        (X.sl (ofSL (gm r₀ * liftSL _ γ)) (wkMu X l n m N x c d (σ y))) ψ ∧
      ∀ r : ℚ, ψ.coeff r ≠ 0 → (r * ((topMu l n m N : ℕ) : ℚ)).den = 1 := fun y r₀ γ =>
    GlobalTheory.T.exists_logDerivQExpansion_modPrimePow_of_translationInvariant ε X hj l _ (hlA y) n (topMu l n m N) _ hMpos
      ((map_ne_zero _).2 (hwc _).2) (sl_mem_KT X (hwc _).1 _)
  choose ψ hψ1 hψ2 using hψx
  have hn2 := fun y r₀ γ => UpperTheory.Kd.L.nrm ε X l _ (hlA y) n (topMu l n m N) hMpos _ (ψ y r₀ γ)
    (GlobalTheory.Glue.NrmT.resZ (ψ y r₀ γ)) (sl_mem_KT X (hwc _).1 _) (hψ1 y r₀ γ) (hψ2 y r₀ γ)
    (GlobalTheory.Glue.NrmT.resZ_coeff _)
  have hD := fun y r₀ γ => UpperTheory.Kd.L.dlgal ε X l A _ (ρ y) (fun _ => ValuationSubring.mem_comap) n 1 _ _ (hn2 y r₀ γ)
  have hP := GlobalTheory.T.isLogDerivQExpansion_finset_prod_zpow ε X hj l A hl n 1 _ I
    (fun i => X.gal (ρ i.1) (nrmT X (topMu l n m N) (X.sl (ofSL (gm i.2.1 * liftSL _ i.2.2)) (wkMu X l n m N x c d (σ i.1)))))
    (fun i => HahnSeries.map (GlobalTheory.Glue.NrmT.resZ (ψ i.1 i.2.1 i.2.2)) (ρ i.1 : Ω →+* Ω))
    (fun i => (mx i : ℤ)) (fun i _ => hD i.1 i.2.1 i.2.2)
  have hFval : ((∏ y ∈ S, Units.map (X.gal (ρ y)).toMonoidHom (f y) : X.Kˣ) : X.K) =
      ∏ i ∈ I, X.gal (ρ i.1) (nrmT X (topMu l n m N) (X.sl (ofSL (gm i.2.1 * liftSL _ i.2.2)) (wkMu X l n m N x c d (σ i.1)))) ^ (mx i : ℤ) := by
    rw [Units.coe_prod, hI, Finset.prod_product]
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [Finset.prod_product]
    show X.gal (ρ y) (f y) = _
    rw [hf1, hFF, map_pow, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun r₀ _ => ?_
    rw [map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun γ _ => ?_
    rw [map_pow, hmx, zpow_natCast, pow_mul]
  have hwit := wit_sum X hN0 S (fun y => X.galB l (ρ y) (bB (σ y)))
    (fun y => Units.map (X.gal (ρ y)).toMonoidHom (f y))
    (fun y _ => (UpperTheory.Kd.L.witalg ε X l N n hN0).2.2.1 (ρ y) _ _ (hf2 y))
  have hTh := (isThB_iff X A N l n _ _).2 ⟨_, hwit, by rw [hFval]; exact hP⟩
  have hmemB : ∑ y ∈ S, X.galB l (ρ y) (bB (σ y)) ∈ X.B N l w := sum_mem fun y _ =>
    GlobalTheory.T.galB_mem_kummer_invariant_set ε X ε.injective hj N l w hp.odd hp.five
      ((Nat.Prime.coprime_iff_not_dvd hlp).2 hp.cop).symm hw (ρ y) _ (hB _ (hσ y)).1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hun := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol hp.odd hp.cop hp.five hl n w hw _ hmemB φ _ hφ hTh r
  have hun2 := GlobalTheory.Glue.NrmT.cgA_mul A l n (pow_mem (natCast_mem A l) cc) hun
  refine cgA_trans hun2 ?_
  have hΦ : ∀ r : ℚ, (∑ i ∈ I, (mx i : ℤ) • HahnSeries.map (GlobalTheory.Glue.NrmT.resZ (ψ i.1 i.2.1 i.2.2)) (ρ i.1 : Ω →+* Ω)).coeff r =
      ∑ i ∈ I, (mx i : Ω) * ρ i.1 (if r.den = 1 then (ψ i.1 i.2.1 i.2.2).coeff r else 0) := fun r => by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [HahnSeries.coeff_smul, zsmul_eq_mul, Int.cast_natCast]
    rfl
  rw [hΦ]
  by_cases hr : r.den = 1
  · simp only [hr, if_true]
    have hab : ∀ i ∈ I, CgA A l n ((l : Ω) ^ cc * ρ i.1 ((ψ i.1 i.2.1 i.2.2).coeff r))
        (s (ρ i.1 (ξ i.1 i.2.1 i.2.2 r)) - ρ i.1 (ξ i.1 i.2.1 i.2.2 r) +
          (l : Ω) ^ cc * ((N : Ω) ^ 3 * ρ i.1 (EE ε l (m + n) N x c d (gm i.2.1 * liftSL _ i.2.2) r) * (t.val : Ω))) := by
      intro i hi
      have h1 := (hξ i.1 i.2.1 i.2.2 (hIR i hi)).2 (σ i.1) (hσ _) (hσS _) t (hσt _) _ (hψ1 i.1 i.2.1 i.2.2) r
      have h2 := cgA_map (ρ i.1) h1
      rw [hσd] at h2
      simp only [map_add, map_sub, map_mul, map_pow, map_natCast, conj_apply] at h2
      exact h2
    have h3 := cgA_sum I mx _ _ hab
    have e1 : (l : Ω) ^ cc * ∑ i ∈ I, (mx i : Ω) * ρ i.1 ((ψ i.1 i.2.1 i.2.2).coeff r) =
        ∑ i ∈ I, (mx i : Ω) * ((l : Ω) ^ cc * ρ i.1 ((ψ i.1 i.2.1 i.2.2).coeff r)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1]
    convert h3 using 1
    have e2 : ∑ y ∈ S, ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R, (ex l n w (gm r₀ * liftSL _ γ) : Ω) * ρ y (EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) r) =
        ∑ i ∈ I, (ex l n w (gm i.2.1 * liftSL _ i.2.2) : Ω) * ρ i.1 (EE ε l (m + n) N x c d (gm i.2.1 * liftSL _ i.2.2) r) := by
      rw [hI, Finset.sum_product]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_product]
    rw [e2, map_sum, ← Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_natCast, hmx]
    push_cast
    ring
  · simp only [hr, if_false, map_zero, mul_zero, Finset.sum_const_zero, sub_zero, add_zero, zero_mul]
    exact ⟨0, zero_mem A, by ring⟩
