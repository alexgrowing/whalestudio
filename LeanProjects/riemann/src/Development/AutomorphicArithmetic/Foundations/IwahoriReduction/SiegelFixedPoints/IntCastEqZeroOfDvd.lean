import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.WcocEdge0
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSLMapMulInvMem
import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem cast_dvd {M d : ℕ} (h : d ∣ M) {a b : ℤ} (e : (a : ZMod M) = b) : (a : ZMod d) = b := by
  simpa using congrArg (ZMod.castHom h (ZMod d)) e

private theorem intCast_eq_zero_of_dvd {M d : ℕ} (h : d ∣ M) {a : ℤ} (e : (a : ZMod M) = 0) : (a : ZMod d) = 0 := by
  simpa using congrArg (ZMod.castHom h (ZMod d)) e

private theorem intCast_eq_one_of_dvd {M d : ℕ} (h : d ∣ M) {a : ℤ} (e : (a : ZMod M) = 1) : (a : ZMod d) = 1 := by
  have h1 := congrArg (ZMod.castHom h (ZMod d)) e
  rwa [map_intCast, map_one] at h1

private theorem en_mul (x y : SL(2, ℤ)) (i j : Fin 2) :
    en (x * y) i j = en x i 0 * en y 0 j + en x i 1 * en y 1 j := by
  simp [en, Matrix.mul_apply, Fin.sum_univ_two]

private theorem en_det (x : SL(2, ℤ)) : en x 0 0 * en x 1 1 - en x 0 1 * en x 1 0 = 1 := by
  have h := x.2
  rw [Matrix.det_fin_two] at h
  exact h

private noncomputable def PP (X : Tower Ω ε) (l n N M : ℕ) [Fact l.Prime] [NeZero M] (gm : (ZMod l)ˣ → SL(2, ℤ)) (W : X.K)
    (e : ZMod (l ^ n) → ℕ) : X.K :=
  ∏ r₀ : (ZMod l)ˣ, ∏ γ ∈ Gs N l M,
    X.sl (ofSL (gm r₀ * liftSL _ γ)) W ^ e ((en (gm r₀ * liftSL _ γ) 0 0 : ℤ) : ZMod (l ^ n))

private theorem PP_add (X : Tower Ω ε) (l n N M : ℕ) [Fact l.Prime] [NeZero M] (gm : (ZMod l)ˣ → SL(2, ℤ)) (W : X.K)
    (e e' : ZMod (l ^ n) → ℕ) :
    PP X l n N M gm W e * PP X l n N M gm W e' = PP X l n N M gm W (fun a => e a + e' a) := by
  simp only [PP, ← Finset.prod_mul_distrib, pow_add]

private theorem congruenceCondition_mul (X : Tower Ω ε) (l n N M : ℕ) [Fact l.Prime] [NeZero M] (gm : (ZMod l)ˣ → SL(2, ℤ)) (W : X.K)
    (k : ℕ) (e : ZMod (l ^ n) → ℕ) :
    PP X l n N M gm W (fun a => k * e a) = PP X l n N M gm W e ^ k := by
  simp only [PP, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun r _ => Finset.prod_congr rfl fun γ _ => ?_
  rw [mul_comm k, pow_mul]

private theorem PP_translate (X : Tower Ω ε) {l n N M : ℕ} [Fact l.Prime] [NeZero M] (hM : l ^ n ∣ M)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) {W : X.K}
    (hW : ∀ ν ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL ν) W = W) (e : ZMod (l ^ n) → ℕ) {δ : SL(2, ℤ)}
    (hδ : δ ∈ Gam N l) {t : ZMod (l ^ n)}
    (h10 : ((en δ 1 0 : ℤ) : ZMod (l ^ n)) = 0) (h11 : ((en δ 1 1 : ℤ) : ZMod (l ^ n)) = t) :
    X.sl (ofSL δ) (PP X l n N M gm W e) = PP X l n N M gm W (fun a => e (a * t)) := by
  have hmem : ∀ γ, γ ∈ Gs N l M ↔ γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) := by
    intro γ
    simp [Gs]
  have hδ' : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ ∈
      (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) := Subgroup.mem_map_of_mem _ hδ
  simp only [PP, map_prod, map_pow]
  refine Finset.prod_congr rfl fun r₀ _ => ?_
  refine Finset.prod_equiv (Equiv.mulRight (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ)) ?_ ?_
  · intro γ
    simp only [hmem, Equiv.coe_mulRight]
    exact ⟨fun h => mul_mem h hδ', fun h => by simpa using mul_mem h (inv_mem hδ')⟩
  · intro γ _
    simp only [Equiv.coe_mulRight]
    generalize hg : gm r₀ * liftSL M γ = g
    generalize hg' : gm r₀ * liftSL M (γ * Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ) = g'
    have hgg : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (g * δ) =
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g' := by
      rw [← hg, ← hg', map_mul, map_mul, map_mul, map_liftSL, map_liftSL, mul_assoc]
    have h1 : X.sl (ofSL δ) (X.sl (ofSL g) W) = X.sl (ofSL g') W := by
      have hν : (g * δ) * g'⁻¹ ∈ CongruenceSubgroup.Gamma M := by
        rw [CongruenceSubgroup.Gamma_mem']
        change Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) _ = 1
        rw [map_mul, map_inv, hgg, mul_inv_cancel]
      have e1 : g * δ = ((g * δ) * g'⁻¹) * g' := by group
      rw [← X.sl_mul, ← map_mul, e1, map_mul, X.sl_mul, hW _ hν]
    have e00 : ((en (g * δ) 0 0 : ℤ) : ZMod M) = ((en g' 0 0 : ℤ) : ZMod M) := by
      have h := congrArg (fun x : SL(2, ZMod M) => (x : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 0) hgg
      exact h
    have e00' := cast_dvd hM e00
    rw [en_mul] at e00'
    push_cast at e00'
    rw [h10] at e00'
    have hdet := congrArg (Int.cast : ℤ → ZMod (l ^ n)) (en_det δ)
    push_cast at hdet
    rw [h10, h11] at hdet
    have h2 : ((en g 0 0 : ℤ) : ZMod (l ^ n)) = ((en g' 0 0 : ℤ) : ZMod (l ^ n)) * t := by
      rw [← e00']
      linear_combination (-((en g 0 0 : ℤ) : ZMod (l ^ n))) * hdet
    rw [h1, h2]

private theorem wit_core (X : Tower Ω ε) {l n N M w c₀ : ℕ} [Fact l.Prime] [NeZero M] (hM : l ^ n ∣ M)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) {W : X.K} (hW : ∀ ν ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL ν) W = W)
    (hw : Odd w) {f : X.K} (hf : f = PP X l n N M gm W (fun a => a.val ^ w) ^ l ^ c₀) :
    Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f ∧
      ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
        ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ f * X.sl (ofSL δ) f = g ^ (l ^ n) := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n (Fact.out : l.Prime).ne_zero⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hv : ∀ a : ZMod (l ^ 0), a.val ^ w = 0 := fun a => by
      have h : a.val = 0 := Nat.lt_one_iff.1 (by simpa using ZMod.val_lt a)
      rw [h, zero_pow hw.pos.ne']
    have h1 : PP X l 0 N M gm W (fun a => a.val ^ w) = 1 := by
      unfold PP
      refine Finset.prod_eq_one fun r _ => Finset.prod_eq_one fun γ _ => ?_
      beta_reduce
      rw [hv, pow_zero]
    rw [h1, one_pow] at hf
    subst hf
    exact ⟨fun γ _ => map_one _, fun δ _ _ => ⟨1, fun γ _ => map_one _, by simp⟩⟩
  · have hinv : ∀ e, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (PP X l n N M gm W e) := by
      intro e δ hδ
      obtain ⟨-, d11, d10⟩ := (CongruenceSubgroup.Gamma1_mem _ _).1 hδ
      have h1 : δ ∈ Gam N l := by
        refine ⟨?_, ?_⟩
        · obtain ⟨d00, -, -⟩ := (CongruenceSubgroup.Gamma1_mem _ _).1 hδ
          exact (CongruenceSubgroup.Gamma1_mem _ _).2
            ⟨intCast_eq_one_of_dvd (Dvd.intro _ rfl) d00, intCast_eq_one_of_dvd (Dvd.intro _ rfl) d11, intCast_eq_zero_of_dvd (Dvd.intro _ rfl) d10⟩
        · exact CongruenceSubgroup.Gamma0_mem.2 (intCast_eq_zero_of_dvd ((dvd_pow_self l hn.ne').mul_left N) d10)
      have h2 := PP_translate X hM gm hW e (t := 1) h1 (intCast_eq_zero_of_dvd (Dvd.intro_left _ rfl) d10)
        (intCast_eq_one_of_dvd (Dvd.intro_left _ rfl) d11)
      simpa using h2
    have hdiv : ∀ a : ZMod (l ^ n), l ^ n ∣ a.val ^ w + (a * -1).val ^ w := by
      intro a
      rw [← ZMod.natCast_eq_zero_iff _ (l ^ n)]
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_neg_one, hw.neg_pow, add_neg_cancel]
    refine ⟨fun δ hδ => by rw [hf, map_pow, hinv _ δ hδ], fun δ hδ1 hδ2 => ?_⟩
    obtain ⟨-, -, d10, d11⟩ := CongruenceSubgroup.Gamma_mem.1 hδ2
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at d10 d11
    have h10 : ((en δ 1 0 : ℤ) : ZMod (l ^ n)) = 0 := neg_eq_zero.1 d10
    have h11 : ((en δ 1 1 : ℤ) : ZMod (l ^ n)) = -1 := by
      change ((((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ)) : ZMod (l ^ n)) = -1
      linear_combination -d11
    have h1 : δ ∈ Gam N l := ⟨hδ1, CongruenceSubgroup.Gamma0_mem.2 (intCast_eq_zero_of_dvd (dvd_pow_self l hn.ne') h10)⟩
    refine ⟨PP X l n N M gm W (fun a => (a.val ^ w + (a * -1).val ^ w) / l ^ n) ^ l ^ c₀,
      fun γ hγ => by rw [map_pow, hinv _ γ hγ], ?_⟩
    rw [hf, map_pow, PP_translate X hM gm hW _ h1 h10 h11, ← mul_pow, PP_add]
    have e1 : (fun a : ZMod (l ^ n) => a.val ^ w + (a * -1).val ^ w) =
        fun a => l ^ n * ((a.val ^ w + (a * -1).val ^ w) / l ^ n) :=
      funext fun a => (Nat.mul_div_cancel' (hdiv a)).symm
    rw [e1, congruenceCondition_mul, ← pow_mul, ← pow_mul, mul_comm]

private theorem smul_eq_nsmul_of_dvd (X : Tower Ω ε) {l n : ℕ} [Fact l.Prime] (a : ℤ_[l]) (k : ℕ)
    (h : (l : ℤ_[l]) ^ n ∣ a - k) (y : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))) :
    a • y = k • y := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have h0 : (a - k) • (Submodule.Quotient.mk v : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.2 h
  rw [sub_smul, sub_eq_zero] at h0
  rw [h0, Nat.cast_smul_eq_nsmul]

private theorem cls_one' (X : Tower Ω ε) (l n : ℕ) [Fact l.Prime] : X.cls l n 1 = 0 := by
  unfold Tower.cls
  rw [ofMul_one, TensorProduct.tmul_zero, Submodule.Quotient.mk_zero]

private theorem cls_pow' (X : Tower Ω ε) (l n : ℕ) [Fact l.Prime] (f : X.Kˣ) (k : ℕ) :
    X.cls l n (f ^ k) = k • X.cls l n f := by
  induction k with
  | zero => simp [cls_one']
  | succ k ih => rw [pow_succ, cls_mul, ih, succ_nsmul]

private theorem cls_prod' (X : Tower Ω ε) (l n : ℕ) [Fact l.Prime] {ι : Type*} (s : Finset ι) (f : ι → X.Kˣ) :
    X.cls l n (∏ i ∈ s, f i) = ∑ i ∈ s, X.cls l n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cls_one']
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, cls_mul, ih]

private theorem ex_dvd (l n w : ℕ) [Fact l.Prime] (g : SL(2, ℤ)) :
    (l : ℤ_[l]) ^ n ∣ ((en g 0 0 : ℤ) : ℤ_[l]) ^ w - (ex l n w g : ℕ) := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n (Fact.out : l.Prime).ne_zero⟩
  unfold ex
  rw [Nat.cast_pow]
  refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ w)
  have h : ((l ^ n : ℕ) : ℤ) ∣ en g 0 0 - ((((en g 0 0 : ℤ) : ZMod (l ^ n)).val : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨c, hc⟩ := h
  refine ⟨(c : ℤ_[l]), ?_⟩
  have h2 := congrArg (Int.cast : ℤ → ℤ_[l]) hc
  push_cast at h2
  exact h2

private theorem eval_term (X : Tower Ω ε) (l n w : ℕ) [Fact l.Prime] (W : X.Kˣ) (g : SL(2, ℤ)) :
    AdicCompletion.eval (idl l) (X.Kl l) n
      (X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) (fun u => (u 0) ^ w • clsK X l n (W : X.K)) ![1, 0]) =
      X.cls l n (Units.map (X.sl (ofSL g)).toRingEquiv.toMonoidHom W ^ ex l n w g) := by
  have hv : (mZl l (g : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![1, 0]) 0 = ((en g 0 0 : ℤ) : ℤ_[l]) := by
    simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, en]
  have hcl : AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n (W : X.K)) = X.cls l n W := by
    rw [eval_clsK X l n W.ne_zero, Units.mk0_val]
  change AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
    ((mZl l (g : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![1, 0]) 0 ^ w • clsK X l n (W : X.K))) = _
  rw [map_smul, map_smul, hv, toGQ_coe_SL, KmapA.eval_kmap X l _ n _ W hcl, cls_pow']
  exact smul_eq_nsmul_of_dvd X _ _ (ex_dvd l n w g) _

end SlopeTestRemainingChoices

theorem UpperTheory.Kd.L.wit :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (w m n c₀ : ℕ), Odd w → 1 ≤ m → ∀ (σ : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) b → ∃ f : X.Kˣ, (f : X.K) = FF X l n m N x c d w gm σ ^ l ^ c₀ ∧ IsWit X N l n b f := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm hP x w m n c₀ hw hm σ b hb
  obtain ⟨hWm, hW0⟩ := (UpperTheory.Kd.L.wcoc ε X l N c d gm hP x m n hm).1 σ
  have hWinv : ∀ ν ∈ CongruenceSubgroup.Gamma (topMu l n m N),
      X.sl (ofSL ν) (wkMu X l n m N x c d σ) = wkMu X l n m N x c d σ := by
    intro ν hν
    have h := Subfield.mem_iInf.1 (Subfield.mem_iInf.1 hWm ν) hν
    exact h
  have hM : l ^ n ∣ topMu l n m N := (pow_dvd_pow l (Nat.le_add_left n m)).mul_right _
  let u : X.Kˣ := Units.mk0 _ hW0
  let FU : X.Kˣ := ∏ r₀ : (ZMod l)ˣ, ∏ γ ∈ Gs N l (topMu l n m N),
    Units.map (X.sl (ofSL (gm r₀ * liftSL _ γ))).toRingEquiv.toMonoidHom u ^ ex l n w (gm r₀ * liftSL _ γ)
  have hFU : (FU : X.K) = PP X l n N (topMu l n m N) gm (wkMu X l n m N x c d σ) (fun a => a.val ^ w) := by
    simp only [FU, PP, Units.coe_prod, Units.val_pow_eq_pow_val, Units.coe_map]
    rfl
  have hcore := wit_core X hM gm hWinv hw (c₀ := c₀) (f := ((FU ^ l ^ c₀ : X.Kˣ) : X.K))
    (by rw [Units.val_pow_eq_pow_val, hFU])
  refine ⟨FU ^ l ^ c₀, by rw [Units.val_pow_eq_pow_val, hFU]; rfl, hcore.1, ?_, hcore.2⟩
  have h1 := hb.2 ![1, 0]
  rw [map_sub, sub_eq_zero] at h1
  rw [h1, map_smul]
  have h2 : AdicCompletion.eval (idl l) (X.Kl l) n (clsBmu X l n m N x c d (w + 2) gm σ ![1, 0]) = X.cls l n FU := by
    simp only [FU, cls_prod']
    simp only [clsBmu, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun r₀ _ => Finset.sum_congr rfl fun γ _ => ?_
    exact eval_term X l n w u _
  rw [h2, cls_pow', ← Nat.cast_smul_eq_nsmul ℤ_[l]]
  push_cast
  rfl
