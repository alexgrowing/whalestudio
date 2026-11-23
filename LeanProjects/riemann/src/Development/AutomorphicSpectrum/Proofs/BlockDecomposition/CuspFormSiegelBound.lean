import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementActsOnFrameColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementArchimedeanMatrixForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetArchimedeanNormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT bc)
open IsDedekindDomain
open scoped TensorProduct NNReal ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelHt

open GlobalTheory.Doubling (absE absE_apply absEw_eq_sq absEv_apply absE_inclR unitInf unitFin finite_mulSupport_absEv)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absE_entry_le {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} (x : GL (Fin n) (AF F ⊗[F] E))
    (u : (AF F ⊗[F] E)ˣ) (i j : Fin n) (hu : u.1 = x.1 i j) : absE F E u ≤ heightGL F x ^ 2 := by
  rw [absE_apply, heightGL, mul_pow, ← Finset.prod_pow, finprod_pow (finite_mulSupport_htFin F x)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_absEv u) ?_ fun v => ?_)
  · obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    rw [absEw_eq_sq hσ τ]
    refine pow_le_pow_left' ?_ 2
    have e : infEmb τ (unitInf F E w u).1 = ((x.1.map (compInf F E w)).map (infEmb τ)) i j := by
      change infEmb τ (compInf F E w u.1) = _
      rw [hu]; rfl
    rw [e]
    exact (GlobalTheory.SWAbsGrowth.entry_le_opNorm _ i j).trans
      (((normInf_le_iff F w).1 le_rfl τ).trans (le_htOf (normInf F w) (bc (compInf F E w) x)))
  · exact (finite_mulSupport_htFin F x).subset fun v hv h => hv (by simp only [h, one_pow])
  · have e : (unitFin F E v u).1 = (x.1.map (compFin F E v)) i j := by
      change compFin F E v u.1 = _
      rw [hu]; rfl
    rw [absEv_apply, e]
    exact (GlobalTheory.SWAbsGrowth.absNorm_le_sq hσ v _).trans (pow_le_pow_left' ((absFin_le_normFin F v _ i j).trans
      (le_htOf (normFin F v) (bc (compFin F E v) x))) 2)

theorem exists_scale {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {s : ℝ} (hs : 0 < s) :
    ∃ u : (AF F ⊗[F] E)ˣ, u.1 = algebraMap (AF F) (AF F ⊗[F] E) (GlobalTheory.TorusTheta.infScale F s) ∧
      (absE F E u : ℝ) = (s ^ 2) ^ Fintype.card (InfinitePlace F) := by
  have h1 : GlobalTheory.TorusTheta.infScale F s * GlobalTheory.TorusTheta.infScale F s⁻¹ = 1 := by
    refine Prod.ext ?_ (mul_one _)
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hs.ne', map_one, map_one]
  let v : (AF F)ˣ := ⟨_, _, h1, (mul_comm _ _).trans h1⟩
  refine ⟨Units.map (algebraMap (AF F) (AF F ⊗[F] E) : AF F →* AF F ⊗[F] E) v, rfl, ?_⟩
  set u := Units.map (algebraMap (AF F) (AF F ⊗[F] E) : AF F →* AF F ⊗[F] E) v with hu
  have hf : ∀ p, GlobalTheory.Doubling.absEv F E p (unitFin F E p u) = 1 := fun p => by
    have : unitFin F E p u = 1 := Units.ext (by
      change compFin F E p (algebraMap (AF F) (AF F ⊗[F] E) (GlobalTheory.TorusTheta.infScale F s)) = 1
      rw [Algebra.TensorProduct.algebraMap_apply]
      change (evFin F p (GlobalTheory.TorusTheta.infScale F s)) ⊗ₜ[F] (1 : E) = 1
      rw [show evFin F p (GlobalTheory.TorusTheta.infScale F s) = 1 from map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F p)]
      rfl)
    rw [this, map_one]
  have hi : ∀ w, GlobalTheory.Doubling.absEw F E w (unitInf F E w u) = s.toNNReal ^ 2 := fun w => by
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    rw [absEw_eq_sq hσ τ]
    have e : infEmb τ (unitInf F E w u).1 = (s : ℂ) := GlobalTheory.TorusMat.piInf_infScale hσ τ s
    rw [e]
    congr 1
    exact NNReal.eq (by simp [abs_of_pos hs, Real.coe_toNNReal _ hs.le])
  rw [absE_apply, finprod_eq_one_of_forall_eq_one hf, mul_one, Finset.prod_congr rfl fun w _ => hi w]
  rw [Finset.prod_const, Finset.card_univ, NNReal.coe_pow, NNReal.coe_pow, Real.coe_toNNReal _ hs.le]

theorem exists_gl_col {n : ℕ} {x : Fin n → E} (hx : x ≠ 0) :
    ∃ (M : GL (Fin n) E) (k : Fin n), ∀ j, M.1 j k = x j := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  have hd : (Matrix.updateCol (1 : Matrix (Fin n) (Fin n) E) k x).det = x k := by
    rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hd.symm ▸ hk), k, fun j => ?_⟩
  change Matrix.updateCol (1 : Matrix (Fin n) (Fin n) E) k x j k = x j
  simp

theorem exists_scale_le {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) (i₀ : Fin r) (h0 : i₀.val = 0) :
    ∃ H : ℝ≥0, 1 ≤ H ∧ ∀ p ∈ minParOne σ J X, ∀ t : Fin r → ℝ, (∀ i, 0 < t i) → ∀ a, IsTorusElt σ J X Y t a →
      ∀ γ ∈ ratPts σ J, ((t i₀ ^ 2) ^ Fintype.card (InfinitePlace F) : ℝ) ≤ ((H * height σ J (γ * p * a) : ℝ≥0) : ℝ) ^ 2 := by
  set x : Fin n → E := fun j => X j i₀ with hxdef
  have hx : x ≠ 0 := by
    intro e
    have h1 := congrFun (congrFun hW.xy i₀) i₀
    have hrow : ∀ j, cT (σ : E →+* E) X i₀ j = 0 := fun j => by
      change σ (X j i₀) = 0
      rw [show X j i₀ = 0 from congrFun e j, map_zero]
    rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_zero fun j _ => by rw [hrow j, zero_mul],
      Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  obtain ⟨M, k, hM⟩ := exists_gl_col hx
  refine ⟨heightGL F (bc (inclR (F := F) (AF F)) M), one_le_heightGL F _, ?_⟩
  rintro p ⟨B, hB, hpB, hu⟩ t ht a ha γ hγ
  obtain ⟨s, hs1, hs2⟩ := exists_scale (F := F) (E := E) hσ (ht i₀)
  obtain ⟨b, hb1, hb2⟩ := hu i₀
  obtain ⟨γ₀, rfl⟩ : ∃ γ₀, ratEmb σ J γ₀ = γ := by
    have : γ ∈ (ratEmb σ J).range := (range_ratEmb σ J).symm ▸ hγ
    exact this
  let ξ : Fin n → AF F ⊗[F] E := fun j => inclR (F := F) (AF F) (x j)
  have hl' : ∀ l, l ≠ i₀ → B l i₀ = 0 := fun l hl => hB (show id i₀ < id l from Fin.lt_def.2 (by
    have : l.val ≠ i₀.val := fun e => hl (Fin.ext e)
    simp only [id]; omega))
  have hP : (matHom _ σ J p).1 *ᵥ ξ = b.1 • ξ := funext fun j => by
    have h1 := congrFun (congrFun hpB j) i₀
    rw [Matrix.mul_apply (M := adMat F X), Finset.sum_eq_single i₀ (fun l _ hl => by
      rw [hl' l hl, mul_zero]) (by simp), hb1] at h1
    exact h1.trans (mul_comm _ _)
  have hA : (matHom _ σ J a).1 *ᵥ ξ = s.1 • ξ := funext fun j => by
    have h1 := congrFun (congrFun (GlobalTheory.TorusMat.isTorusElt_mat F E σ hσ n J r X Y t ht a ha).1 j) i₀
    rw [Matrix.mul_diagonal, ← hs1] at h1
    exact h1.trans (mul_comm _ _)
  have hG : (matHom _ σ J (ratEmb σ J γ₀)).1 *ᵥ ξ = fun j => inclR (F := F) (AF F) ((γ₀.1.1 *ᵥ x) j) := funext fun j =>
    (RingHom.map_mulVec (inclR (F := F) (AF F)) γ₀.1.1 x j).symm
  have hv : γ₀.1.1 *ᵥ x ≠ 0 := fun e => hx (by
    have := congrArg (fun y => ((γ₀.1)⁻¹).1 *ᵥ y) e
    simpa [Matrix.mulVec_mulVec] using this)
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  let e : Eˣ := Units.mk0 _ hi
  let u : (AF F ⊗[F] E)ˣ := s * b * Units.map (inclR (F := F) (AF F)).toMonoidHom e
  have hz : u.1 = (matHom _ σ J (ratEmb σ J γ₀ * p * a) * bc (inclR (F := F) (AF F)) M).1 i k := by
    have h1 : (matHom _ σ J (ratEmb σ J γ₀ * p * a) * bc (inclR (F := F) (AF F)) M).1 i k =
        ((matHom _ σ J (ratEmb σ J γ₀ * p * a)).1 *ᵥ ξ) i := by
      rw [Units.val_mul, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => congrArg _ ?_
      exact congrArg (inclR (F := F) (AF F)) (hM j)
    have h2 : (matHom _ σ J (ratEmb σ J γ₀ * p * a)).1 *ᵥ ξ =
        (s.1 * b.1) • fun j => inclR (F := F) (AF F) ((γ₀.1.1 *ᵥ x) j) := by
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA,
        Matrix.mulVec_smul, hP, Matrix.mulVec_smul, Matrix.mulVec_smul, hG, smul_smul]
    rw [h1, h2]
    rfl
  have habs : (absE F E u : ℝ) = (t i₀ ^ 2) ^ Fintype.card (InfinitePlace F) := by
    rw [map_mul, map_mul, absE_inclR, hb2, mul_one, mul_one, hs2]
  rw [← habs]
  have h2 := absE_entry_le hσ _ u i k hz
  have h3 := heightGL_mul_le F (matHom _ σ J (ratEmb σ J γ₀ * p * a)) (bc (inclR (F := F) (AF F)) M)
  have h4 : absE F E u ≤ (heightGL F (bc (inclR (F := F) (AF F)) M) * height σ J (ratEmb σ J γ₀ * p * a)) ^ 2 :=
    h2.trans (pow_le_pow_left' (h3.trans_eq (mul_comm _ _)) 2)
  exact_mod_cast h4

theorem cone_up {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ} (ht : t ∈ cone r c) (i₀ : Fin r) (h0 : i₀.val = 0)
    (m : ℕ) (hm : m < r) : t ⟨m, hm⟩ ≤ max 1 c⁻¹ ^ m * t i₀ := by
  induction m with
  | zero =>
    have : (⟨0, hm⟩ : Fin r) = i₀ := Fin.ext h0.symm
    rw [this]; simp
  | succ m ih =>
    have h1 := ht.2.1 ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl
    have h2 := ih (by omega)
    have h3 : t ⟨m + 1, hm⟩ ≤ c⁻¹ * t ⟨m, by omega⟩ := by
      rw [inv_mul_eq_div, le_div_iff₀ hc]; linarith
    have h4 := ht.1 ⟨m, by omega⟩
    calc t ⟨m + 1, hm⟩ ≤ c⁻¹ * t ⟨m, by omega⟩ := h3
      _ ≤ max 1 c⁻¹ * t ⟨m, by omega⟩ := by gcongr; exact le_max_right _ _
      _ ≤ max 1 c⁻¹ * (max 1 c⁻¹ ^ m * t i₀) := by gcongr
      _ = _ := by ring

theorem exists_prod_le {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ minParOne σ J X, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a →
      ∀ γ ∈ ratPts σ J, 1 + ∏ i, t i ≤ B * (height σ J (γ * p * a) : ℝ) ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨2, by norm_num, fun p _ t _ a _ γ _ => by norm_num⟩
  let i₀ : Fin r := ⟨0, hr⟩
  obtain ⟨H, hH1, hH⟩ := exists_scale_le (F := F) hσ hW i₀ rfl
  set L : ℝ := max 1 c⁻¹ ^ r with hL
  have hL1 : 1 ≤ L := one_le_pow₀ (le_max_left _ _)
  refine ⟨2 * (L * H) ^ r, by positivity, fun p hp t ht a ha γ hγ => ?_⟩
  set Q : ℝ := (height σ J (γ * p * a) : ℝ) with hQ
  have hQ1 : 1 ≤ Q := by exact_mod_cast one_le_height σ J _
  have hH1' : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  have hHQ : 1 ≤ (H : ℝ) * Q := one_le_mul_of_one_le_of_one_le hH1' hQ1
  have hd : Fintype.card (InfinitePlace F) ≠ 0 := Fintype.card_ne_zero
  have h0 : t i₀ ≤ H * Q := by
    by_contra hlt
    push Not at hlt
    have h1 := hH p hp t ht.1 a ha γ hγ
    rw [NNReal.coe_mul] at h1
    have h2 : ((H : ℝ) * Q) ^ 2 < t i₀ ^ 2 := pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
    have h3 : 1 ≤ t i₀ ^ 2 := one_le_pow₀ (hHQ.trans hlt.le)
    have h4 : t i₀ ^ 2 ≤ (t i₀ ^ 2) ^ Fintype.card (InfinitePlace F) := le_self_pow₀ h3 hd
    exact absurd (h4.trans h1) (not_le.2 h2)
  have hb : ∀ i, t i ≤ L * (H * Q) := fun i => by
    have h1 := cone_up hc ht i₀ rfl i.val i.2
    have h2 : max 1 c⁻¹ ^ i.val ≤ L := pow_le_pow_right₀ (le_max_left _ _) i.2.le
    calc t i ≤ max 1 c⁻¹ ^ i.val * t i₀ := h1
      _ ≤ L * (H * Q) := mul_le_mul h2 h0 (ht.1 i₀).le (by positivity)
  have hprod : ∏ i, t i ≤ (L * (H * Q)) ^ r := by
    have := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin r))) (fun i _ => (ht.1 i).le) fun i _ => hb i
    simpa using this
  have h5 : 1 ≤ (L * (H * Q)) ^ r := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hL1 hHQ)
  calc 1 + ∏ i, t i ≤ (L * (H * Q)) ^ r + (L * (H * Q)) ^ r := add_le_add h5 hprod
    _ = 2 * (L * H) ^ r * Q ^ r := by rw [mul_pow, mul_pow, mul_pow]; ring

set_option maxHeartbeats 1000000 in

theorem height_le_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ), IsCompact (K : Set (GAd σ J)) → IsCompact Ω → Ω ⊆ minParOne σ J X → 0 < c → ∃ (C : ℝ≥0) (A : ℕ), ∀ g ∈ siegelSet σ J X Y Ω c K, ∀ γ ∈ ratPts σ J, height σ J g ≤ C * height σ J (γ * g) ^ A := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW K Ω c hK hΩ hΩ' hc
  have hcont : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  obtain ⟨R₁, hR₁⟩ := (hΩ.image hcont).bddAbove
  obtain ⟨R₂, hR₂⟩ := (hK.image hcont).bddAbove
  obtain ⟨B, hB0, hB⟩ := exists_prod_le hσ hW hc
  have hc' : 0 < min 1 c ^ r := pow_pos (lt_min one_pos hc) _
  obtain ⟨Ch, Ah, hCh⟩ := @GlobalTheory.TorusHeight.height_torus_le F E _ _ _ _ _ σ hσ n J r X Y _ hc'
  have hR₂0 : 0 ≤ R₂ := by
    have h1 := hR₂ ⟨1, one_mem K, rfl⟩
    exact (NNReal.coe_nonneg _).trans h1
  set R₁' := max R₁ 0 with hR₁'
  set Ch' := max Ch 0 with hCh'
  have hR₁0 : 0 ≤ R₁' := le_max_right _ _
  have hCh0 : 0 ≤ Ch' := le_max_right _ _
  have hC0 : 0 ≤ R₁' * Ch' * B ^ Ah * R₂ ^ (r * Ah) * R₂ := by positivity
  refine ⟨(R₁' * Ch' * B ^ Ah * R₂ ^ (r * Ah) * R₂).toNNReal, r * Ah, ?_⟩
  rintro _ ⟨p, hp, t, ht, a, ha, k, hk, rfl⟩ γ hγ
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ hC0]
  set S : ℝ := (height σ J (γ * (p * a * k)) : ℝ) with hS
  have hS0 : 0 ≤ S := NNReal.coe_nonneg _
  have h1 : (height σ J a : ℝ) ≤ Ch * (1 + ∏ i, t i) ^ Ah :=
    hCh t (GlobalTheory.SiegelHt.cone_low hc ht) a ha.1
      (@GlobalTheory.SiegelTorusMat.archMat_torus F E _ _ _ _ _ σ hσ n J hJ r X Y hW t
        (fun i => hc'.trans_le (GlobalTheory.SiegelHt.cone_low hc ht i)) a ha)
  have hprod0 : 0 ≤ 1 + ∏ i, t i := add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => (ht.1 i).le)
  have hpa : γ * p * a = γ * (p * a * k) * k⁻¹ := by group
  have hkb : (height σ J k : ℝ) ≤ R₂ := hR₂ ⟨k, hk, rfl⟩
  have hkib : (height σ J k⁻¹ : ℝ) ≤ R₂ := by rw [height_inv]; exact hkb
  have hpb : (height σ J p : ℝ) ≤ R₁' := (hR₁ ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  have hQ : (height σ J (γ * p * a) : ℝ) ≤ S * R₂ := by
    rw [hpa]
    calc (height σ J (γ * (p * a * k) * k⁻¹) : ℝ) ≤ ((height σ J (γ * (p * a * k)) * height σ J k⁻¹ : ℝ≥0) : ℝ) := by
          exact_mod_cast height_mul_le σ J _ _
      _ ≤ S * R₂ := by rw [NNReal.coe_mul]; exact mul_le_mul_of_nonneg_left hkib hS0
  have h2 := hB p (hΩ' hp) t ht a ha γ hγ
  have h3 : 1 + ∏ i, t i ≤ B * (S * R₂) ^ r := h2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hQ r) hB0)
  have h4 : (height σ J a : ℝ) ≤ Ch' * (B * (S * R₂) ^ r) ^ Ah :=
    h1.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hprod0 h3 _) (pow_nonneg hprod0 _) hCh0)
  have h5 : (height σ J (p * a * k) : ℝ) ≤ (height σ J p : ℝ) * height σ J a * height σ J k := by
    exact_mod_cast (height_mul_le σ J _ _).trans (mul_le_mul' (height_mul_le σ J _ _) le_rfl)
  calc (height σ J (p * a * k) : ℝ) ≤ (height σ J p : ℝ) * height σ J a * height σ J k := h5
    _ ≤ R₁' * (Ch' * (B * (S * R₂) ^ r) ^ Ah) * R₂ :=
        mul_le_mul (mul_le_mul hpb h4 (NNReal.coe_nonneg _) hR₁0) hkb (NNReal.coe_nonneg _)
          (mul_nonneg hR₁0 ((NNReal.coe_nonneg _).trans h4))
    _ = R₁' * Ch' * B ^ Ah * R₂ ^ (r * Ah) * R₂ * S ^ (r * Ah) := by
      rw [mul_pow B, ← pow_mul, mul_pow S]; ring

end GlobalTheory.CompanionTheory.SiegelHt

end
