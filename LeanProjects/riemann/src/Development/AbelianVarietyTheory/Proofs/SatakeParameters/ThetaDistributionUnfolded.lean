import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.TensorBasis
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ProdFinEqProdCastLE

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KerWt

open Formalism Formalism.L2 Formalism.L2.Ker Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H

section Wt

open MvPolynomial Formalism.L2.DIV

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b n : ℕ}

theorem prod_castLE {M : Type} [CommMonoid M] (h : a ≤ b) (f : Fin b → M) (h0 : ∀ r : Fin b, a ≤ r.1 → f r = 1) :
    ∏ r, f r = ∏ r : Fin a, f (Fin.castLE h r) := by
  first
  | exact @_root_.GlobalTheory.ProdFinCastLE.prod_fin_eq_prod_castLE
  | exact _root_.GlobalTheory.ProdFinCastLE.prod_fin_eq_prod_castLE
  | (apply _root_.GlobalTheory.ProdFinCastLE.prod_fin_eq_prod_castLE <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProdFinCastLE.prod_fin_eq_prod_castLE <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProdFinCastLE.prod_fin_eq_prod_castLE <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProdFinCastLE.prod_fin_eq_prod_castLE ..)

theorem sum_castLE {M : Type} [AddCommMonoid M] (h : a ≤ b) (f : Fin b → M) (h0 : ∀ r : Fin b, a ≤ r.1 → f r = 0) :
    ∑ r, f r = ∑ r : Fin a, f (Fin.castLE h r) := by
  have e : ∑ r : Fin a, f (Fin.castLE h r) = ∑ r ∈ Finset.univ.map (Fin.castLEEmb h), f r := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine (Finset.sum_subset (Finset.subset_univ _) fun r _ hr => h0 r ?_).symm
  by_contra hlt
  exact hr (Finset.mem_map.2 ⟨⟨r.1, not_le.1 hlt⟩, Finset.mem_univ _, rfl⟩)

def liftL (φ : Pol K ι b →ₐ[K] Pol K ι b) :
    MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K →ₐ[K] MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K :=
  aeval (Sum.elim (fun v => rename Sum.inl (φ (X v))) fun w => X (Sum.inr w))

theorem liftL_inl (φ : Pol K ι b →ₐ[K] Pol K ι b) (f : Pol K ι b) :
    liftL (a := a) φ (rename Sum.inl f) = rename Sum.inl (φ f) := by
  have h : ((liftL (a := a) φ).comp (rename Sum.inl)) = (rename Sum.inl).comp φ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftL]
  exact DFunLike.congr_fun h f

theorem liftL_inr (φ : Pol K ι b →ₐ[K] Pol K ι b) (g : MvPolynomial (DVar ι a b) K) :
    liftL (a := a) φ (rename Sum.inr g) = rename Sum.inr g := by
  have h : ((liftL (a := a) φ).comp (rename Sum.inr)) = rename Sum.inr := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftL]
  exact DFunLike.congr_fun h g

theorem jetLin_inl_mul (J : (DVar ι a b →₀ ℕ) → K) (f : Pol K ι b) (q : DVar ι a b →₀ ℕ) (c : K) :
    jetLin J (rename Sum.inl f * rename Sum.inr (monomial q c)) = (c * J q) • f := by
  induction f using MvPolynomial.induction_on' with
  | monomial p d =>
    rw [rename_monomial, rename_monomial, monomial_mul, jetLin_mixed, smul_monomial, smul_eq_mul]
    congr 1
    ring
  | add f g hf hg => rw [map_add, add_mul, map_add, hf, hg, smul_add]

theorem jetLin_liftL (J : (DVar ι a b →₀ ℕ) → K) (φ : Pol K ι b →ₐ[K] Pol K ι b)
    (R : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) : jetLin J (liftL φ R) = φ (jetLin J R) := by
  induction R using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [split_mono m]
    set p := m.comapDomain Sum.inl Sum.inl_injective.injOn
    set q := m.comapDomain Sum.inr Sum.inr_injective.injOn
    have h : (monomial (p.mapDomain Sum.inl + q.mapDomain Sum.inr) c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) =
        rename Sum.inl (monomial p 1) * rename Sum.inr (monomial q c) := by
      rw [rename_monomial, rename_monomial, monomial_mul, one_mul]
    rw [h, map_mul, liftL_inl, liftL_inr, jetLin_inl_mul, jetLin_inl_mul, map_smul]
  | add f g hf hg => rw [map_add, map_add, map_add, map_add, hf, hg]

def resB (h : a ≤ b) (β : ι → Matrix (Fin b) (Fin b) K) : ι → Matrix (Fin a) (Fin a) K :=
  fun τ r s => β τ (Fin.castLE h r) (Fin.castLE h s)

theorem isBor_resB (h : a ≤ b) {β : ι → Matrix (Fin b) (Fin b) K} (hβ : IsBor β) : IsBor (resB h β) :=
  fun τ => ⟨fun _ _ hrs => (hβ τ).1 _ _ hrs, fun _ => (hβ τ).2 _⟩

theorem liftL_subD (h : a ≤ b) {β : ι → Matrix (Fin b) (Fin b) K} (hβ : IsBor β) (Q : Pol K ι a) :
    liftL (colSub β) (subD K ι a b Q) = subD K ι a b (colSub (resB h β) Q) := by
  have e : (liftL (colSub β)).comp (subD K ι a b) = (subD K ι a b).comp (colSub (resB h β)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, α, s⟩
    have hs : s.1 < b := lt_of_lt_of_le s.2 h
    simp only [AlgHom.comp_apply, subD, colSub, aeval_X, dif_pos hs, map_sum, map_mul, liftL, Sum.elim_inl, Sum.elim_inr, rename_X,
      algHom_C, algebraMap_eq]
    have h1 : ∀ r : Fin a, (r : ℕ) < b := fun r => lt_of_lt_of_le r.2 h
    simp only [dif_pos (h1 _)]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [sum_castLE h]
    · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun β' _ => ?_
      simp only [resB]
      rw [mul_assoc]
      rfl
    · intro r hr
      refine Finset.sum_eq_zero fun β' _ => ?_
      rw [(hβ τ).1 r ⟨s.1, hs⟩ (Fin.lt_def.2 (lt_of_lt_of_le s.2 hr)), C_0, zero_mul, zero_mul]
  exact DFunLike.congr_fun e Q

theorem jetMap_zero (J : (DVar ι a b →₀ ℕ) → K) (Q : Pol K ι a) : jetMap J (fun _ => 0) Q = jetLin J (subD K ι a b Q) := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_zero, Finset.prod_const_one, mul_one, AlgHom.toLinearMap_apply]

theorem jet_weight : JetWt := by
  intro K _ ι _ a b h J ν Q hQ β hβ
  rw [jetMap_zero, ← jetLin_liftL, liftL_subD h hβ, hQ _ (isBor_resB h hβ), map_smul, map_smul]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [prod_castLE h]
  · refine Finset.prod_congr rfl fun r _ => ?_
    simp only [resB, extNu]
    rw [dif_pos (show ((Fin.castLE h r : Fin b) : ℕ) < a from r.2)]
    rfl
  · intro r hr
    simp only [extNu]
    rw [dif_neg (not_lt.2 hr), pow_zero]

end Wt

section BaseCh

open MvPolynomial Formalism.L2.DIV

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {a b : ℕ}

theorem map_jetLin (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (R : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    map σ (jetLin J R) = jetLin (fun m => σ (J m)) (map σ R) := by
  induction R using MvPolynomial.induction_on' with
  | monomial m c => rw [jetLin_monomial, map_monomial, map_monomial, jetLin_monomial, map_mul]
  | add f g hf hg => simp only [map_add, hf, hg]

theorem map_subD (σ : K →+* L) (P : Pol K ι a) : map σ (subD K ι a b P) = subD L ι a b (map σ P) := by
  have e : (map σ).comp (subD K ι a b).toRingHom = ((subD L ι a b).toRingHom).comp (map σ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [subD]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, subD, aeval_X, map_X]
      split_ifs <;> simp
  exact RingHom.congr_fun e P

theorem map_frDet (σ : K →+* L) (τ : ι) : map σ (frDet K a τ) = frDet L a τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp

theorem map_jetMap (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    map σ (jetMap J n P) = jetMap (fun m => σ (J m)) n (map σ P) := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  rw [map_jetLin, map_subD, map_mul, map_prod]
  simp only [map_pow, map_frDet]

theorem jetLin_scal (c : K) (J : (DVar ι a b →₀ ℕ) → K) : jetLin (fun m => c * J m) = c • jetLin J := by
  apply (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext
  intro m
  rw [LinearMap.smul_apply]
  simp only [coe_basisMonomials, jetLin_monomial, one_mul, smul_monomial, smul_eq_mul]

theorem jetMap_scal (c : K) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap (fun m => c * J m) n P = c • jetMap J n P := by
  unfold jetMap
  rw [jetLin_scal]
  rfl

theorem jetMap_shift (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap J n P = jetMap J (fun _ => 0) (P * ∏ τ, frDet K a τ ^ n τ) := by
  rw [jetMap_zero]
  rfl

end BaseCh

section UnfG

open MvPolynomial Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {a b : ℕ} {Y Y' : Type}

theorem eval_frDet (v : ι × Fin a × Fin a → ℂ) (τ : ι) : eval v (frDet ℂ a τ) = (Matrix.of fun α k => v (τ, α, k)).det := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α k
  simp

theorem frPolyG_inj (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ)
    (hr : ∀ f : ι → Matrix (Fin a) (Fin a) ℂ, (∀ τ, (f τ).det ≠ 0) → ∃ y, fr y = f) : Function.Injective (frPolyG fr) := by
  rw [injective_iff_map_eq_zero]
  intro Q hQ
  have h0 : Q * ∏ τ, frDet ℂ a τ = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_mul, map_zero, map_prod]
    simp only [eval_frDet]
    by_cases h : ∀ τ, (Matrix.of fun α k => v (τ, α, k) : Matrix (Fin a) (Fin a) ℂ).det ≠ 0
    · obtain ⟨y, hy⟩ := hr (fun τ => Matrix.of fun α k => v (τ, α, k)) h
      have h1 := congrFun hQ y
      have h2 : eval v Q = 0 := by
        have : frPolyG fr Q y = eval v Q := by
          show eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) Q = _
          rw [hy]; rfl
        rw [← this, h1]; rfl
      rw [h2, zero_mul]
    · push Not at h
      obtain ⟨τ, hτ⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  rcases mul_eq_zero.1 h0 with h | h
  · exact h
  · exfalso
    have h1 := congrArg (eval fun k : ι × Fin a × Fin a => if k.2.1 = k.2.2 then (1 : ℂ) else 0) h
    rw [map_prod, map_zero] at h1
    simp only [eval_frDet] at h1
    have h2 : ∀ τ : ι, (Matrix.of fun α k : Fin a => (if α = k then (1 : ℂ) else 0)).det = 1 := by
      intro τ
      have : (Matrix.of fun α k : Fin a => (if α = k then (1 : ℂ) else 0)) = 1 := by
        ext α k; simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    exact one_ne_zero ((Finset.prod_eq_one fun τ _ => h2 τ).symm.trans h1)

theorem frInvG_spec {fr : Y → ι → Matrix (Fin a) (Fin a) ℂ} (hinj : Function.Injective (frPolyG fr)) :
    frInvG fr ∘ₗ frPolyG fr = LinearMap.id :=
  Classical.epsilon_spec (p := fun g => g ∘ₗ frPolyG fr = LinearMap.id)
    (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 hinj))

theorem unfG_frPolyG {fr : Y → ι → Matrix (Fin a) (Fin a) ℂ} (hinj : Function.Injective (frPolyG fr)) (fr' : Y' → ι → Matrix (Fin b) (Fin b) ℂ)
    (cD : ι → ℂ) (Θ : VCx ι a b → ℂ) (Q : Pol ℂ ι a) :
    unfG fr fr' cD Θ (frPolyG fr Q) = frPolyG fr' (jetMap (jetC cD Θ) (fun _ => 0) Q) := by
  have h : frInvG fr (frPolyG fr Q) = Q := LinearMap.congr_fun (frInvG_spec hinj) Q
  unfold unfG
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h]

theorem mulFun_evG {K : Type} [Field K] {fr : Y → ι → Matrix (Fin a) (Fin a) ℂ} (hdet : ∀ y τ, (fr y τ).det ≠ 0) (σ : K →+* ℂ) (sh sS : ι → ℤ) (n : ι → ℕ)
    (hn : ∀ τ, sh τ + sS τ = n τ) (P : Pol K ι a) :
    mulFun (fun y => ∏ τ, (fr y τ).det ^ sS τ) (evG fr sh σ P) = frPolyG fr (map σ P * ∏ τ, frDet ℂ a τ ^ n τ) := by
  funext y
  show (∏ τ, (fr y τ).det ^ sS τ) * ((∏ τ, (fr y τ).det ^ sh τ) * eval₂ σ (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) P) =
    eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (map σ P * ∏ τ, frDet ℂ a τ ^ n τ)
  rw [map_mul, eval_map, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, eval_frDet, ← zpow_add₀ (hdet y τ), add_comm, hn, zpow_natCast]
  rfl

theorem unfolding_gl_eval : UnfGEv := by
  intro K _ ι _ a b Y Y' fr fr' hinj hdet σ cD Θ J z hJ sh sS sD n hn P
  have h1 : mulFun (fun y => ∏ τ, (fr y τ).det ^ sS τ) (evG fr sh σ P) = frPolyG fr (map σ P * ∏ τ, frDet ℂ a τ ^ n τ) := by
    funext y
    show (∏ τ, (fr y τ).det ^ sS τ) * ((∏ τ, (fr y τ).det ^ sh τ) * eval₂ σ (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) P) =
      eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (map σ P * ∏ τ, frDet ℂ a τ ^ n τ)
    rw [map_mul, eval_map, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, eval_frDet, ← zpow_add₀ (hdet y τ), add_comm, hn, zpow_natCast]
    rfl
  rw [h1, unfG_frPolyG hinj, ← jetMap_shift]
  funext y'
  show (∏ τ, (fr' y' τ).det ^ (-sD τ)) * eval₂ σ (fun k : ι × Fin b × Fin b => fr' y' k.1 k.2.1 k.2.2) (jetMap J n P) =
    z * ((∏ τ, (fr' y' τ).det ^ sD τ)⁻¹ * eval (fun k : ι × Fin b × Fin b => fr' y' k.1 k.2.1 k.2.2) (jetMap (jetC cD Θ) n (map σ P)))
  rw [← eval_map, map_jetMap, funext hJ, jetMap_scal, smul_eval, ← Finset.prod_inv_distrib]
  simp only [zpow_neg]
  ring

theorem frPolyG_colSub (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) (β : ι → Matrix (Fin a) (Fin a) ℂ) (Q : Pol ℂ ι a) (y : Y) :
    frPolyG fr (colSub β Q) y = eval (fun k : ι × Fin a × Fin a => (fr y k.1 * β k.1) k.2.1 k.2.2) Q := by
  have e : (eval fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2).comp (colSub β).toRingHom =
      eval fun k : ι × Fin a × Fin a => (fr y k.1 * β k.1) k.2.1 k.2.2 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [colSub]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, colSub, aeval_X, map_sum, map_mul, eval_C, eval_X,
        Matrix.mul_apply]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  exact RingHom.congr_fun e Q

theorem det_bor {β : ι → Matrix (Fin a) (Fin a) ℂ} (hβ : IsBor β) (τ : ι) : (β τ).det = ∏ r, β τ r r :=
  Matrix.det_of_isUpperTriangular fun r s h => (hβ τ).1 r s h

theorem bor_id {β : ι → Matrix (Fin a) (Fin a) ℂ} (hβ : IsBor β) (d : ι → ℂ) (lam : ι → Fin a → ℤ) (sS : ι → ℤ) (ν : ι → Fin a → ℕ)
    (hν : ∀ τ r, lam τ r + sS τ = ν τ r) :
    (∏ τ, (d τ * (β τ).det) ^ sS τ) * ∏ τ, ∏ r, β τ r r ^ lam τ r = (∏ τ, ∏ r, β τ r r ^ ν τ r) * ∏ τ, d τ ^ sS τ := by
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [mul_assoc, mul_comm]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [det_bor hβ, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [← zpow_add₀ ((hβ τ).2 r), add_comm, hν, zpow_natCast]

theorem sharp_vector_formula : SharpVIs := by
  intro ι _ a Y fr hr lam sS ν hν F
  have hdet : ∀ y τ, (fr y τ).det ≠ 0 := fun y => (hr (fr y)).1 ⟨y, rfl⟩
  have hinj : Function.Injective (frPolyG fr) := frPolyG_inj fr fun f hf => (hr f).2 hf
  have hP : ∀ y, (∏ τ, (fr y τ).det ^ sS τ) ≠ 0 := fun y => Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hdet y τ)
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    refine ⟨⟨fun y => (∏ τ, (fr y τ).det ^ sS τ)⁻¹ * frPolyG fr Q y, ⟨⟨Q * ∏ τ, frDet ℂ a τ ^ (-sS τ).toNat, fun τ => (sS τ).toNat, ?_⟩, ?_⟩, ?_⟩, Q, rfl⟩
    · intro y
      show (∏ τ, (fr y τ).det ^ sS τ)⁻¹ * eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) Q * ∏ τ, (fr y τ).det ^ (sS τ).toNat =
        eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (Q * ∏ τ, frDet ℂ a τ ^ (-sS τ).toNat)
      rw [map_mul, map_prod, mul_comm (∏ τ, (fr y τ).det ^ sS τ)⁻¹, mul_assoc, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_pow, eval_frDet, ← zpow_neg, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hdet y τ)]
      congr 1
      have := Int.toNat_sub_toNat_neg (sS τ)
      omega
    · intro y y₂ β hβ h2
      have e1 : frPolyG fr Q y₂ = (∏ τ, ∏ r, β τ r r ^ ν τ r) * frPolyG fr Q y := by
        have := frPolyG_colSub fr β Q y
        rw [hQ β hβ] at this
        show eval (fun k : ι × Fin a × Fin a => fr y₂ k.1 k.2.1 k.2.2) Q = _
        simp only [h2]
        rw [← this]
        simp
      have e2 := bor_id hβ (fun τ => (fr y τ).det) lam sS ν hν
      have e3 : (∏ τ, (fr y₂ τ).det ^ sS τ) = ∏ τ, ((fr y τ).det * (β τ).det) ^ sS τ :=
        Finset.prod_congr rfl fun τ _ => by rw [h2, Matrix.det_mul]
      show (∏ τ, (fr y₂ τ).det ^ sS τ)⁻¹ * frPolyG fr Q y₂ = _ * ((∏ τ, (fr y τ).det ^ sS τ)⁻¹ * frPolyG fr Q y)
      rw [e1, inv_mul_eq_iff_eq_mul₀ (hP y₂), e3, ← mul_assoc, ← mul_assoc, e2, mul_assoc (∏ τ, ∏ r, β τ r r ^ ν τ r), mul_assoc,
        mul_inv_cancel₀ (hP y), one_mul]
    · funext y
      show _ = (∏ τ, (fr y τ).det ^ sS τ) * ((∏ τ, (fr y τ).det ^ sS τ)⁻¹ * frPolyG fr Q y)
      rw [mul_inv_cancel_left₀ (hP y)]
  · rintro ⟨⟨f, ⟨-, hw⟩, hF⟩, Q, hQ⟩
    refine ⟨Q, fun β hβ => hinj ?_, hQ⟩
    funext y
    obtain ⟨y₂, h2⟩ := (hr fun τ => fr y τ * β τ).2 fun τ => by
      rw [Matrix.det_mul, det_bor hβ]
      exact mul_ne_zero (hdet y τ) (Finset.prod_ne_zero_iff.2 fun r _ => (hβ τ).2 r)
    have h2' : ∀ τ, fr y₂ τ = fr y τ * β τ := fun τ => congrFun h2 τ
    have e0 : ∀ y, frPolyG fr Q y = (∏ τ, (fr y τ).det ^ sS τ) * f y := fun y => by rw [← hQ, hF]; rfl
    have e1 : frPolyG fr (colSub β Q) y = frPolyG fr Q y₂ := by
      rw [frPolyG_colSub]
      show _ = eval (fun k : ι × Fin a × Fin a => fr y₂ k.1 k.2.1 k.2.2) Q
      simp only [h2']
    have e2 := bor_id hβ (fun τ => (fr y τ).det) lam sS ν hν
    have e3 : (∏ τ, (fr y₂ τ).det ^ sS τ) = ∏ τ, ((fr y τ).det * (β τ).det) ^ sS τ :=
      Finset.prod_congr rfl fun τ _ => by rw [h2', Matrix.det_mul]
    rw [e1, map_smul, Pi.smul_apply, smul_eq_mul, e0, e0, hw y y₂ β hβ h2', e3, ← mul_assoc, e2, mul_assoc]

end UnfG

section VVWt

open MvPolynomial Formalism.L2.DIV Formalism.GradedWeylDivisibility

variable {K : Type} [Field K] {r n : ℕ}

def colSub1 (β : Matrix (Fin n) (Fin n) K) : MvPolynomial (Fin r × Fin n) K →ₐ[K] MvPolynomial (Fin r × Fin n) K :=
  aeval fun v => ∑ w : Fin n, C (β w v.2) * X (v.1, w)

def colSc (t : Fin n) (d : K) : MvPolynomial (Fin r × Fin n) K →ₐ[K] MvPolynomial (Fin r × Fin n) K :=
  aeval fun v => C (if v.2 = t then d else 1) * X v

def colAddS (t : Fin n) (S : Finset (Fin n)) (c : Fin n → K) : MvPolynomial (Fin r × Fin n) K →ₐ[K] MvPolynomial (Fin r × Fin n) K :=
  aeval fun v => if v.2 = t then X v + ∑ l ∈ S, C (c l) * X (v.1, l) else X v

theorem colAdd_inv {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : F ∈ dualWeyl K r n ν) (l j : Fin n) (h : l < j) (c : K) :
    colAdd K l j c F = F := by
  have hk := (lsat_mem_dualWeyl.1 hF).2 l j h
  have h1 := congrArg (fun g => g F) (lsat_spec_colAddGen (r := r) l j c)
  have h2 := congrArg (fun g => g F) (lsat_spec_rename (r := r) (n := n) c)
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply] at h1 h2
  rw [← h1, hk, h2]

theorem colAddS_insert (t l : Fin n) (hl : l ≠ t) (S : Finset (Fin n)) (hS : l ∉ S) (c : Fin n → K) :
    (colAddS (r := r) t (insert l S) c) = (colAddS t S c).comp (colAdd K l t (c l)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [colAddS, colAdd, AlgHom.comp_apply, aeval_X]
  split_ifs with h
  · rw [map_add, map_mul, aeval_X, aeval_X, algHom_C, if_pos h, if_neg hl, Finset.sum_insert hS]
    simp only [algebraMap_eq]
    ring
  · rw [aeval_X, if_neg h]

theorem colAddS_inv {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : F ∈ dualWeyl K r n ν) (t : Fin n) (c : Fin n → K)
    (S : Finset (Fin n)) (hS : ∀ l ∈ S, l < t) : colAddS t S c F = F := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have : colAddS (r := r) t ∅ c = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [colAddS]
    rw [this]; rfl
  | insert l S hl ih =>
    rw [colAddS_insert t l (hS l (Finset.mem_insert_self _ _)).ne S hl c, AlgHom.comp_apply,
      colAdd_inv hF l t (hS l (Finset.mem_insert_self _ _)), ih fun x hx => hS x (Finset.mem_insert_of_mem hx)]

theorem colSc_monomial (t : Fin n) (d : K) (m : Fin r × Fin n →₀ ℕ) (c : K) :
    colSc t d (monomial m c) = (d ^ (∑ a : Fin r, m (a, t))) • monomial m c := by
  classical
  have h1 : colSc t d (monomial m c) = C c * m.prod fun v k => (C (if v.2 = t then d else 1) * X v : MvPolynomial (Fin r × Fin n) K) ^ k := by
    rw [colSc, aeval_monomial]; rfl
  have h2 : (m.prod fun v k => (C (if v.2 = t then d else 1) * X v : MvPolynomial (Fin r × Fin n) K) ^ k) =
      C (m.prod fun v k => (if v.2 = t then d else 1) ^ k) * m.prod fun v k => X v ^ k := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, C_pow]
  have h3 : (m.prod fun v k => (if v.2 = t then d else (1 : K)) ^ k) = d ^ (∑ a : Fin r, m (a, t)) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_eq_single t]
    · simp
    · intro s _ hs
      simp [hs]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, h2, h3, monomial_eq, smul_eq_C_mul]
  ring

theorem colSc_hom {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : IsWeightedHomogeneous (colW r n) F ν) (t : Fin n) (d : K) :
    colSc t d F = (d ^ ν t) • F := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [colSc_monomial]
  congr 2
  have h := hF (mem_support_iff.1 hm)
  have h2 := congrFun h t
  rw [← h2, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ (colW r n i)), Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single t]
  · simp [colW]
  · intro s _ hs
    simp [colW, hs]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_split (t : Fin n) {M : Type} [AddCommMonoid M] (f : Fin n → M) (h : ∀ w, t < w → f w = 0) :
    ∑ w, f w = f t + ∑ l ∈ Finset.univ.filter (· < t), f l := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < t), add_comm]
  congr 1
  rw [Finset.sum_eq_single t]
  · intro w hw hne
    have h1 : ¬ w < t := (Finset.mem_filter.1 hw).2
    exact h w (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hne))
  · intro h1
    exact (h1 (by simp)).elim

def colOne (β : Matrix (Fin n) (Fin n) K) (t : Fin n) : MvPolynomial (Fin r × Fin n) K →ₐ[K] MvPolynomial (Fin r × Fin n) K :=
  aeval fun v => if v.2 = t then ∑ w : Fin n, C (β w t) * X (v.1, w) else X v

theorem colOne_eq (β : Matrix (Fin n) (Fin n) K) (hβ : ∀ w s, s < w → β w s = 0) (t : Fin n) :
    colOne (r := r) β t = (colSc t (β t t)).comp (colAddS t (Finset.univ.filter (· < t)) fun l => β l t) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [colOne, colSc, colAddS, AlgHom.comp_apply, aeval_X]
  split_ifs with h
  · rw [sum_split t _ fun w hw => by rw [hβ w t hw, C_0, zero_mul]]
    rw [map_add, aeval_X, if_pos h, map_sum]
    congr 1
    · obtain ⟨a, s⟩ := v
      simp only at h
      subst h
      rfl
    · refine Finset.sum_congr rfl fun l hl => ?_
      rw [map_mul, aeval_X, algHom_C, if_neg (Finset.mem_filter.1 hl).2.ne, C_1, one_mul]
      rfl
  · rw [aeval_X, if_neg h, C_1, one_mul]

theorem colOne_good {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : F ∈ dualWeyl K r n ν) (β : Matrix (Fin n) (Fin n) K)
    (hβ : ∀ w s, s < w → β w s = 0) (t : Fin n) : colOne β t F = (β t t ^ ν t) • F := by
  rw [colOne_eq β hβ, AlgHom.comp_apply, colAddS_inv hF t _ _ (fun l hl => (Finset.mem_filter.1 hl).2), colSc_hom (lsat_mem_dualWeyl.1 hF).1]

open Classical in

def cutCol (β : Matrix (Fin n) (Fin n) K) (t : Fin n) : Matrix (Fin n) (Fin n) K :=
  fun w s => if s = t then (if w = t then 1 else 0) else β w s

theorem colSub1_cut (β : Matrix (Fin n) (Fin n) K) (t : Fin n) (hid : ∀ s, s < t → ∀ w, β w s = if w = s then 1 else 0)
    (hβ : ∀ w s, s < w → β w s = 0) : colSub1 (r := r) β = (colSub1 (cutCol β t)).comp (colOne β t) := by
  classical
  apply MvPolynomial.algHom_ext
  rintro ⟨a, s⟩
  simp only [colSub1, colOne, AlgHom.comp_apply, aeval_X]
  split_ifs with h
  · subst h
    rw [map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, algHom_C, aeval_X]
    by_cases hw : s < w
    · simp [hβ w s hw]
    · have hc : ∀ x, cutCol β s x w = if x = w then 1 else 0 := by
        intro x
        unfold cutCol
        by_cases h1 : w = s
        · subst h1; simp
        · rw [if_neg h1]
          exact hid w (lt_of_le_of_ne (not_lt.1 hw) h1) x
      simp only [hc]
      rw [Finset.sum_eq_single w]
      · simp
      · intro x _ hx
        simp [hx]
      · intro h; exact absurd (Finset.mem_univ _) h
  · rw [aeval_X]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [cutCol, h]

theorem colSub1_good {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : F ∈ dualWeyl K r n ν) :
    ∀ (k t : ℕ), t + k = n → ∀ β : Matrix (Fin n) (Fin n) K, (∀ w s, s < w → β w s = 0) →
      (∀ s : Fin n, s.1 < t → ∀ w, β w s = if w = s then 1 else 0) → colSub1 β F = (∏ x, β x x ^ ν x) • F := by
  classical
  intro k
  induction k with
  | zero =>
    intro t ht β _ hid
    have h1 : ∀ s w : Fin n, β w s = if w = s then 1 else 0 := fun s w => hid s (by omega) w
    have h2 : colSub1 (r := r) β = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, s⟩
      simp only [colSub1, aeval_X, h1, AlgHom.id_apply]
      rw [Finset.sum_eq_single s]
      · simp
      · intro x _ hx
        simp [hx]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h2, AlgHom.id_apply, Finset.prod_eq_one (fun x _ => by rw [h1, if_pos rfl, one_pow]), one_smul]
  | succ k ih =>
    intro t ht β hβ hid
    have htn : t < n := by omega
    set tt : Fin n := ⟨t, htn⟩ with htt
    have hu : ∀ w s, s < w → cutCol β tt w s = 0 := by
      intro w s hsw
      unfold cutCol
      by_cases h1 : s = tt
      · rw [if_pos h1, if_neg (by rw [← h1]; exact hsw.ne')]
      · rw [if_neg h1]; exact hβ w s hsw
    have hi : ∀ s : Fin n, s.1 < t + 1 → ∀ w, cutCol β tt w s = if w = s then 1 else 0 := by
      intro s hs w
      unfold cutCol
      by_cases h1 : s = tt
      · rw [if_pos h1, h1]
      · rw [if_neg h1]
        refine hid s ?_ w
        have : s.1 ≠ t := fun h => h1 (Fin.ext h)
        omega
    rw [colSub1_cut β tt (fun s hs => hid s hs) hβ, AlgHom.comp_apply, colOne_good hF β hβ tt, map_smul,
      ih (t + 1) (by omega) (cutCol β tt) hu hi, smul_smul]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ (fun x => cutCol β tt x x ^ ν x) (Finset.mem_univ tt),
      ← Finset.mul_prod_erase Finset.univ (fun x => β x x ^ ν x) (Finset.mem_univ tt)]
    have e1 : cutCol β tt tt tt = 1 := by simp [cutCol]
    rw [e1, one_pow, one_mul]
    congr 1
    refine Finset.prod_congr rfl fun x hx => ?_
    have : x ≠ tt := (Finset.mem_erase.1 hx).1
    simp [cutCol, this]

theorem dualWeyl_bor {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : F ∈ dualWeyl K r n ν) (β : Matrix (Fin n) (Fin n) K)
    (hβ : ∀ w s, s < w → β w s = 0) : colSub1 β F = (∏ x, β x x ^ ν x) • F :=
  colSub1_good hF n 0 (by omega) β hβ fun s hs => absurd hs (Nat.not_lt_zero _)

variable {ι : Type} [Fintype ι]

theorem colSub_blockEmb (β : ι → Matrix (Fin n) (Fin n) K) (τ : ι) (F : MvPolynomial (Fin n × Fin n) K) :
    colSub β (blockEmb K τ F) = blockEmb K τ (colSub1 (β τ) F) := by
  have e : (colSub β).comp (blockEmb K τ) = (blockEmb K τ).comp (colSub1 (β τ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [colSub, blockEmb, colSub1]
  exact DFunLike.congr_fun e F

theorem VV_le_WtPol (lam : ι → DomWeight n) : DIV.VV K lam ≤ WtPol K fun τ r => (lam τ).natW r := by
  unfold DIV.VV tensorLat
  rw [Submodule.span_le]
  rintro P ⟨F, hF, rfl⟩ β hβ
  rw [map_prod]
  simp only [colSub_blockEmb]
  have h : ∀ τ, blockEmb K τ (colSub1 (β τ) (F τ)) = (∏ x, β τ x x ^ (lam τ).natW x) • blockEmb K τ (F τ) := by
    intro τ
    rw [dualWeyl_bor (hF τ) (β τ) (hβ τ).1, map_smul]
  simp only [h]
  rw [Finset.prod_smul]

theorem colSub_frDet (β : ι → Matrix (Fin n) (Fin n) K) (hβ : IsBor β) (τ : ι) :
    colSub β (frDet K n τ) = (∏ x, β τ x x) • frDet K n τ := by
  unfold frDet
  rw [AlgHom.map_det]
  have e : (colSub β).mapMatrix (Matrix.of fun α s : Fin n => (X (τ, α, s) : Pol K ι n)) =
      (Matrix.of fun α s : Fin n => (X (τ, α, s) : Pol K ι n)) * (β τ).map C := by
    refine Matrix.ext fun α s => ?_
    rw [Matrix.mul_apply]
    show colSub β (X (τ, α, s) : Pol K ι n) = ∑ x : Fin n, (X (τ, α, x) : Pol K ι n) * C (β τ x s)
    simp only [colSub, aeval_X]
    exact Finset.sum_congr rfl fun x _ => mul_comm (C (β τ x s)) (X (τ, α, x) : Pol K ι n)
  rw [e, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_of_isUpperTriangular (fun x s h => (hβ τ).1 x s h),
    smul_eq_C_mul, mul_comm]

theorem vv_in_weight : VVInWt := by
  intro K _ ι _ n lam k P hP β hβ
  rw [map_mul, VV_le_WtPol lam hP β hβ, map_prod]
  simp only [map_pow, colSub_frDet β hβ, smul_pow]
  rw [Finset.prod_smul, smul_mul_smul_comm]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun x _ => (pow_add _ _ _).symm

end VVWt

section WtVVA

open MvPolynomial Formalism.L2.DIV Formalism.GradedWeylDivisibility

variable {K : Type} [Field K] {r n : ℕ}

theorem coeff_colSc (t : Fin n) (d : K) (F : MvPolynomial (Fin r × Fin n) K) (m : Fin r × Fin n →₀ ℕ) :
    coeff m (colSc t d F) = d ^ (∑ a : Fin r, m (a, t)) * coeff m F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial m' c =>
    rw [colSc_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  | add f g hf hg => rw [map_add, coeff_add, coeff_add, hf, hg, mul_add]

theorem pow_inj_of_infinite [Infinite K] {a b : ℕ} (h : ∀ x : K, x ≠ 0 → x ^ a = x ^ b) : a = b := by
  have h0 : (Polynomial.X ^ a - Polynomial.X ^ b : Polynomial K) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : K)).infinite_compl
    intro x hx
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [h x hx, sub_self]
  have h1 := congrArg Polynomial.natDegree (sub_eq_zero.1 h0)
  simpa using h1

theorem colSub1_diag (t : Fin n) (d : K) :
    colSub1 (r := r) (Matrix.diagonal fun s => if s = t then d else 1) = colSc t d := by
  classical
  apply MvPolynomial.algHom_ext
  rintro ⟨a, s⟩
  simp only [colSub1, colSc, aeval_X]
  rw [Finset.sum_eq_single s]
  · rw [Matrix.diagonal_apply_eq]
  · intro w _ hw
    rw [Matrix.diagonal_apply_ne _ hw, C_0, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem colSub1_trans (l j : Fin n) (hlj : l ≠ j) (c : K) :
    colSub1 (r := r) (fun w s => if w = s then 1 else if w = l ∧ s = j then c else 0) = colAdd K l j c := by
  classical
  apply MvPolynomial.algHom_ext
  rintro ⟨a, s⟩
  simp only [colSub1, colAdd, aeval_X]
  have e : ∀ w : Fin n, (C (if w = s then (1 : K) else if w = l ∧ s = j then c else 0) * X (a, w) : MvPolynomial (Fin r × Fin n) K) =
      (if w = s then X (a, w) else 0) + (if w = l then (if s = j then C c * X (a, w) else 0) else 0) := by
    intro w
    by_cases h1 : w = s
    · by_cases h2 : w = l
      · have h3 : s ≠ j := fun h => hlj (h2.symm.trans (h1.trans h))
        simp [h1, h3]
      · have h2' : s ≠ l := fun h => h2 (h1.trans h)
        simp [h1, h2']
    · by_cases h2 : w = l
      · by_cases h3 : s = j <;> simp [h1, h2, h3, hlj]
      · simp [h1, h2]
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp

theorem mem_dualWeyl_of_bor [Infinite K] {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K}
    (h : ∀ β : Matrix (Fin n) (Fin n) K, (∀ w s, s < w → β w s = 0) → (∀ w, β w w ≠ 0) → colSub1 β F = (∏ x, β x x ^ ν x) • F) :
    F ∈ dualWeyl K r n ν := by
  classical
  refine (dualWeylModuleMemIff K r n ν F).2 ⟨?_, ?_⟩
  · intro m hm
    funext t
    have h1 : ∀ x : K, x ≠ 0 → x ^ (∑ a : Fin r, m (a, t)) = x ^ ν t := by
      intro x hx
      have h2 := h (Matrix.diagonal fun s => if s = t then x else 1) (fun w s hws => Matrix.diagonal_apply_ne _ hws.ne')
        (fun w => by rw [Matrix.diagonal_apply_eq]; split_ifs; exacts [hx, one_ne_zero])
      rw [colSub1_diag] at h2
      have h3 := congrArg (coeff m) h2
      rw [coeff_colSc, coeff_smul, smul_eq_mul] at h3
      have h4 : (∏ y, (Matrix.diagonal (fun s => if s = t then x else 1) : Matrix (Fin n) (Fin n) K) y y ^ ν y) = x ^ ν t := by
        rw [Finset.prod_eq_single t]
        · rw [Matrix.diagonal_apply_eq, if_pos rfl]
        · intro y _ hy
          rw [Matrix.diagonal_apply_eq, if_neg hy, one_pow]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [h4] at h3
      exact mul_right_cancel₀ hm h3
    rw [← pow_inj_of_infinite h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ (colW r n i)), Finset.sum_apply,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single t]
    · simp [colW]
    · intro s _ hs
      simp [colW, hs]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro l j hlj c
    have h2 := h (fun w s => if w = s then 1 else if w = l ∧ s = j then c else 0)
      (fun w s hws => by
        rw [if_neg hws.ne', if_neg]
        rintro ⟨rfl, rfl⟩
        exact absurd hlj (not_lt.2 hws.le))
      (fun w => by simp)
    rw [colSub1_trans l j hlj.ne] at h2
    rw [h2]
    simp

end WtVVA

section WtVVB

open MvPolynomial Formalism.L2.DIV Formalism.GradedWeylDivisibility

variable {K : Type} [Field K] {n : ℕ} {ι : Type}

abbrev Off (ι : Type) (n : ℕ) (τ : ι) : Type := {v : ι × Fin n × Fin n // v.1 ≠ τ}

open Classical in

def psi (τ : ι) : Pol K ι n →ₐ[K] MvPolynomial (Off ι n τ) (MvPolynomial (Fin n × Fin n) K) :=
  aeval fun v => if h : v.1 = τ then C (X v.2) else X ⟨v, h⟩

def psi' (τ : ι) : MvPolynomial (Off ι n τ) (MvPolynomial (Fin n × Fin n) K) →+* Pol K ι n :=
  eval₂Hom (blockEmb K τ).toRingHom fun w => X w.1

theorem psi'_psi (τ : ι) (Q : Pol K ι n) : psi' τ (psi τ Q) = Q := by
  have e : (psi' (K := K) (n := n) τ).comp (psi τ).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [psi, psi', blockEmb, MvPolynomial.algebraMap_apply]
    · rintro ⟨t, v⟩
      by_cases h : t = τ
      · subst h
        simp [psi, psi', blockEmb]
      · simp [psi, psi', h]
  exact RingHom.congr_fun e Q

theorem psi_blockEmb (τ : ι) (G : MvPolynomial (Fin n × Fin n) K) : psi τ (blockEmb K τ G) = C G := by
  induction G using MvPolynomial.induction_on with
  | C a => simp [blockEmb, MvPolynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp =>
    rw [map_mul, map_mul, hp, map_mul]
    simp [blockEmb, psi]

theorem psi_psi' (τ : ι) (p : MvPolynomial (Off ι n τ) (MvPolynomial (Fin n × Fin n) K)) : psi τ (psi' τ p) = p := by
  have e : (psi (K := K) (n := n) τ).toRingHom.comp (psi' τ) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro G
      simp only [RingHom.comp_apply, psi', coe_eval₂Hom, eval₂_C, RingHom.id_apply]
      exact psi_blockEmb τ G
    · intro w
      simp [psi, psi', w.2]
  exact RingHom.congr_fun e p

open Classical in
theorem psi_colSub [Fintype ι] (τ : ι) (β : Matrix (Fin n) (Fin n) K) (Q : Pol K ι n) :
    psi τ (colSub (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β) Q) = map (colSub1 β).toRingHom (psi τ Q) := by
  have e : (psi (K := K) (n := n) τ).toRingHom.comp (colSub (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β)).toRingHom =
      (map (colSub1 β).toRingHom).comp (psi τ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [MvPolynomial.algebraMap_apply]
    · rintro ⟨t, a, s⟩
      by_cases h : t = τ
      · subst h
        simp [psi, colSub, colSub1, MvPolynomial.algebraMap_apply]
      · simp [psi, colSub, h, Matrix.one_apply]
  exact RingHom.congr_fun e Q

theorem coeff_psi_mem [Fintype ι] [Infinite K] {ν : ι → Fin n → ℕ} {Q : Pol K ι n} (hQ : Q ∈ WtPol K ν) (τ : ι) (r : Off ι n τ →₀ ℕ) :
    coeff r (psi τ Q) ∈ dualWeyl K n n (ν τ) := by
  classical
  apply mem_dualWeyl_of_bor
  intro β h1 h2
  have hB : IsBor (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β) := by
    intro σ
    by_cases h : σ = τ
    · subst h
      rw [Function.update_self]
      exact ⟨h1, h2⟩
    · rw [Function.update_of_ne h]
      exact ⟨fun w s hws => Matrix.one_apply_ne hws.ne', fun w => by simp⟩
  have h3 := congrArg (fun x => coeff r (psi τ x)) (hQ _ hB)
  simp only [psi_colSub, coeff_map, map_smul, coeff_smul] at h3
  have h4 : (∏ σ, ∏ x, (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β) σ x x ^ ν σ x) = ∏ x, β x x ^ ν τ x := by
    rw [Finset.prod_eq_single τ]
    · rw [Function.update_self]
    · intro σ _ hσ
      rw [Function.update_of_ne hσ]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h4] at h3
  exact h3

def gOf (τ : ι) (m : ι × Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn

def rOf (τ : ι) (m : ι × Fin n × Fin n →₀ ℕ) : Off ι n τ →₀ ℕ := m.comapDomain Subtype.val Subtype.val_injective.injOn

theorem split_pos (τ : ι) (m : ι × Fin n × Fin n →₀ ℕ) :
    m = (gOf τ m).mapDomain (Prod.mk τ) + (rOf τ m).mapDomain Subtype.val := by
  ext ⟨t, v⟩
  by_cases h : t = τ
  · subst h
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply (Prod.mk_right_injective t), Finsupp.mapDomain_of_notMem_range, add_zero]
    · rfl
    · rintro ⟨w, hw⟩
      exact w.2 (congrArg Prod.fst hw)
  · rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range, zero_add]
    · exact (Finsupp.mapDomain_apply Subtype.val_injective (rOf τ m) (⟨(t, v), h⟩ : Off ι n τ)).symm
    · rintro ⟨w, hw⟩
      exact h (congrArg Prod.fst hw).symm

theorem psi'_monomial (τ : ι) (r : Off ι n τ →₀ ℕ) (G : MvPolynomial (Fin n × Fin n) K) :
    psi' τ (monomial r G) = blockEmb K τ G * monomial (r.mapDomain Subtype.val) 1 := by
  have h : (monomial (r.mapDomain Subtype.val) 1 : Pol K ι n) = r.prod fun w e => X w.1 ^ e := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [h, psi', coe_eval₂Hom, eval₂_monomial]
  rfl

theorem psi_monomial (τ : ι) (m : ι × Fin n × Fin n →₀ ℕ) (c : K) :
    psi τ (monomial m c) = monomial (rOf τ m) (monomial (gOf τ m) c) := by
  have h : (monomial m c : Pol K ι n) = psi' τ (monomial (rOf τ m) (monomial (gOf τ m) c)) := by
    rw [psi'_monomial, blockEmb, rename_monomial, monomial_mul, mul_one, ← split_pos]
  rw [h, psi_psi']

def atPos (τ : ι) (π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K) : Pol K ι n →ₗ[K] Pol K ι n :=
  (basisMonomials _ K).constr K fun m => psi' τ (monomial (rOf τ m) (π (monomial (gOf τ m) 1)))

theorem coeff_psi_atPos (τ : ι) (π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K) (Q : Pol K ι n)
    (r : Off ι n τ →₀ ℕ) : coeff r (psi τ (atPos τ π Q)) = π (coeff r (psi τ Q)) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial m c =>
    have h : (monomial m c : Pol K ι n) = c • basisMonomials _ K m := by
      rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    have h2 : (monomial (gOf τ m) c : MvPolynomial (Fin n × Fin n) K) = c • monomial (gOf τ m) 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [psi_monomial, h, map_smul, atPos, Module.Basis.constr_basis, map_smul, psi_psi', coeff_smul, coeff_monomial, coeff_monomial, h2]
    split_ifs
    · rw [map_smul]
    · rw [smul_zero, map_zero]
  | add f g hf hg => simp only [map_add, coeff_add, hf, hg]

theorem atPos_fixed (τ : ι) (π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K) (Q : Pol K ι n)
    (h : ∀ r, π (coeff r (psi τ Q)) = coeff r (psi τ Q)) : atPos τ π Q = Q := by
  have e : psi τ (atPos τ π Q) = psi τ Q := MvPolynomial.ext _ _ fun r => by rw [coeff_psi_atPos, h r]
  rw [← psi'_psi τ (atPos τ π Q), e, psi'_psi]

theorem atPos_mul (τ : ι) (π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K) (G : MvPolynomial (Fin n × Fin n) K)
    (R : Pol K ι n) (R' : MvPolynomial (Off ι n τ) K) (hR : psi τ R = map C R') :
    atPos τ π (blockEmb K τ G * R) = blockEmb K τ (π G) * R := by
  have e : psi τ (atPos τ π (blockEmb K τ G * R)) = psi τ (blockEmb K τ (π G) * R) := by
    refine MvPolynomial.ext _ _ fun r => ?_
    rw [coeff_psi_atPos, map_mul, map_mul, psi_blockEmb, psi_blockEmb, hR, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm G, mul_comm (π G),
      ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  rw [← psi'_psi τ (atPos τ π (blockEmb K τ G * R)), e, psi'_psi]

theorem psi_blockEmb_ne (τ σ : ι) (h : σ ≠ τ) (F : MvPolynomial (Fin n × Fin n) K) :
    psi τ (blockEmb K σ F) = map C (rename (fun v => (⟨(σ, v), h⟩ : Off ι n τ)) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [blockEmb, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    simp [blockEmb, psi, h]

open Classical in
theorem atPos_prod [Fintype ι] (τ : ι) (π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K)
    (F : ι → MvPolynomial (Fin n × Fin n) K) :
    atPos τ π (∏ σ, blockEmb K σ (F σ)) = ∏ σ, blockEmb K σ (Function.update F τ (π (F τ)) σ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
  have e1 : ∏ σ ∈ Finset.univ.erase τ, blockEmb K σ (Function.update F τ (π (F τ)) σ) = ∏ σ ∈ Finset.univ.erase τ, blockEmb K σ (F σ) :=
    Finset.prod_congr rfl fun σ hσ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]
  rw [e1]
  refine atPos_mul τ π (F τ) _ (∏ σ ∈ Finset.univ.erase τ, if h : σ = τ then 1 else rename (fun v => (⟨(σ, v), h⟩ : Off ι n τ)) (F σ)) ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun σ hσ => ?_
  rw [dif_neg (Finset.ne_of_mem_erase hσ), psi_blockEmb_ne τ σ (Finset.ne_of_mem_erase hσ)]

def TS [Fintype ι] (W : ι → Submodule K (MvPolynomial (Fin n × Fin n) K)) (S : Finset ι) : Submodule K (Pol K ι n) :=
  Submodule.span K {P | ∃ F : ι → MvPolynomial (Fin n × Fin n) K, (∀ σ ∈ S, F σ ∈ W σ) ∧ P = ∏ σ, blockEmb K σ (F σ)}

theorem mem_TS_empty [Fintype ι] (W : ι → Submodule K (MvPolynomial (Fin n × Fin n) K)) (Q : Pol K ι n) : Q ∈ TS W ∅ := by
  classical
  rw [Q.as_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  have hm : m = ∑ t, (gOf t m).mapDomain (Prod.mk t) := by
    ext ⟨t, v⟩
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single t]
    · exact (Finsupp.mapDomain_apply (Prod.mk_right_injective t) (gOf t m) v).symm
    · intro σ _ hσ
      refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨w, hw⟩
      exact hσ (congrArg Prod.fst hw)
    · intro h; exact absurd (Finset.mem_univ _) h
  have h : (monomial m (coeff m Q) : Pol K ι n) = coeff m Q • ∏ σ, blockEmb K σ (monomial (gOf σ m) (1 : K)) := by
    rw [ldtensor_prod_monomial, smul_monomial, smul_eq_mul, mul_one, ← hm]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun σ hσ => absurd hσ (Finset.notMem_empty σ), rfl⟩)

theorem wtPol_le_tensor [Fintype ι] [Infinite K] (ν : ι → Fin n → ℕ) :
    WtPol K ν ≤ tensorLat K K fun τ => dualWeyl K n n (ν τ) := by
  classical
  intro Q hQ
  have key : ∀ S : Finset ι, Q ∈ TS (fun τ => dualWeyl K n n (ν τ)) S := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact mem_TS_empty _ Q
    | insert τ S _ ih =>
      obtain ⟨T, hT⟩ := Submodule.exists_isCompl (dualWeyl K n n (ν τ))
      set π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
        (dualWeyl K n n (ν τ)).subtype ∘ₗ Submodule.projectionOnto _ T hT with hπ
      have hfix : atPos τ π Q = Q := by
        refine atPos_fixed τ π Q fun r => ?_
        have h := Submodule.projectionOnto_apply_left hT (⟨coeff r (psi τ Q), coeff_psi_mem hQ τ r⟩ : dualWeyl K n n (ν τ))
        have h' : Submodule.projectionOnto _ T hT (coeff r (psi τ Q)) = ⟨coeff r (psi τ Q), coeff_psi_mem hQ τ r⟩ := h
        rw [hπ, LinearMap.comp_apply, h']
        rfl
      have hle : TS (fun τ => dualWeyl K n n (ν τ)) S ≤ (TS (fun τ => dualWeyl K n n (ν τ)) (insert τ S)).comap (atPos τ π) := by
        unfold TS
        rw [Submodule.span_le]
        rintro P ⟨F, hF, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, atPos_prod]
        refine Submodule.subset_span ⟨_, fun σ hσ => ?_, rfl⟩
        by_cases h : σ = τ
        · subst h
          rw [Function.update_self]
          exact (Submodule.projectionOnto _ T hT (F σ)).2
        · rw [Function.update_of_ne h]
          exact hF σ ((Finset.mem_insert.1 hσ).resolve_left h)
      have := hle ih
      rw [Submodule.mem_comap, hfix] at this
      exact this
  have h := key Finset.univ
  unfold TS at h
  unfold tensorLat
  refine Submodule.span_mono ?_ h
  rintro P ⟨F, hF, rfl⟩
  exact ⟨F, fun s => hF s (Finset.mem_univ s), rfl⟩

theorem WtInVV_core [Fintype ι] [Infinite K] (lam : ι → DomWeight n) : WtPol K (fun τ r => (lam τ).natW r) ≤ DIV.VV K lam :=
  wtPol_le_tensor fun τ => (lam τ).natW

end WtVVB

theorem weight_in_vv : WtInVV := fun _ _ _ _ _ _ lam => WtInVV_core lam

theorem jet_in_vv_reduction : JetInVVRed := by
  intro h1 h2 K _ _ ι _ a b hab lam lam' n hw J P hP
  rw [jetMap_shift]
  apply h2 K ι b lam'
  have e : (fun τ r => (lam' τ).natW r) = extNu b (fun τ r => (lam τ).natW r + n τ) := by
    funext τ r; exact hw τ r
  rw [e]
  exact jet_weight K ι a b hab J _ _ (h1 K ι a lam n P hP)

theorem jetInVV_of_wtInVV (h2 : WtInVV) (K : Type) [Field K] [Infinite K] (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (hw : ∀ τ r, (lam' τ).natW r = extNu b (fun τ r => (lam τ).natW r + n τ) τ r) : JetInVV K lam lam' n :=
  jet_in_vv_reduction vv_in_weight h2 K ι a b hab lam lam' n hw

theorem jet_in_vv_of_weight : JetInVVOf := jetInVV_of_wtInVV weight_in_vv

section Unf

open MvPolynomial

theorem frobenius_poly_injective : FrPolyInj := by
  intro D u C O i hi
  rw [injective_iff_map_eq_zero]
  intro Q hQ
  set Dt : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ := ∏ τ, frDet ℂ (D.R.N i) τ with hDt
  have hev : ∀ v : GL3Theta.FrV D (D.R.N i) → ℂ, eval v Dt = ∏ τ, (Matrix.of fun α k => v (τ, α, k)).det := by
    intro v
    rw [hDt, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    unfold frDet
    rw [RingHom.map_det]
    congr 1
    ext α k
    simp
  have h0 : Q * Dt = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_mul, map_zero, hev]
    by_cases h : ∀ τ, (Matrix.of fun α k => v (τ, α, k) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ).det ≠ 0
    · obtain ⟨y, hy⟩ := (O.frm_range i hi fun τ => Matrix.of fun α k => v (τ, α, k)).2 h
      have h1 := congrFun hQ y
      have h2 : eval v Q = 0 := by
        have : frPoly O i Q y = eval v Q := by
          show GL3Theta.evFr D Q (O.frm i y) = _
          rw [hy]; rfl
        rw [← this, h1]; rfl
      rw [h2, zero_mul]
    · push Not at h
      obtain ⟨τ, hτ⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  rcases mul_eq_zero.1 h0 with h | h
  · exact h
  · exfalso
    have h1 := hev fun k => if k.2.1 = k.2.2 then 1 else 0
    rw [h, map_zero] at h1
    have h2 : ∀ τ : D.what₂.Tau, (Matrix.of fun α k : Fin (D.R.N i) => (if α = k then (1 : ℂ) else 0)).det = 1 := by
      intro τ
      have : (Matrix.of fun α k : Fin (D.R.N i) => (if α = k then (1 : ℂ) else 0)) = 1 := by
        ext α k; simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    exact zero_ne_one (h1.trans (Finset.prod_eq_one fun τ _ => h2 τ))

theorem frInv_spec {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) {i : ℕ} (hi : i ≤ D.R.m) :
    frInv O i ∘ₗ frPoly O i = LinearMap.id :=
  Classical.epsilon_spec (p := fun g => g ∘ₗ frPoly O i = LinearMap.id)
    (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 (frobenius_poly_injective D u C O i hi)))

theorem unfolding_char_formula : UnfCFormula := by
  intro D u C O i hi Θ Q y'
  have h : frInv O i (fun y => GL3Theta.evFr D Q (O.frm i y)) = Q := LinearMap.congr_fun (frInv_spec O hi) Q
  unfold unfC
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h]
  exact jetMap_applyAt0 D O.dgen Θ Q (O.frm (i + 1) y')

theorem unfolding_iff_alt : UnfIsIff := by
  intro D u C O i hi ν
  constructor
  · intro h c c' Q hQ y'
    rw [← unfolding_char_formula D u C O i hi]
    exact congrFun (h c c' Q hQ) y'
  · intro h c c' Q hQ
    funext y'
    exact (h c c' Q hQ y').trans (unfolding_char_formula D u C O i hi _ Q y').symm

theorem nuRow_anti_le (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r s : ℕ) (hrs : r ≤ s) (hs : s < D.R.N i) :
    DV.nuRow D u (i + 1) τ s ≤ DV.nuRow D u (i + 1) τ r := by
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (RowWeightLemmas.nuRow_anti D u i hi τ n hs).trans (ih (by omega))

theorem nu_t_identity : NuTIs := by
  intro D u i hi τ r
  obtain ⟨z, hz⟩ := RowWeightLemmas.nuRow_int D u i hi τ r r.2
  have hpos : 0 < DV.nuRow D u (i + 1) τ r :=
    lt_of_lt_of_le (RowWeightLemmas.nuRow_last_pos D u i hi τ) (nuRow_anti_le D u i hi τ r _ (by have := r.2; omega) (by have := r.2; omega))
  have hz0 : 0 < z := by rw [hz] at hpos; exact_mod_cast hpos
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz0.le
  have : nuT D u i τ r = n := by
    unfold nuT; rw [hz]; simp
  rw [this, hz]; constructor
  · simp
  · exact_mod_cast hz0

theorem UnfIsAll.unfIs {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O : GL3Theta.LiftObj D C} {i : ℕ} (h : UnfIsAll O i)
    (ν : D.what₂.Tau → Fin (D.R.N i) → ℕ) : UnfIs O i ν := fun c c' Q _ => h c c' Q

theorem forms_sharp_description : FormsSharp := by
  intro hSP D u C O i hi ν f hf
  have e1 : C.sharp i f = mulFun (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) f := by
    have e : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
      funext y; simp only [O.frm_de i hi]
    rw [e]
    rfl
  obtain ⟨Q, hQ⟩ := hSP D.what₂.Tau (D.R.N i) (C.Y i) (O.frm i) (O.frm_range i hi) _ (C.sSharp i) ν (fun τ r => sub_add_cancel _ _) f hf
  obtain ⟨Q', hQ', h⟩ := (sharp_vector_formula D.what₂.Tau (D.R.N i) (C.Y i) (O.frm i) (O.frm_range i hi) _ (C.sSharp i) ν (fun τ r => sub_add_cancel _ _)
    (mulFun (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) f)).2 ⟨⟨f, hf, rfl⟩, Q, hQ⟩
  exact ⟨Q', hQ', e1.trans h⟩

theorem chain_char_eval : ChainCEv := by
  intro D u C O i hi K _ σ c c' J z hJ sh n hn P
  have h := unfolding_gl_eval K D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) (C.Y i) (C.Y (i + 1)) (O.frm i) (O.frm (i + 1)) (frobenius_poly_injective D u C O i hi.le)
    (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) σ O.dgen (O.Th i c c') J z hJ sh (C.sSharp i) (C.sDiv i) n hn P
  rw [h]
  have e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
    funext y; simp only [O.frm_de i hi.le]
  have e2 : (fun y' => (∏ τ, (O.frm (i + 1) y' τ).det ^ C.sDiv i τ)⁻¹) = fun y' => (∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ))⁻¹ := by
    funext y'; simp only [O.frm_de (i + 1) hi]
  rw [e1, e2]
  rfl

theorem map_mem_VV {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {n : ℕ} (σ : K →+* L) (lam : ι → DomWeight n) (F : DIV.Pol K ι n)
    (hF : F ∈ DIV.VV K lam) : MvPolynomial.map σ F ∈ DIV.VV L lam := by
  unfold DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun τ => MvPolynomial.map σ (f τ), fun τ => Formalism.GradedWeylDivisibility.dualWeylMap K L σ n n _ _ (hf τ), ?_⟩
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Formalism.GradedWeylDivisibility.blockEmb, Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.map_rename]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem tied_on_models : TiedOnModels := by
  intro D u C O i hi ν h K _ σ lam n hw c c' J z hJ sh hn P hP
  have hs : C.sharp i (evG (O.frm i) sh σ P) = frPoly O i (MvPolynomial.map σ P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ) := by
    have h1 := mulFun_evG (fr := O.frm i) (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) σ sh (C.sSharp i) n hn P
    have e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
      funext y; simp only [O.frm_de i hi.le]
    rw [e1] at h1
    exact h1
  have hQ : MvPolynomial.map σ P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ ∈ WtPol ℂ ν := by
    have h2 := vv_in_weight ℂ D.what₂.Tau _ lam n (MvPolynomial.map σ P) (map_mem_VV σ lam P hP)
    have e : (fun τ r => (lam τ).natW r + n τ) = ν := by funext τ r; exact hw τ r
    rwa [e] at h2
  rw [chain_char_eval D u C O i hi K σ c c' J z hJ sh n hn P]
  show z • ((C.rhoDet i c * C.rhoDet' i c') • C.divDe i (C.unf i c c' (C.sharp i (evG (O.frm i) sh σ P)))) =
    (C.rhoDet i c * C.rhoDet' i c') • z • C.divDe i (unfC O i (O.Th i c c') (C.sharp i (evG (O.frm i) sh σ P)))
  rw [hs, h c c' _ hQ, smul_comm]

end Unf

end GlobalTheory.KerWt
