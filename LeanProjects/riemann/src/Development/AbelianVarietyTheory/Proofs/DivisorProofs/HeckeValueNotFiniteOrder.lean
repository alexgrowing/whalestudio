import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterInfiniteOrderAtSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpli
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.CMSplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (τ₀ τ₁ : E →+* ℂ) :
    ∃ g : E ≃ₐ[ℚ] E, ∀ x, τ₀ (g x) = τ₁ x := by
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    show algebraMap ℚ ℂ q = τ₀ (algebraMap ℚ E q)
    rw [eq_ratCast (algebraMap ℚ ℂ), eq_ratCast (algebraMap ℚ E), map_ratCast]
  exact ⟨(τ₁.toRatAlgHom).restrictNormal' E, fun x => (τ₁.toRatAlgHom).restrictNormal_commutes E x⟩

theorem not_isOfFinOrder_val_of_tame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (hgal : IsGalois ℚ E) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (χ : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ) (ht : ∀ v, χ.TameAt v) (hinf : χ.HasInf (fun w => (τ w).1) n)
    (hn : ∀ w, n w ≠ 0) (p : ℕ) (hp : p.Prime) (W : HeightOneSpectrum (𝓞 E)) (hN : Ideal.absNorm W.asIdeal = p)
    (hsq : (p : 𝓞 E) ∉ W.asIdeal ^ 2) : ¬ IsOfFinOrder (χ.val W) := by
  intro hfin
  classical
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht W (Formalism.L2.Host.unif W)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val W ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ₀ : E →+* ℂ := (τ w₀).1 with hτ₀
  choose g hg using fun w => exists_aut_comp τ₀ (τ w).1
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 = τ₀ (∏ w, (g w z / g w (σ z)) ^ n w) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : τ₀ (g w (σ z)) = starRingEnd ℂ (τ₀ (g w z)) := by
      rw [hg, hg]
      exact hcm.2.2.2 _ _
    have e' : (τ w).1 z = τ₀ (g w z) := (hg w z).symm
    have h0 : τ₀ (g w z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ w, (g w z / g w (σ z)) ^ n w) ^ a = 1 := by
    apply τ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := W) ha (by rw [h6, map_one])
  have hg0 : ∀ x, g w₀ x = x := fun x => τ₀.injective (hg w₀ x)
  have hres : ∀ w, (∀ f : F, τ₀ (algebraMap F E f) = w.embedding f) → w = w₀ := by
    intro w hw
    have e : w.embedding = w₀.embedding := by
      ext f
      rw [← hw f]
      exact (RingHom.congr_fun (τ w₀).2 f)
    rw [← InfinitePlace.mk_embedding w, e, InfinitePlace.mk_embedding]
  have hc : ∀ w, W.valuation E (g w (σ z)) = 1 := by
    intro w
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 ((g w : E →+* E).comp (σ : E →+* E)) fun e => ?_
    have hw : w = w₀ := hres w fun f => by
      have := RingHom.congr_fun e (algebraMap F E f)
      change g w (σ (algebraMap F E f)) = algebraMap F E f at this
      rw [← this, hg, AlgHom.commutes]
      exact RingHom.congr_fun (τ w).2 f
    subst hw
    obtain ⟨x, hx⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
    have := RingHom.congr_fun e x
    change g w (σ x) = x at this
    rw [hg0] at this
    exact hx this
  have hgw : ∀ w, w ≠ w₀ → W.valuation E (g w z) = 1 := by
    intro w hw
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 (g w : E →+* E) fun e => hw (hres w fun f => ?_)
    have := RingHom.congr_fun e (algebraMap F E f)
    change g w (algebraMap F E f) = algebraMap F E f at this
    rw [← this, hg]
    exact RingHom.congr_fun (τ w).2 f
  rw [map_prod, Finset.prod_eq_single w₀ (fun w _ h => by rw [map_zpow₀, map_div₀, hgw w h, hc w, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hg0, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn w₀ h
  · omega
  · omega

end GlobalTheory.CMSplitValue

namespace GlobalTheory.CMSplitValue

theorem not_isOfFinOrder_val : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → IsGalois ℚ E → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (H : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ), H.HasInf (fun w => (τ w).1) n → (∀ w, n w ≠ 0) → ∀ (p : ℕ), p.Prime → ∀ W : HeightOneSpectrum (𝓞 E), Ideal.absNorm W.asIdeal = p → (p : 𝓞 E) ∉ W.asIdeal ^ 2 → ¬ IsOfFinOrder (H.val W) := by
  intro F E _ _ _ _ _ σ hcm hgal τ H n hinf hn p hp W hN hsq hfin
  obtain ⟨N, hN0, hunr⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt E H
  have ht : ∀ v, (H ^ N).TameAt v := fun v x hx _ => hunr v x hx
  have hinf' : (H ^ N).HasInf (fun w => (τ w).1) (fun w => (N : ℤ) * n w) := by
    intro k
    rw [GlobalTheory.SplitValuePow.inf_pow, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  refine not_isOfFinOrder_val_of_tame F E σ hcm hgal τ (H ^ N) _ ht hinf'
    (fun w => mul_ne_zero (by exact_mod_cast hN0.ne') (hn w)) p hp W hN hsq ?_
  rw [GlobalTheory.SplitValuePow.val_pow]
  exact hfin.pow

end GlobalTheory.CMSplitValue
