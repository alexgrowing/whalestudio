import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductMapTensorAinfToBcrisWachInclusionConstantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionLayerIoCommutesFrobeniusGaloisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialTeichmullerRootTaylorModFilStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBanachModelTensorAcrisStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.BanachEval

open PowerSeries Filter GlobalTheory.HWL.Disc

section Letters

variable {O N : Type} [CommRing O] [CommRing N] {n : ℕ} [NeZero n] (f : LetA O n →+* N)

theorem sum_letE : ∑ i, f (letE i) = 1 := by
  rw [← map_sum, ← map_one f]
  exact congrArg f (Finset.univ_sum_single (1 : LetA O n))

theorem sum_letE_mul (x y : ZMod n → N) :
    ∑ i, f (letE i) * (x i * y i) = (∑ i, f (letE i) * x i) * ∑ i, f (letE i) * y i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · have : (letE i : LetA O n) * letE i = letE i := by
      ext1 j
      by_cases h : j = i <;> simp [letE, h]
    rw [mul_mul_mul_comm, ← map_mul, this]
  · intro j _ hj
    have : (letE i : LetA O n) * letE j = 0 := by
      ext1 k
      by_cases h : k = i
      · simp [letE, h, hj.symm]
      · simp [letE, h]
    rw [mul_mul_mul_comm, ← map_mul, this, map_zero, zero_mul]
  · simp

theorem sum_letE_const (a : LetA O n) : ∑ i, f (letE i) * f (fun _ => a i) = f a := by
  simp only [← map_mul]
  rw [← map_sum]
  congr 1
  ext1 j
  simp [letE, Pi.single_apply]

omit [NeZero n] in
theorem letφ_letE (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) : letφ φ₀ (letE (i - 1)) = letE i := by
  ext1 j
  change φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = _
  by_cases h : j = i <;> simp [letE, h]

omit [NeZero n] in
theorem letγ_letE (g : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) : letγ g (letE i) = letE i := by
  ext1 j
  change g ((letE i : LetA O n) j) = _
  by_cases h : j = i <;> simp [letE, h]

end Letters

variable {l : ℕ} [Fact l.Prime]

theorem frob_root {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    WittVector.frobenius (WittVector.teichmuller l (AI.εroot (s + 1)) - 1) =
      WittVector.teichmuller l (AI.εroot s) - 1 := by
  rw [map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
    LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  rfl

theorem sc_map {LL : FinExt l} (a : (↥(OL LL))⟦X⟧) : SC (map (algebraMap ↥(OL LL) ↥LL.1) a) :=
  sc_of_le 0 fun k => by simpa using norm_integer_le_one (coeff k a)

theorem sc_log (LL : FinExt l) : SC (logS LL) := sc_lg (norm_natCast_inv_le LL)

theorem frob_injective {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (LL : FinExt l) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := ↥LL.1) P.φB.toLinearMap
    (GlobalTheory.Per.TiedField.tied_field l P AI T).2.2.2.1

theorem crisFrobenius_periodT_eq_prime_smul (P : LocPrime l) (K : FinExt l) : P.φB P.tB = (l : ℚ_[l]) • P.tB := by
  have h := (P.PD K).t_φ
  rwa [P.PD_φ, P.period_datum_t_eq, P.PD_p] at h

set_option maxHeartbeats 1000000 in

theorem exists_eval : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∃ J, IsEval I β J := by
  intro l _ P AI T K s LL hG Γ R I hW β hβ
  obtain ⟨N, _, _, c, b, κ, φ, γ, t, ⟨hκb, hφb, hκφ, hγb, hκγ, hκt⟩, hc, hb, hbo, hκc, ⟨hφ, hφc⟩, hγ, hs, hlog, hcl⟩ :=
    GlobalTheory.T.exists_banachModel_tensor_Acris l P AI T LL β hβ
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨by
    haveI := (P.PD K).finK₀
    exact Module.finrank_pos.ne'⟩
  let μ : ℕ → N := fun s => b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1))
  have hμ : ∀ s, Small (μ s) := hs
  have hc' : Bdd c := hc
  let f : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)) →+* N := b.comp I.io.toRingHom
  have hf : ∀ a, f a = b (I.io a) := fun _ => rfl
  have hfπ : f letπ = μ s := congrArg b I.io_π
  have hint : ∀ a, ev c (μ s) (map (algebraMap ↥(OL LL) ↥LL.1) a) = f (fun _ => a) := fun a =>
    ev_map (algebraMap ↥(OL LL) ↥LL.1) (hμ s) hc' (f.comp (Pi.constRingHom _ _))
      (fun o => (congrArg b (I.io.commutes o)).trans (by exact hbo o)) hfπ (fun _ => hb _) a (sc_map a)
  have hfφ : ∀ a, f (letφ R.φ₀ a) = φ (f a) := (GlobalTheory.T.wachInclusionLayer_io_commutes_frobenius_galois l P AI K s LL Γ R I N b (φ.comp b)).1 hφb
  have hfγ : ∀ (g : ↥(GK K)) a, f (letγ (R.γ₀ (Γ.resΓ g)) a) = γ g (f a) := fun g =>
    (GlobalTheory.T.wachInclusionLayer_io_commutes_frobenius_galois l P AI K s LL Γ R I N b ((γ g).comp b)).2 g (hγb g)
  have hsub : ∀ (ψ : N →+* N) (y : (↥(OL LL))⟦X⟧), Continuous ψ → (∀ x, ψ (c x) = c x) → constantCoeff y = 0 →
      f (fun _ => y) = ψ (μ s) → ∀ a, Conv a →
      ev c (μ s) (subst (map (algebraMap ↥(OL LL) ↥LL.1) y) a) = ψ (ev c (μ s) a) := by
    intro ψ y h1 h2 h3 h4 a ha
    have ha' := (conv_iff_sc a).1 ha
    have h5 := hasSum_subst hc' (hμ s) (y := map (algebraMap ↥(OL LL) ↥LL.1) y)
      (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h3, map_zero])
      (fun k => by simpa using norm_integer_le_one (coeff k y)) ha'
    rw [hint, h4] at h5
    exact h5.unique (hasSum_map hc' (hμ s) ha' ψ h1 h2)
  refine ⟨fun a => κ (∑ i, f (letE i) * ev c (μ s) (a i)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a a' ha ha'
    rw [← map_add, ← Finset.sum_add_distrib]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.add_apply, ev_add hc' (hμ s) ((conv_iff_sc _).1 (ha i)) ((conv_iff_sc _).1 (ha' i)), mul_add]
  · intro a a' ha ha'
    rw [← map_mul, ← sum_letE_mul]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.mul_apply, ev_mul hc' (hμ s) ((conv_iff_sc _).1 (ha i)) ((conv_iff_sc _).1 (ha' i))]
  · intro x a ha
    have e : algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] P.R.B) x = κ (c x) := (hκc x).symm
    rw [Algebra.smul_def x (κ _), e, ← map_mul, Finset.mul_sum]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.smul_apply, ev_C_mul hc' (hμ s) x ((conv_iff_sc _).1 (ha i)), mul_left_comm]
  · intro a
    rw [← hκb, ← hf, ← sum_letE_const f a]
    exact congrArg κ (Finset.sum_congr rfl fun i _ => congrArg _ (hint (a i)))
  · intro a ha
    have hy : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
    have hy' : ((1 + X) ^ l - 1 : (↥LL.1)⟦X⟧) = map (algebraMap ↥(OL LL) ↥LL.1) (R.φ₀ X) := by
      simp [hy]
    rw [← hκφ, map_sum φ, ← Equiv.sum_comp (Equiv.subRight (1 : ZMod _))
      (fun i => φ (f (letE i) * ev c (μ s) (a i)))]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Equiv.subRight_apply, map_mul, ← hfφ, letφ_letE, hy',
      hsub φ _ hφ hφc (by simp [hy]) (hfπ ▸ hfφ letπ) _ (ha _)]
  · intro g a ha
    rw [← hκγ, map_sum (γ g)]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, ← hfγ, letγ_letE,
      hsub (γ g) _ (hγ g).1 (hγ g).2 (R.γ₀_X _).1 (hfπ ▸ hfγ g letπ) _ (ha _)]
  · rw [← Finset.sum_mul, sum_letE, one_mul]
    have key : ∀ k : ℕ, κ (ev c (μ k) (logS LL)) = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] ((((l : ℚ_[l]) ^ k)⁻¹) • P.tB) := by
      intro k
      induction k with
      | zero =>
        rw [tendsto_nhds_unique (hasSum_ev hc' (hμ 0) (sc_log LL)).tendsto_sum_nat hlog, hκt]
        simp
      | succ k ih =>
        have h1 := hasSum_map hc' (hμ (k + 1)) (sc_log LL) φ hφ hφc
        have h2 : φ (μ (k + 1)) = μ k := (hφb _ _).trans (by rw [frob_root])
        rw [h2] at h1
        apply frob_injective T LL
        have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
        rw [← hκφ, h1.unique (hasSum_ev hc' (hμ k) (sc_log LL)), ih, Algebra.TensorProduct.map_tmul, map_smul,
          crisFrobenius_periodT_eq_prime_smul P K, smul_smul, map_one, pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hl, mul_one]
    exact key s
  · intro i ζ ι hι hζ a ha e he m
    let π : N →+* P.R.BdR := (Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp κ
    have hπ : ∀ x, π x = Algebra.TensorProduct.productMap ι P.ιB (κ x) := fun _ => rfl
    have hπc : ∀ x, π (c x) = ι x := fun x => by rw [hπ, hκc]; simp
    have hπE : ∀ j, π (f (letE j)) = if i = j then 1 else 0 := fun j => by
      have h := GlobalTheory.T.productMap_tensorAinfToBcris_wachInclusion_constants l P AI T K s LL hG Γ R I hW β hβ i ι hι (Pi.single j 1)
      have e1 : (fun k => C ((Pi.single j 1 : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) k)) =
          (letE j : LetA ↥(OL LL) _) := by
        ext1 k
        by_cases h : k = j <;> simp [letE, h]
      rw [e1] at h
      rw [hπ, hf, hκb, h]
      by_cases h : i = j <;> simp [h]
    have hπμ : π (μ s) = P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1)) := by
      rw [hπ, hκb, hβ]
      simp
    let τ : N := c (algebraMap ℚ_[l] ↥LL.1 ((l : ℚ_[l]) ^ s)⁻¹) * t
    have hπτ : π τ = (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB := by
      rw [map_mul, hπc, AlgHom.commutes, hπ, hκt, Algebra.smul_def]
      simp
    have hev : ∀ x : ℕ → ↥LL.1, π (∑ k ∈ Finset.range m, c (x k) * τ ^ k) =
        ∑ k ∈ Finset.range m, ι (x k) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k := fun x => by
      simp only [map_sum, map_mul π, map_pow π, hπc, hπτ]
    have hlim : Tendsto (fun M : ℕ => Polynomial.eval₂ c (μ s) (trunc M (a i)) - ∑ k ∈ Finset.range m,
        c (coeff k (Polynomial.aeval (C ζ * exp ↥LL.1 - 1) (trunc M (a i)))) * τ ^ k) atTop
        (nhds (ev c (μ s) (a i) - ∑ k ∈ Finset.range m, c (coeff k e) * τ ^ k)) := by
      refine (tendsto_ev hc' (hμ s) ((conv_iff_sc _).1 (ha i))).sub (tendsto_finset_sum _ fun k _ => ?_)
      exact ((hc'.continuous.tendsto _).comp (tendsto_subtype_rng.2 (he k))).mul_const _
    have hmem := (hcl ι m).mem_of_tendsto hlim (Eventually.of_forall fun M => by
      have h := GlobalTheory.T.polynomial_teichmullerRoot_taylor_modFil l P AI T LL s ζ ι hζ (trunc M (a i)) m
      rw [Set.mem_setOf_eq, ← hπ, map_sub, hev, Polynomial.hom_eval₂, hπμ, show π.comp c = (ι : ↥LL.1 →+* P.R.BdR) from RingHom.ext hπc]
      exact h)
    rw [Set.mem_setOf_eq, ← hπ, map_sub, hev] at hmem
    have e2 : π (∑ j, f (letE j) * ev c (μ s) (a j)) = π (ev c (μ s) (a i)) := by
      simp [map_sum, map_mul π, hπE]
    rw [← hπ, e2]
    exact (Set.ext_iff.1 (P.PD_Fil _ K m) _).1 hmem

end GlobalTheory.HWL.BanachEval
