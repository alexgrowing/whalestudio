import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreSemilocalCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractRelevant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Scale

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R T : Type*} [CommRing R] [CommRing T]

theorem prod_pow_blockWeight (t : K → T) (d : (Σ k, ι k) →₀ ℕ) :
    ∏ k, t k ^ (Finsupp.weight (blockWeight ι) d k) = ∏ s ∈ d.support, t s.1 ^ d s := by
  rw [Finsupp.weight_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, smul_eq_mul]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Finset.prod_eq_single s.1 (fun k _ hk => by simp [hk]) (by simp)]
  simp

theorem eval₂_blockScale (f : R →+* T) (t : K → T) (a : (Σ k, ι k) → T) {F : MRing ι R} {b : K → ℕ}
    (hF : IsMultiHomog F b) :
    eval₂ f (fun s => t s.1 * a s) F = (∏ k, t k ^ b k) * eval₂ f a F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (blockWeight ι) d = b := hF (mem_support_iff.mp hd)
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [← hw, prod_pow_blockWeight]
  ring

variable {κ : Type*} [CommRing κ]

theorem eval₂_blockVar_of_isMultiHomog (g : R →+* κ) (c : (Σ k, ι k) → κ) {F : MRing ι R} {b : K → ℕ}
    (hF : IsMultiHomog F b) :
    eval₂ ((C : κ →+* MvPolynomial K κ).comp g) (fun s => X s.1 * C (c s)) F =
      monomial (Finsupp.equivFunOnFinite.symm b) (eval₂ g c F) := by
  rw [eval₂_blockScale _ _ _ hF]
  have h1 : eval₂ ((C : κ →+* MvPolynomial K κ).comp g) (fun s => C (c s)) F = C (eval₂ g c F) :=
    (eval₂_comp_left C g c F).symm
  rw [h1, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  ring

theorem eval₂_blockVar_component (g : R →+* κ) (c : (Σ k, ι k) → κ) (F : MRing ι R) (b : K → ℕ) :
    eval₂ ((C : κ →+* MvPolynomial K κ).comp g) (fun s => X s.1 * C (c s))
        (weightedHomogeneousComponent (blockWeight ι) b F) =
      monomial (Finsupp.equivFunOnFinite.symm b)
        (coeff (Finsupp.equivFunOnFinite.symm b)
          (eval₂ ((C : κ →+* MvPolynomial K κ).comp g) (fun s => X s.1 * C (c s)) F)) := by
  induction F using MvPolynomial.induction_on' with
  | monomial d r =>
    have hd : IsMultiHomog (monomial d r : MRing ι R) (Finsupp.weight (blockWeight ι) d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    rw [eval₂_blockVar_of_isMultiHomog g c hd, coeff_monomial]
    by_cases h : Finsupp.weight (blockWeight ι) d = b
    · subst h
      rw [hd.weightedHomogeneousComponent_same, eval₂_blockVar_of_isMultiHomog g c hd, if_pos rfl]
    · have h0 : weightedHomogeneousComponent (blockWeight ι) b (monomial d r : MRing ι R) = 0 := by
        rw [weightedHomogeneousComponent_of_mem (p := (monomial d r : MRing ι R))
          (n := Finsupp.weight (blockWeight ι) d) hd, if_neg (Ne.symm h)]
      rw [h0, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h')), eval₂_zero, map_zero]
  | add p q hp hq =>
    rw [map_add, eval₂_add, hp, hq, eval₂_add, coeff_add, map_add]

theorem eval₂_blockVar_eq_zero_iff (g : R →+* κ) (c : (Σ k, ι k) → κ) (F : MRing ι R) :
    eval₂ ((C : κ →+* MvPolynomial K κ).comp g) (fun s => X s.1 * C (c s)) F = 0 ↔
      ∀ b, eval₂ ((C : κ →+* MvPolynomial K κ).comp g) (fun s => X s.1 * C (c s))
        (weightedHomogeneousComponent (blockWeight ι) b F) = 0 := by
  refine ⟨fun h b => by rw [eval₂_blockVar_component, h, coeff_zero, map_zero], fun h => ?_⟩
  ext d
  have := h (Finsupp.equivFunOnFinite d)
  rw [eval₂_blockVar_component, Equiv.symm_apply_apply, monomial_eq_zero] at this
  rw [this, coeff_zero]

end Scale

section Centre

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} [Fintype J] {O : Type u} [CommRing O]

theorem exists_blowUp_centre (P W : Ideal (MRing ι O)) [P.IsPrime] (hPh : IsMultiHomogIdeal P)
    (hW : W.IsPrime) (hPW : P ≤ W) (hWrel : IsRelevant W) (N : K → ℕ) (u : J → MRing ι O)
    (hu : ∀ j, IsMultiHomog (u j) N) (hu' : ∃ j, u j ∉ P)
    (V : ValuationSubring (FractionRing (MRing ι O ⧸ P))) (hAV : homLocRing P W ≤ V.toSubring) :
    ∃ W' : Ideal (MRing (extIdx ι J) O),
      W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
        W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W ∧ blowUpLocRing P u W' ≤ V.toSubring := by
  classical
  set L := FractionRing (MRing ι O ⧸ P)
  let τ : MRing (extIdx ι J) O →+* L := (algebraMap (MRing ι O ⧸ P) L).comp (blowUpEval P u)
  let q : MRing ι O →+* L := (algebraMap (MRing ι O ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hτl : ∀ f, τ (liftForm f) = q f := fun f => by
    simp only [τ, q, RingHom.comp_apply, blowUpEval_liftForm]
  have hτX : ∀ (k : K) (i : ι k), τ (X ⟨some k, i⟩) = q (X ⟨k, i⟩) := fun k i => by
    rw [← hτl, liftForm_X]
  have hτY : ∀ l : J, τ (X ⟨none, l⟩) = q (u l) := fun l => by
    simp [τ, q, blowUpEval, blowUpSubst]
  have hq0 : ∀ f, q f = 0 ↔ f ∈ P := fun f => by
    simp only [q, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have hAgen : ∀ (b : K → ℕ) (f g : MRing ι O), IsMultiHomog f b → IsMultiHomog g b → g ∉ W →
      q f / q g ∈ V := fun b f g hf hg hgW => hAV (Subring.subset_closure ⟨b, f, g, hf, hg, hgW, rfl⟩)
  choose ik hik using hWrel
  obtain ⟨j, hjP, hjmax⟩ : ∃ j, u j ∉ P ∧ ∀ l, u l ∉ P → V.valuation (q (u l)) ≤ V.valuation (q (u j)) := by
    obtain ⟨j₀, hj₀⟩ := hu'
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun j => u j ∉ P)
      (fun j => V.valuation (q (u j))) ⟨j₀, by simpa using hj₀⟩
    exact ⟨j, (Finset.mem_filter.mp hj).2, fun l hl => hmax l (by simpa using hl)⟩
  let e : (o : Option K) → extIdx ι J o := fun o =>
    match o with
    | none => j
    | some k => ik k
  let t : Option K → L := fun o => τ (X ⟨o, e o⟩)
  have ht : ∀ o, t o ≠ 0 := by
    rintro (_ | k)
    · show τ (X ⟨none, j⟩) ≠ 0
      rw [hτY, Ne, hq0]
      exact hjP
    · show τ (X ⟨some k, ik k⟩) ≠ 0
      rw [hτX, Ne, hq0]
      exact fun h => hik k (hPW h)
  let a : (Σ o, extIdx ι J o) → L := fun s => τ (X s) / t s.1
  have ha : ∀ s, a s ∈ V := by
    rintro ⟨_ | k, i⟩
    · show τ (X ⟨none, i⟩) / τ (X ⟨none, j⟩) ∈ V
      rw [show τ (X ⟨none, i⟩) = q (u i) from hτY i, hτY]
      by_cases hi : u i ∈ P
      · rw [(hq0 _).2 hi, zero_div]
        exact V.zero_mem
      · refine V.mem_of_valuation_le_one _ ?_
        rw [map_div₀]
        have hj0 : V.valuation (q (u j)) ≠ 0 := by
          rw [Ne, Valuation.zero_iff, hq0]
          exact hjP
        exact (div_le_one₀ (zero_lt_iff.2 hj0)).2 (hjmax i hi)
    · show τ (X ⟨some k, i⟩) / τ (X ⟨some k, ik k⟩) ∈ V
      rw [show τ (X ⟨some k, i⟩) = q (X ⟨k, i⟩) from hτX k i, hτX]
      exact hAgen (Pi.single k 1) _ _ (isWeightedHomogeneous_X _ _ _) (isWeightedHomogeneous_X _ _ _) (hik k)
  have hC : ∀ r, (τ.comp C) r ∈ V := fun r => by
    have h := hAgen 0 (C r) 1 (isWeightedHomogeneous_C _ _) (isWeightedHomogeneous_one _ _)
      (fun h => hW.ne_top ((Ideal.eq_top_iff_one _).2 h))
    rw [map_one, div_one] at h
    rwa [RingHom.comp_apply, ← liftForm_C, hτl]
  let cV : O →+* V := (τ.comp C).codRestrict V hC
  let aV : (Σ o, extIdx ι J o) → V := fun s => ⟨a s, ha s⟩
  let ψV : MRing (extIdx ι J) O →+* V := eval₂Hom cV aV
  have hψ : ∀ F, (ψV F : L) = eval₂ (τ.comp C) a F := fun F => by
    have h := eval₂_comp_left V.subtype cV aV F
    exact h
  have hτψ : ∀ F b, IsMultiHomog F b → τ F = (∏ o, t o ^ b o) * ψV F := by
    intro F b hF
    rw [hψ, ← eval₂_blockScale _ t a hF]
    have h1 : (fun s : (Σ o, extIdx ι J o) => t s.1 * a s) = τ ∘ X :=
      funext fun s => mul_div_cancel₀ _ (ht s.1)
    rw [h1]
    conv_lhs => rw [← eval₂_eta F]
    exact eval₂_comp_left τ C X F
  have hM : ∀ b : Option K → ℕ, (∏ o, t o ^ b o) ≠ 0 := fun b =>
    Finset.prod_ne_zero_iff.2 fun o _ => pow_ne_zero _ (ht o)
  let ρ : V →+* IsLocalRing.ResidueField V := IsLocalRing.residue V
  let Φ : MRing (extIdx ι J) O →+* MvPolynomial (Option K) (IsLocalRing.ResidueField V) :=
    eval₂Hom ((C : IsLocalRing.ResidueField V →+* _).comp (ρ.comp cV)) (fun s => X s.1 * C (ρ (aV s)))
  have hΦhom : ∀ F b, IsMultiHomog F b → Φ F = monomial (Finsupp.equivFunOnFinite.symm b) (ρ (ψV F)) := by
    intro F b hF
    have h := eval₂_blockVar_of_isMultiHomog (ρ.comp cV) (fun s => ρ (aV s)) hF
    have h2 : eval₂ (ρ.comp cV) (fun s => ρ (aV s)) F = ρ (ψV F) := (eval₂_comp_left ρ cV aV F).symm
    rw [h2] at h
    exact h
  have hmem : ∀ F b, IsMultiHomog F b → (F ∈ RingHom.ker Φ ↔ ψV F ∈ IsLocalRing.maximalIdeal V) := by
    intro F b hF
    rw [RingHom.mem_ker, hΦhom F b hF, monomial_eq_zero, IsLocalRing.residue_eq_zero_iff]
  have hker : ∀ F, F ∈ RingHom.ker Φ ↔
      ∀ b, weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F ∈ RingHom.ker Φ := fun F => by
    simp only [RingHom.mem_ker]
    exact eval₂_blockVar_eq_zero_iff (ρ.comp cV) (fun s => ρ (aV s)) F
  refine ⟨RingHom.ker Φ, RingHom.ker_isPrime Φ, fun F hF b => (hker F).1 hF b, ?_, ?_, ?_, ?_⟩
  ·
    intro o
    refine ⟨e o, ?_⟩
    have h1 : aV ⟨o, e o⟩ = 1 := Subtype.ext (div_self (ht o))
    rw [RingHom.mem_ker]
    simp only [Φ, eval₂Hom_X', h1, map_one, mul_one]
    exact X_ne_zero _
  ·
    intro F hF
    rw [hker]
    intro b
    have hFb := isMultiHomogIdeal_blowUpOf hPh N u hu F hF b
    have hh := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight (extIdx ι J)) b F
    rw [hmem _ b hh]
    have h0 : τ (weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F) = 0 := by
      show algebraMap _ L (Polynomial.eval 1 (aeval (blowUpSubst P u) _)) = 0
      rw [(RingHom.mem_ker).mp hFb, Polynomial.eval_zero, map_zero]
    rw [hτψ _ b hh, mul_eq_zero] at h0
    have h0' : ψV (weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F) = 0 :=
      Subtype.ext (h0.resolve_left (hM b))
    rw [h0']
    exact Ideal.zero_mem _
  ·
    intro f hf
    rw [Ideal.mem_comap, hker] at hf
    suffices hc : ∀ c, weightedHomogeneousComponent (blockWeight ι) c f ∈ W by
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun c _ => hc c
    intro c
    by_contra hcW
    set fc := weightedHomogeneousComponent (blockWeight ι) c f
    have hfc : IsMultiHomog fc c := weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hlift : weightedHomogeneousComponent (blockWeight (extIdx ι J)) (liftMDeg c) (liftForm f) =
        liftForm fc := by
      have h := FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent
        (ι := ι) (ι' := extIdx ι J) (j := some) (g := fun v => (⟨some v.1, v.2⟩ : Σ o, extIdx ι J o))
        (fun _ => rfl) (Option.some_injective K)
        (fun v w h => Sigma.ext (Option.some_injective _ (congrArg Sigma.fst h))
          (Sigma.mk.inj_iff.mp h).2) (R := O) c f
      have hext : Function.extend some c 0 = liftMDeg c := by
        funext o
        cases o with
        | none =>
          rw [Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ => Option.some_ne_none k hk)]
          rfl
        | some k => rw [(Option.some_injective K).extend_apply]; rfl
      rw [hext] at h
      exact h.symm
    have h1 := hf (liftMDeg c)
    rw [hlift, hmem _ _ (isMultiHomog_liftForm hfc)] at h1
    have hM' : (∏ o, t o ^ liftMDeg c o) = q (powMonomial c ik) := by
      rw [Fintype.prod_option]
      simp only [liftMDeg, Option.elim, pow_zero, one_mul, powMonomial, map_prod, map_pow]
      refine Finset.prod_congr rfl fun k _ => ?_
      show τ (X ⟨some k, ik k⟩) ^ c k = _
      rw [hτX]
    have hpm : powMonomial c ik ∉ W := fun h =>
      (W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hik k) _ : powMonomial c ik ∈ W.primeCompl) h
    have hinv := hAgen c _ _ (isMultiHomog_powMonomial c ik) hfc hcW
    have hqf : q fc ≠ 0 := fun h => hcW (hPW ((hq0 _).1 h))
    have hqm : q (powMonomial c ik) ≠ 0 := fun h => hpm (hPW ((hq0 _).1 h))
    have heq := hτψ _ _ (isMultiHomog_liftForm hfc)
    rw [hτl, hM'] at heq
    have hψ0 : (ψV (liftForm fc) : L) ≠ 0 := fun h => hqf (by rw [heq, h, mul_zero])
    have key : (ψV (liftForm fc) : L) * (q (powMonomial c ik) / q fc) = 1 := by
      rw [heq]
      field_simp
    have hunit : IsUnit (ψV (liftForm fc)) := IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext key)
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 hunit
  ·
    refine Subring.closure_le.2 ?_
    rintro z ⟨b, F, G, hF, hG, hGW', rfl⟩
    show τ F / τ G ∈ V
    rw [hτψ F b hF, hτψ G b hG, mul_div_mul_left _ _ (hM b)]
    have hG' : IsUnit (ψV G) := by
      by_contra hnu
      exact hGW' ((hmem G b hG).2 ((IsLocalRing.mem_maximalIdeal _).2 hnu))
    refine V.mem_of_valuation_le_one _ ?_
    rw [map_div₀, (V.valuation_eq_one_iff _).1 hG', div_one]
    exact V.valuation_le_one _

end Centre

end

end GroundTheory.Heights₂.Heights.NumbersDVR
