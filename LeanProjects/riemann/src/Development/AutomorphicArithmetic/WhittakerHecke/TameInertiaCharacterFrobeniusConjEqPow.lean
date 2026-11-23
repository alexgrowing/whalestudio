import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsSemisimpleInducedParam
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
import Development.DiscreteGroups.GlobalIrreducibility.DzTame
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsAddCharInvariantIffFiniteFieldAutEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

namespace UpperTheory.IrreducibleNonTameWeilDeligne

open Multiplicative

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {K : Type} [Field K]

private def eta (f : RingAut K) (ψ : Multiplicative K →* ℂˣ) (π : Ine (F := E) A →* Multiplicative K) (j : ℤ) :
    Ine (F := E) A →* ℂˣ where
  toFun t := ψ (ofAdd ((f ^ j) (toAdd (π t))))
  map_one' := by simp
  map_mul' s t := by
    rw [map_mul, toAdd_mul, map_add, ofAdd_add, map_mul]

private theorem eta_apply (f : RingAut K) (ψ : Multiplicative K →* ℂˣ) (π : Ine (F := E) A →* Multiplicative K) (j : ℤ)
    (t : Ine (F := E) A) : eta f ψ π j t = ψ (ofAdd ((f ^ j) (toAdd (π t)))) := rfl

private theorem eta_succ (f : RingAut K) (ψ : Multiplicative K →* ℂˣ) (π : Ine (F := E) A →* Multiplicative K) (j : ℤ)
    {t t' : Ine (F := E) A} (e : π t' = ofAdd (f (toAdd (π t)))) : eta f ψ π j t' = eta f ψ π (j + 1) t := by
  rw [eta_apply, eta_apply, e, toAdd_ofAdd, zpow_add_one]
  rfl

private theorem eta_eq_iff (f : RingAut K) (ψ : Multiplicative K →* ℂˣ) (π : Ine (F := E) A →* Multiplicative K)
    (hψ : ∀ m : ℤ, (∀ x, ψ (ofAdd ((f ^ m) x)) = ψ (ofAdd x)) ↔ f ^ m = 1) (hs : Function.Surjective π) (j j' : ℤ) :
    eta f ψ π j = eta f ψ π j' ↔ ((orderOf f : ℕ) : ℤ) ∣ j - j' := by
  rw [orderOf_dvd_iff_zpow_eq_one]
  constructor
  · intro e
    refine (hψ _).1 fun x => ?_
    obtain ⟨t, ht⟩ := hs (ofAdd ((f ^ (-j')) x))
    have h1 := DFunLike.congr_fun e t
    rw [eta_apply, eta_apply, ht, toAdd_ofAdd] at h1
    have e1 : (f ^ j) ((f ^ (-j')) x) = (f ^ (j - j')) x := by
      rw [sub_eq_add_neg, zpow_add]
      rfl
    have e2 : (f ^ j') ((f ^ (-j')) x) = x := by
      show (f ^ j' * f ^ (-j')) x = x
      rw [← zpow_add, add_neg_cancel, zpow_zero]
      rfl
    rwa [e1, e2] at h1
  · intro e
    have e1 : f ^ j = f ^ j' := by
      rwa [zpow_sub, mul_inv_eq_one] at e
    refine MonoidHom.ext fun t => ?_
    rw [eta_apply, eta_apply, e1]

private theorem eta_pow_card [Finite K] (f : RingAut K) (ψ : Multiplicative K →* ℂˣ) (π : Ine (F := E) A →* Multiplicative K)
    (j : ℤ) (t : Ine (F := E) A) : eta f ψ π j t ^ Nat.card K = 1 := by
  have e : Nat.card (Multiplicative K) = Nat.card K := Nat.card_congr Multiplicative.toAdd
  rw [eta_apply, ← map_pow, ← e, pow_card_eq_one', map_one]

end

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

private noncomputable def cj (h : IsPlaceOver A w) (s : Ine (F := E) A) : Ine (F := E) A :=
  ⟨(frob h : G E Ω) * s * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 s.2⟩

private theorem ineIncl_cj (h : IsPlaceOver A w) (s : Ine (F := E) A) :
    ineIncl h (cj h s) = frob h * ineIncl h s * (frob h)⁻¹ := Subtype.ext rfl

private theorem eta_eq_of_wild [Finite K] (h : IsPlaceOver A w) (n : ℕ) (f : RingAut K) (ψ : Multiplicative K →* ℂˣ)
    (π : Ine (F := E) A →* Multiplicative K) (hcard : Nat.card K = normV w ^ n) (hord : orderOf f = n)
    (hπ : ∀ t t' : Ine (F := E) A, ineIncl h t' = frob h * ineIncl h t * (frob h)⁻¹ →
      π t' = ofAdd (f (toAdd (π t))))
    (hw : ∀ t : Ine (F := E) A, Formalism.MainNotions.BlochKatoReduction.IsWild A (t : G E Ω) → eta f ψ π 0 t = eta f ψ π 1 t) :
    eta f ψ π 0 = eta f ψ π 1 := by
  set χ : Ine (F := E) A →* ℂˣ := eta f ψ π 0 / eta f ψ π 1 with hχ
  have hχa : ∀ s, χ s = eta f ψ π 0 s / eta f ψ π 1 s := fun s => rfl
  have h1 : ∀ s, χ (cj h s) = χ s ^ normV w := fun s => by
    have e := hw _ (DiscreteGroups.sglob.DzType.isWild_frob (isFrob_frob (h := h)) s)
    have e' : eta f ψ π 0 (cj h s * (s ^ normV w)⁻¹) = eta f ψ π 1 (cj h s * (s ^ normV w)⁻¹) := e
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow] at e'
    rw [hχa, hχa, div_pow, div_eq_div_iff_mul_eq_mul]
    have e2 := mul_inv_eq_iff_eq_mul.1 e'
    rw [e2]
    simp [mul_comm, mul_left_comm, mul_assoc]
  have h2 : ∀ (k : ℕ) s, χ ((cj h)^[k] s) = χ s ^ normV w ^ k ∧
      π ((cj h)^[k] s) = ofAdd ((f ^ k) (toAdd (π s))) := fun k s => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', h1, ih.1, hπ _ _ (ineIncl_cj h _), ih.2, toAdd_ofAdd, pow_succ' f k]
      exact ⟨by rw [← pow_mul, pow_succ], rfl⟩
  have h3 : ∀ s s', π s = π s' → χ s = χ s' := fun s s' e => by
    rw [hχa, hχa, eta_apply, eta_apply, eta_apply, eta_apply, e]
  have h4 : ∀ s, χ s = 1 := fun s => by
    obtain ⟨e1, e2⟩ := h2 n s
    have e3 : π ((cj h)^[n] s) = π s := by
      rw [e2, ← hord, pow_orderOf_eq_one]
      rfl
    rw [h3 _ _ e3, ← hcard, hχa, div_pow, eta_pow_card, eta_pow_card, div_one] at e1
    exact e1
  exact MonoidHom.ext fun s => div_eq_one.1 (h4 s)

end

end UpperTheory.IrreducibleNonTameWeilDeligne

open UpperTheory.IrreducibleNonTameWeilDeligne Multiplicative in
theorem UpperTheory.tameInertiaCharacter_frobenius_conj_eq_pow :
    ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
        {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (n : ℕ), 2 ≤ n → ∀ (K : Type) [Field K] [Finite K] (f : RingAut K)
        (π : Ine (F := E) A →* Multiplicative K), Nat.card K = normV w ^ n → orderOf f = n → Function.Surjective π →
        IsOpen (π.ker : Set (Ine (F := E) A)) →
        (∀ t t' : Ine (F := E) A, ineIncl h t' = frob h * ineIncl h t * (frob h)⁻¹ →
          π t' = Multiplicative.ofAdd (f (Multiplicative.toAdd (π t)))) →
        ∃ J : WD h, IsIrrWD J ∧ J.lpDim = n ∧ (∀ σ, ‖(J.eig σ).prod‖ = 1) ∧
          ∀ (V : WD h) ξ hξ, IsTameWD V → J ≠ V.lpTwist ξ hξ := by
  intro E Ω _ _ _ _ _ A w h n hn K _ _ f π hcard hord hs ho hπ
  obtain ⟨ψ, hψ⟩ := UpperTheory.exists_addChar_invariant_iff_finiteField_aut_eq_one K f
  have bindC : ∀ m : Multiset ℂˣ, (do let x ← m; pure (x : ℂ) : Multiset ℂ) = m.map fun z : ℂˣ => (z : ℂ) :=
    fun m => Multiset.bind_singleton _ _
  have hiff : ∀ j j' : ℤ, eta f ψ π j = eta f ψ π j' ↔ (n : ℤ) ∣ j - j' := fun j j' => by
    rw [← hord]
    exact eta_eq_iff f ψ π hψ hs j j'
  have hopen : IsOpen ((eta f ψ π 0).ker : Set (Ine (F := E) A)) := by
    refine Subgroup.isOpen_mono (H₁ := π.ker) (fun t ht => ?_) ho
    rw [MonoidHom.mem_ker] at ht ⊢
    rw [eta_apply, ht]
    simp
  obtain ⟨J, hirr, hdim, hdet, hine, -⟩ := UpperTheory.Zero.LLC.indEx E Ω A w h (frob h) deg_frob n (by omega) (eta f ψ π) hopen
    (fun j t t' e => eta_succ f ψ π j (hπ t t' e)) hiff 1 one_ne_zero
  refine ⟨J, hirr, hdim, fun σ => ?_, fun V ξ hξ hV he => ?_⟩
  · obtain ⟨⟨δ, hδ⟩, -, -, -, -, -, -, hcl, -⟩ := UpperTheory.Zero.LLC.wDBasic E Ω A w h J
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    have hφ : δ (frob h) = 1 := Units.ext (by rw [← hδ, hdet]; rfl)
    have hm : J.inePol (τ : G E Ω) =
        (((Finset.range n).val.map fun j : ℕ => eta f ψ π j τ).map fun z : ℂˣ => X - C (z : ℂ)).prod := by
      rw [hine τ, Multiset.map_map]
      rfl
    have h1 := (hcl τ ((Finset.range n).val.map fun j : ℕ => eta f ψ π j τ) (by rw [bindC, Multiset.map_map]; exact hm)).1
    have h2 : δ (ineIncl h τ) ^ Nat.card K = 1 := by
      have e : δ (ineIncl h τ) = ∏ j ∈ Finset.range n, eta f ψ π j τ := Units.ext (by rw [← hδ, h1]; rfl)
      rw [e, ← Finset.prod_pow]
      exact Finset.prod_eq_one fun j _ => eta_pow_card f ψ π j τ
    have h3 : δ σ = δ (ineIncl h τ) := by
      conv_lhs => rw [hτ]
      rw [map_mul, map_zpow, hφ, one_zpow, one_mul]
    rw [hδ, h3]
    refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card K) ?_ Nat.card_pos.ne'
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  · obtain ⟨t, htw, hne⟩ : ∃ t : Ine (F := E) A, Formalism.MainNotions.BlochKatoReduction.IsWild A (t : G E Ω) ∧ eta f ψ π 0 t ≠ eta f ψ π 1 t := by
      by_contra hall
      push_neg at hall
      have e := (hiff 0 1).1 (eta_eq_of_wild h n f ψ π hcard hord hπ hall)
      have e2 := Int.le_of_dvd (by norm_num) ((dvd_neg).2 e)
      norm_num at e2
      omega
    obtain ⟨m, b, hb, hb1⟩ := hV
    have hbt : b.ρ (ineIncl h t) = 1 := hb1 _ htw
    have hVp : V.inePol (t : G E Ω) = ((Multiset.replicate m (1 : ℂˣ)).map fun z : ℂˣ => X - C (z : ℂ)).prod := by
      rw [WD.inePol_of_mem_Ine V t.2, ← hb, WD.charPol_mk]
      show (b.ρ (ineIncl h t)).charpoly = _
      rw [hbt, LinearMap.charpoly_one]
      simp
    obtain ⟨-, -, -, -, -, -, -, hcl, -⟩ := UpperTheory.Zero.LLC.wDBasic E Ω A w h V
    have h3 := (hcl t (Multiset.replicate m (1 : ℂˣ)) (by rw [bindC, Multiset.map_map]; exact hVp)).2.2 ξ hξ
    rw [← he, hine t] at h3
    have hroot : ∀ j ∈ Finset.range n, eta f ψ π j t = ξ (ineIncl h t) := fun j hj => by
      have e := congrArg (eval ((eta f ψ π j t : ℂˣ) : ℂ)) h3
      rw [eval_prod, Finset.prod_eq_zero hj (by simp)] at e
      simp at e
      have e0 : ((eta f ψ π j t : ℂˣ) : ℂ) - (ξ (ineIncl h t) : ℂˣ) = 0 :=
        eq_zero_of_pow_eq_zero e.symm
      exact Units.ext (sub_eq_zero.1 e0)
    exact hne (by simpa using (hroot 0 (by simp; omega)).trans (hroot 1 (by simp; omega)).symm)
