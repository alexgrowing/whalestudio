import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IdemCases

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

set_option linter.deprecated false

theorem card_QE (h : IsCMExt F E σ) [Finite (𝓞 F ⧸ v.asIdeal)] :
    Nat.card (QE (E := E) v) = Nat.card (𝓞 F ⧸ v.asIdeal) ^ 2 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hr : Module.finrank (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) = 2 := by
    rw [← h.2.2.1]
    exact Ideal.finrank_quotient_map v.asIdeal F E
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) :=
    Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  haveI : Finite (QE (E := E) v) := Module.finite_of_finite (𝓞 F ⧸ v.asIdeal)
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  letI := Fintype.ofFinite (QE (E := E) v)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := QE (E := E) v), hr]

def gP (P : Ideal (𝓞 E)) (hP : IE (E := E) v ≤ P) : 𝓞 F ⧸ v.asIdeal →+* 𝓞 E ⧸ P :=
  Ideal.quotientMap P (algebraMap (𝓞 F) (𝓞 E)) (Ideal.map_le_iff_le_comap.1 hP)

theorem bij_of_card {A B : Type} [Finite A] [Finite B] (f : A → B) (hf : Function.Injective f)
    (hc : Nat.card A = Nat.card B) : Function.Bijective f := by
  exact hf.bijective_of_nat_card_le hc.ge

theorem qProd_holds : QProd σ J ψ v := by
  intro hS hU hnp
  have hcm : IsCMExt F E σ := hS.1
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hI : IE (E := E) v ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  set ι := (UniqueFactorizationMonoid.factors (IE (E := E) v)).toFinset with hι
  have hmem : ∀ P : ι, (P : Ideal (𝓞 E)) ∈ UniqueFactorizationMonoid.factors (IE (E := E) v) :=
    fun P => Multiset.mem_toFinset.mp P.2
  have hprime : ∀ P : ι, (P : Ideal (𝓞 E)).IsPrime :=
    fun P => Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_factor _ (hmem P))
  have hne : ∀ P : ι, (P : Ideal (𝓞 E)) ≠ ⊥ :=
    fun P => (UniqueFactorizationMonoid.prime_of_factor _ (hmem P)).ne_zero
  have hle : ∀ P : ι, IE (E := E) v ≤ (P : Ideal (𝓞 E)) :=
    fun P => Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors (hmem P))
  have hcomap : ∀ P : ι,
      Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (P : Ideal (𝓞 E)) = v.asIdeal := by
    intro P
    haveI := hprime P
    exact (v.isMaximal.eq_of_le (Ideal.IsPrime.comap _).ne_top
      (Ideal.map_le_iff_le_comap.mp (hle P))).symm
  have hcount : ∀ P : ι, (P : Ideal (𝓞 E)) ^ Multiset.count (P : Ideal (𝓞 E))
      (UniqueFactorizationMonoid.factors (IE (E := E) v)) = P := by
    intro P
    haveI := hprime P
    haveI : (P : Ideal (𝓞 E)).LiesOver v.asIdeal := ⟨(hcomap P).symm⟩
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count v.asIdeal (P : Ideal (𝓞 E)) hI,
      hU P (hprime P) (hne P) (hcomap P), pow_one]
  let eqv : QE (E := E) v ≃+* ∀ P : ι, 𝓞 E ⧸ (P : Ideal (𝓞 E)) :=
    (IsDedekindDomain.quotientEquivPiFactors hI).trans
      (RingEquiv.piCongrRight fun P => Ideal.quotEquivOfEq (hcount P))
  have heqv : ∀ (y : 𝓞 E) (P : ι), eqv (Ideal.Quotient.mk _ y) P = Ideal.Quotient.mk _ y :=
    fun y P => rfl
  haveI hfinE : ∀ P : ι, Finite (𝓞 E ⧸ (P : Ideal (𝓞 E))) :=
    fun P => Ideal.finiteQuotientOfFreeOfNeBot _ (hne P)
  haveI : Finite (QE (E := E) v) := Finite.of_equiv _ eqv.symm.toEquiv
  have hinj : ∀ P : ι, Function.Injective (gP v (P : Ideal (𝓞 E)) (hle P)) := by
    intro P
    haveI := hprime P
    exact (gP v _ (hle P)).injective
  set q := Nat.card (𝓞 F ⧸ v.asIdeal) with hq
  have hq2 : 1 < q := Finite.one_lt_card
  have hcardP : ∀ P : ι, q ≤ Nat.card (𝓞 E ⧸ (P : Ideal (𝓞 E))) :=
    fun P => Nat.card_le_card_of_injective _ (hinj P)
  have hprod : ∏ P : ι, Nat.card (𝓞 E ⧸ (P : Ideal (𝓞 E))) = q ^ 2 := by
    rw [← Nat.card_pi, ← Nat.card_congr eqv.toEquiv, card_QE σ v hcm]
  have hn : Fintype.card ι = 2 := by
    have hpow : q ^ Fintype.card ι ≤ q ^ 2 := by
      rw [← hprod]
      calc q ^ Fintype.card ι = ∏ _P : ι, q := by rw [Finset.prod_const, Finset.card_univ]
        _ ≤ _ := Finset.prod_le_prod' fun P _ => hcardP P
    rcases Nat.lt_or_ge (Fintype.card ι) 2 with hlt | hge
    · exfalso
      interval_cases hc : Fintype.card ι
      · haveI := Fintype.card_eq_zero_iff.mp hc
        rw [Finset.univ_eq_empty, Finset.prod_empty] at hprod
        nlinarith
      · obtain ⟨P0, hP0⟩ := Fintype.card_eq_one_iff.mp hc
        apply hnp
        haveI := hprime P0
        have h0 : ∀ z : 𝓞 E, z ∈ IE (E := E) v ↔
            Ideal.Quotient.mk (P0 : Ideal (𝓞 E)) z = 0 := by
          intro z
          rw [← Ideal.Quotient.eq_zero_iff_mem (I := IE (E := E) v)]
          constructor
          · intro hz
            have := congrArg (fun w => eqv w P0) hz
            simpa only [heqv, map_zero, Pi.zero_apply] using this
          · intro hz
            apply eqv.injective
            rw [map_zero]
            funext P
            obtain rfl := hP0 P
            rw [heqv, hz, Pi.zero_apply]
        rw [Ideal.isPrime_iff]
        refine ⟨fun h => (hprime P0).ne_top (top_le_iff.mp (h ▸ hle P0)), ?_⟩
        intro x y hxy
        rw [h0, map_mul] at hxy
        rw [h0, h0]
        exact mul_eq_zero.mp hxy
    · by_contra hne2
      have h3 : 3 ≤ Fintype.card ι := by omega
      have h4 : q ^ 3 ≤ q ^ Fintype.card ι := Nat.pow_le_pow_right (by omega) h3
      have h5 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right hq2 (by norm_num)
      linarith
  let eι := Fintype.equivFinOfCardEq hn
  have hfin2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  have hall : ∀ P : ι, P = eι.symm 0 ∨ P = eι.symm 1 := by
    intro P
    rcases hfin2 (eι P) with h | h
    · left; rw [← h, Equiv.symm_apply_apply]
    · right; rw [← h, Equiv.symm_apply_apply]
  have hprod2 : Nat.card (𝓞 E ⧸ ((eι.symm 0 : ι) : Ideal (𝓞 E))) *
      Nat.card (𝓞 E ⧸ ((eι.symm 1 : ι) : Ideal (𝓞 E))) = q ^ 2 := by
    rw [← hprod, ← eι.symm.prod_comp, Fin.prod_univ_two]
  have hc0 := hcardP (eι.symm 0)
  have hc1 := hcardP (eι.symm 1)
  have hcq : ∀ P : ι, Nat.card (𝓞 E ⧸ (P : Ideal (𝓞 E))) = q := by
    intro P
    rcases hall P with rfl | rfl
    · nlinarith
    · nlinarith
  let eP : ∀ P : ι, (𝓞 F ⧸ v.asIdeal) ≃+* 𝓞 E ⧸ (P : Ideal (𝓞 E)) := fun P =>
    RingEquiv.ofBijective (gP v _ (hle P)) (bij_of_card _ (hinj P) (hcq P).symm)
  let φ : QE (E := E) v →+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) :=
    RingHom.prod
      (((eP (eι.symm 0)).symm : _ →+* _).comp
        ((Pi.evalRingHom (fun P : ι => 𝓞 E ⧸ (P : Ideal (𝓞 E))) (eι.symm 0)).comp
          (eqv : QE (E := E) v →+* _)))
      (((eP (eι.symm 1)).symm : _ →+* _).comp
        ((Pi.evalRingHom (fun P : ι => 𝓞 E ⧸ (P : Ideal (𝓞 E))) (eι.symm 1)).comp
          (eqv : QE (E := E) v →+* _)))
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h0 : eqv a (eι.symm 0) = eqv b (eι.symm 0) :=
      (eP (eι.symm 0)).symm.injective (congrArg Prod.fst hab)
    have h1 : eqv a (eι.symm 1) = eqv b (eι.symm 1) :=
      (eP (eι.symm 1)).symm.injective (congrArg Prod.snd hab)
    apply eqv.injective
    funext P
    rcases hall P with rfl | rfl
    · exact h0
    · exact h1
  have hbij : Function.Bijective φ :=
    bij_of_card φ hφinj (by rw [Nat.card_prod, card_QE σ v hcm, sq])
  refine ⟨RingEquiv.ofBijective φ hbij, fun c => ?_⟩
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  have h1 := Ideal.Quotient.algebraMap_quotient_map_quotient (S := 𝓞 E) (p := v.asIdeal) f
  rw [RingEquiv.ofBijective_apply]
  refine Prod.ext ?_ ?_
  · show (eP (eι.symm 0)).symm (eqv (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)
      (Ideal.Quotient.mk v.asIdeal f)) (eι.symm 0)) = _
    rw [RingEquiv.symm_apply_eq]
    rw [show algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk v.asIdeal f) =
      Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) f) from h1, heqv]
    rfl
  · show (eP (eι.symm 1)).symm (eqv (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)
      (Ideal.Quotient.mk v.asIdeal f)) (eι.symm 1)) = _
    rw [RingEquiv.symm_apply_eq]
    rw [show algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk v.asIdeal f) =
      Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) f) from h1, heqv]
    rfl

theorem qSplit_holds : QSplit σ J ψ v := qSplit_of σ J ψ v (qProd_holds σ J ψ v)

private theorem sigma_sigma_eq_of_isCMExt (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hc⟩ := h
  let τ : E →+* ℂ := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
  apply τ.injective
  rw [hc, hc, star_star]

theorem resAlg_of' (hQ : ResQ σ J ψ v) (hE : EtaLink σ J ψ v) : ResAlg σ J ψ v := by
  intro hS hU ϖ hϖ
  have hcm : IsCMExt F E σ := hS.1
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  obtain ⟨ρ, hρ⟩ := hQ hS hU ϖ hϖ
  have hη : etaV (E := E) v = 1 ∨ etaV (E := E) v = -1 := by
    unfold etaV
    split_ifs <;> simp
  have hlink := hE hS hU
  have hcardk : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨𝓞 F ⧸ v.asIdeal, inferInstance, inferInstance, hcardk, ?_⟩
  by_cases hp : (IE (E := E) v).IsPrime
  · left
    have hm1 : etaV (E := E) v = -1 := by
      rcases hη with h | h
      · exact absurd hp (hlink.mp h)
      · exact h
    refine ⟨hm1, ?_⟩
    haveI : (IE (E := E) v).IsMaximal := hp.isMaximal (Ideal.map_ne_bot_of_ne_bot v.ne_bot)
    letI : Field (QE (E := E) v) := Ideal.Quotient.field _
    have hinv : ∀ z, sigQ σ v (sigQ σ v z) = z := by
      intro z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      simp only [sigQ, Ideal.quotientMap_mk]
      congr 1
      apply RingOfIntegers.ext
      exact sigma_sigma_eq_of_isCMExt σ hcm (y : E)
    have hfixc : ∀ c, sigQ σ v (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c) =
        algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c := by
      intro c
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
      have h1 := Ideal.Quotient.algebraMap_quotient_map_quotient (S := 𝓞 E) (p := v.asIdeal) f
      have h2 : sigO σ (algebraMap (𝓞 F) (𝓞 E) f) = algebraMap (𝓞 F) (𝓞 E) f := by
        apply RingOfIntegers.ext
        exact σ.commutes (f : F)
      calc sigQ σ v (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk v.asIdeal f))
          = sigQ σ v (Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) f)) := congrArg _ h1
        _ = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) f) := by
            simp only [sigQ, Ideal.quotientMap_mk, h2]
        _ = _ := h1.symm
    let s : QE (E := E) v ≃ₐ[𝓞 F ⧸ v.asIdeal] QE (E := E) v :=
      { sigQ σ v with
        invFun := sigQ σ v
        left_inv := hinv
        right_inv := hinv
        commutes' := hfixc }
    have hr : Module.finrank (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) = 2 := by
      rw [← hcm.2.2.1]
      exact Ideal.finrank_quotient_map v.asIdeal F E
    refine ⟨QE (E := E) v, inferInstance, inferInstance, s, ρ, fun x => hinv x, hr, ?_, hρ⟩
    intro hs
    have hfix : ∀ x, sigQ σ v x = x := fun x => AlgEquiv.ext_iff.mp hs x
    have hsq : ∀ x : QE (E := E) v, ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x * x :=
      fun x => sq_mem σ v hcm x (hfix x)
    have hall : ∀ x : QE (E := E) v, ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x := by
      by_cases h2 : (2 : QE (E := E) v) = 0
      · haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) :=
          Module.finite_of_finrank_pos (by rw [hr]; norm_num)
        haveI : Finite (QE (E := E) v) := Module.finite_of_finite (𝓞 F ⧸ v.asIdeal)
        have hinjsq : Function.Injective (fun y : QE (E := E) v => y * y) := by
          intro a b hab
          have hab' : a * a = b * b := hab
          have h3 : (a - b) * (a - b) = 0 := by
            have e1 : (a - b) * (a - b) = a * a - b * b - 2 * b * (a - b) := by ring
            rw [e1, hab', h2]
            ring
          exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
        intro x
        obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hinjsq x
        obtain ⟨c, hc⟩ := hsq y
        exact ⟨c, hc.trans hy⟩
      · intro x
        obtain ⟨c0, hc0⟩ := hsq x
        obtain ⟨c1, hc1⟩ := hsq (x + 1)
        refine ⟨(c1 - c0 - 1) * 2⁻¹, ?_⟩
        have hx2 : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (c1 - c0 - 1) = 2 * x := by
          rw [map_sub, map_sub, map_one, hc0, hc1]
          ring
        rw [map_mul, map_inv₀, hx2, map_ofNat, mul_comm]
        exact inv_mul_cancel_left₀ h2 x
    have hle1 : Module.finrank (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) ≤ 1 :=
      finrank_le_one (1 : QE (E := E) v) (fun w => by
        obtain ⟨c, hc⟩ := hall w
        exact ⟨c, by rw [← Algebra.algebraMap_eq_smul_one, hc]⟩)
    omega
  · right
    refine ⟨hlink.mpr hp, ?_⟩
    obtain ⟨e, he⟩ := qSplit_holds σ J ψ v hS hU hp
    refine ⟨(e : QE (E := E) v →+* _).comp ρ, ?_, ?_, ?_⟩
    · exact e.surjective.comp hρ.1
    · intro x
      rw [← hρ.2.1 x]
      show e (ρ x) = 0 ↔ ρ x = 0
      exact map_eq_zero_iff _ e.injective
    · intro x y hxy
      show e (ρ y) = RingEquiv.prodComm (e (ρ x))
      rw [hρ.2.2 x y hxy, he]
      rfl

end PI.OmLocU.Red
