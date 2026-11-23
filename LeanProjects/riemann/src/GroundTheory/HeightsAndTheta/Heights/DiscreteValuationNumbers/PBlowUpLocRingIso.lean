import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreSemilocalCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Abstract

variable {D A : Type*} [CommRing D] [IsDomain D] [CommRing A] [IsDomain A]

theorem exists_ringEquiv_closure_div_of_eq_C_mul_X_pow (θ : A →+* Polynomial D)
    (hθ : Function.Injective θ) {I : Type*} (f g : I → A) (a c : I → D) (n : I → ℕ)
    (hf : ∀ i, θ (f i) = Polynomial.C (a i) * Polynomial.X ^ n i)
    (hg : ∀ i, θ (g i) = Polynomial.C (c i) * Polynomial.X ^ n i)
    (s₁ : Subring (FractionRing A)) (s₂ : Subring (FractionRing D))
    (h₁ : s₁ = Subring.closure (Set.range fun i =>
        algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i)))
    (h₂ : s₂ = Subring.closure (Set.range fun i =>
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i))) :
    ∃ φ : s₁ ≃+* s₂, ∀ i (hi : algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i) ∈ s₁),
      (φ ⟨_, hi⟩ : FractionRing D) =
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i) := by
  subst h₁ h₂
  let M := FractionRing (Polynomial D)
  have hM : Function.Injective (algebraMap (Polynomial D) M) := IsFractionRing.injective _ M
  let g₁ : A →+* M := (algebraMap (Polynomial D) M).comp θ
  let g₂ : D →+* M := (algebraMap (Polynomial D) M).comp Polynomial.C
  have hg₁ : Function.Injective g₁ := hM.comp hθ
  have hg₂ : Function.Injective g₂ := hM.comp Polynomial.C_injective
  let ι₁ : FractionRing A →+* M := IsFractionRing.lift hg₁
  let ι₂ : FractionRing D →+* M := IsFractionRing.lift hg₂
  have hgen : ∀ i, ι₁ (algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i)) =
      ι₂ (algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i)) := by
    intro i
    rw [map_div₀, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
      IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    have hX : algebraMap (Polynomial D) M (Polynomial.X ^ n i) ≠ 0 := fun h =>
      pow_ne_zero _ Polynomial.X_ne_zero (hM (h.trans (map_zero _).symm))
    simp only [g₁, g₂, RingHom.comp_apply, hf, hg, map_mul]
    exact mul_div_mul_right _ _ hX
  have himg : (Subring.closure (Set.range fun i =>
        algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i))).map ι₁ =
      (Subring.closure (Set.range fun i =>
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i))).map ι₂ := by
    rw [RingHom.map_closure, RingHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, (hgen i).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, hgen i⟩
  refine ⟨(Subring.equivMapOfInjective _ ι₁ ι₁.injective).trans ((RingEquiv.subringCongr himg).trans
    (Subring.equivMapOfInjective _ ι₂ ι₂.injective).symm), fun i hi => ?_⟩
  apply ι₂.injective
  rw [← hgen i, ← Subring.coe_equivMapOfInjective_apply _ ι₂ ι₂.injective, RingEquiv.trans_apply,
    RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

end Abstract

variable {K : Type*} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem aeval_blowUpSubst_of_isMultiHomog (P : Ideal (MRing ι R)) (u : J → MRing ι R)
    {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b) :
    aeval (blowUpSubst P u) F = Polynomial.C (blowUpEval P u F) * Polynomial.X ^ (b none) := by
  classical
  set w := blockWeight (extIdx ι J)
  set ωT : (Σ o, extIdx ι J o) → ℕ := fun v => Pi.evalAddMonoidHom (fun _ => ℕ) none (w v)
  have hT : ∀ d, Finsupp.weight ωT d = Finsupp.weight w d none := fun d =>
    weight_comp_addMonoidHom_apply w (Pi.evalAddMonoidHom (fun _ => ℕ) none) d
  have hsubst : blowUpSubst P u = fun v =>
      Polynomial.C (Ideal.Quotient.mkₐ R P (blowUpAtOne u v)) * Polynomial.X ^ ωT v := by
    funext v
    obtain ⟨o, i⟩ := v
    cases o <;> simp [blowUpSubst, blowUpAtOne, ωT, w, blockWeight]
  have hFT : IsWeightedHomogeneous ωT F (b none) := by
    intro d hd
    rw [hT]
    exact congrFun (hF hd) none
  set c := aeval (fun v => Ideal.Quotient.mkₐ R P (blowUpAtOne u v)) F
  have key : aeval (blowUpSubst P u) F = Polynomial.C c * Polynomial.X ^ (b none) := by
    refine Polynomial.ext fun n => ?_
    rw [hsubst, coeff_aeval_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hn
    · rw [hn, hFT.weightedHomogeneousComponent_same]
    · rw [hFT.weightedHomogeneousComponent_ne n hn, map_zero]
  have hσ : blowUpEval P u F = c := by
    show Polynomial.eval 1 (aeval (blowUpSubst P u) F) = c
    rw [key]
    simp
  rw [hσ]
  exact key

theorem BlowUpLocRingIso.proof : BlowUpLocRingIso.Statement.{u} := by
  intro R _ K _ ι J P _ u Q _
  have hB : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  let θ : MRing (extIdx ι J) R ⧸ blowUpOf P u →+* Polynomial (MRing ι R ⧸ P) :=
    Ideal.Quotient.lift (blowUpOf P u) (aeval (blowUpSubst P u)).toRingHom
      (fun a ha => RingHom.mem_ker.mp ha)
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr ha)
  let I := {t : (Option K → ℕ) × MRing (extIdx ι J) R × MRing (extIdx ι J) R //
    IsMultiHomog t.2.1 t.1 ∧ IsMultiHomog t.2.2 t.1 ∧ t.2.2 ∉ Q}
  have hf : ∀ i : I, θ (Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) =
      Polynomial.C (blowUpEval P u i.1.2.1) * Polynomial.X ^ (i.1.1 none) := fun i => by
    rw [Ideal.Quotient.lift_mk]
    exact aeval_blowUpSubst_of_isMultiHomog P u i.2.1
  have hg : ∀ i : I, θ (Ideal.Quotient.mk (blowUpOf P u) i.1.2.2) =
      Polynomial.C (blowUpEval P u i.1.2.2) * Polynomial.X ^ (i.1.1 none) := fun i => by
    rw [Ideal.Quotient.lift_mk]
    exact aeval_blowUpSubst_of_isMultiHomog P u i.2.2.1
  have h₁ : homLocRing (blowUpOf P u) Q = Subring.closure (Set.range fun i : I =>
      algebraMap _ (FractionRing (MRing (extIdx ι J) R ⧸ blowUpOf P u)) (Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) /
        algebraMap _ (FractionRing (MRing (extIdx ι J) R ⧸ blowUpOf P u)) (Ideal.Quotient.mk (blowUpOf P u) i.1.2.2)) := by
    rw [homLocRing]
    congr 1
    ext z
    constructor
    · rintro ⟨b, F, G, hF, hG, hGQ, rfl⟩
      exact ⟨⟨(b, F, G), hF, hG, hGQ⟩, rfl⟩
    · rintro ⟨⟨⟨b, F, G⟩, hF, hG, hGQ⟩, rfl⟩
      exact ⟨b, F, G, hF, hG, hGQ, rfl⟩
  have h₂ : blowUpLocRing P u Q = Subring.closure (Set.range fun i : I =>
      algebraMap _ (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u i.1.2.1) /
        algebraMap _ (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u i.1.2.2)) := by
    rw [blowUpLocRing]
    congr 1
    ext z
    constructor
    · rintro ⟨b, F, G, hF, hG, hGQ, rfl⟩
      exact ⟨⟨(b, F, G), hF, hG, hGQ⟩, rfl⟩
    · rintro ⟨⟨⟨b, F, G⟩, hF, hG, hGQ⟩, rfl⟩
      exact ⟨b, F, G, hF, hG, hGQ, rfl⟩
  obtain ⟨φ, hφ⟩ := exists_ringEquiv_closure_div_of_eq_C_mul_X_pow θ hθ
    (fun i : I => Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) (fun i : I => Ideal.Quotient.mk (blowUpOf P u) i.1.2.2)
    (fun i : I => blowUpEval P u i.1.2.1) (fun i : I => blowUpEval P u i.1.2.2) (fun i : I => i.1.1 none)
    hf hg _ _ h₁ h₂
  refine ⟨φ, ?_⟩
  intro b F G hF hG hGQ
  exact hφ ⟨(b, F, G), hF, hG, hGQ⟩ _

end

end GroundTheory.Heights₂.Heights.NumbersDVR
