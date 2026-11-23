import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipConjIdeal

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_sub_left (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (x - y) z = ReciprocityTheory.ChartRestriction.G.FD.herm G x z - ReciprocityTheory.ChartRestriction.G.FD.herm G y z := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.herm, sub_mul, Finset.sum_sub_distrib]

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (a : E) (x z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (a • x) z = a * ReciprocityTheory.ChartRestriction.G.FD.herm G x z := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (a : E) (x z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G x (a • z) = ReciprocityTheory.ChartRestriction.G.FD.cc a * ReciprocityTheory.ChartRestriction.G.FD.herm G x z := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem herm_adjoint_pow (G : Matrix (Fin r) (Fin r) E) (β : GL (Fin r) E)
    (hU : ∀ v w, ReciprocityTheory.ChartRestriction.G.FD.herm G ((β : Matrix (Fin r) (Fin r) E) *ᵥ v)
      ((β : Matrix (Fin r) (Fin r) E) *ᵥ w) = ReciprocityTheory.ChartRestriction.G.FD.herm G v w) (k : ℕ) (x y : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G ((((β : Matrix (Fin r) (Fin r) E) - 1) ^ k) *ᵥ x) y =
      ReciprocityTheory.ChartRestriction.G.FD.herm G x (((((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) - 1) ^ k) *ᵥ y) := by
  have step : ∀ x z : Fin r → E, ReciprocityTheory.ChartRestriction.G.FD.herm G (((β : Matrix (Fin r) (Fin r) E) - 1) *ᵥ x) z =
      ReciprocityTheory.ChartRestriction.G.FD.herm G x ((((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) - 1) *ᵥ z) := by
    intro x z
    have hz : (β : Matrix (Fin r) (Fin r) E) *ᵥ (((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ z) = z := by
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, herm_sub_left]
    conv_lhs => rw [← hz, hU]
    simp [ReciprocityTheory.ChartRestriction.G.FD.herm, Finset.sum_sub_distrib, mul_sub, ReciprocityTheory.ChartRestriction.G.FD.cc]
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ih, step, mulVec_mulVec, ← pow_succ']

end GlobalTheory.UnipConjIdeal

namespace GlobalTheory.UnipConjIdeal

open Matrix

theorem pow_sub_one_mem_conj_ideal_smul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (β : GL (Fin r) E),
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v) (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) =
      herm X.Gm v w) →
    (∀ v, v ∈ X.L' ↔ Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v ∈ X.L') →
    ∀ P : Ideal (𝓞 E), (∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • X.L') →
    ∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈
      P.map ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E ≃+* 𝓞 E) : 𝓞 E →+* 𝓞 E) • X.L' := by
  intro E _ _ _ r X β hU hL P hP v hv
  have hsm : ∀ (p : 𝓞 E) (w : Fin r → E), p • w = (p : E) • w := fun p w => (algebraMap_smul E p w).symm
  set βm : Matrix (Fin r) (Fin r) E := (β : Matrix (Fin r) (Fin r) E) with hβm
  set βi : Matrix (Fin r) (Fin r) E := ((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hβi
  have h1 : βi * βm = 1 := Units.inv_mul β
  have h2 : βm * βi = 1 := Units.mul_inv β

  have hinv : ∀ w ∈ X.L', βi *ᵥ w ∈ X.L' := by
    intro w hw
    refine (hL _).mpr ?_
    rw [mulVec_mulVec, h2, one_mulVec]; exact hw
  have hBpow : ∀ k : ℕ, ∀ w ∈ X.L', ((-βi) ^ k) *ᵥ w ∈ X.L' := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ', ← mulVec_mulVec, neg_mulVec]
      exact X.L'.neg_mem (hinv _ (ih w hw))

  have hfac : βi - 1 = (-βi) * (βm - 1) := by
    rw [neg_mul, mul_sub, h1, mul_one]; abel
  have hcomm : Commute (-βi) (βm - 1) := by
    unfold Commute SemiconjBy
    rw [neg_mul, mul_neg, mul_sub, sub_mul, h1, h2, mul_one, one_mul]
  have hadjpow : (βi - 1) ^ r = (-βi) ^ r * (βm - 1) ^ r := by
    rw [hfac, hcomm.mul_pow]
  by_cases hP0 : P = ⊥
  · subst hP0
    have h0 := hP v hv
    rw [Submodule.bot_smul, Submodule.mem_bot] at h0
    rw [h0]; exact zero_mem _
  obtain ⟨c, hcP, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨P', hPP'⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr hcP)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc0

  have hi : ∀ w ∈ P • X.L', ∀ p' ∈ P', ((c : E)⁻¹ * p') • w ∈ X.L' := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro p hp l hl p' hp'
      have hm : p * p' ∈ Ideal.span {c} := by rw [hPP']; exact Ideal.mul_mem_mul hp hp'
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
      have : ((c : E)⁻¹ * p') • (p • l) = t • l := by
        rw [hsm, hsm, smul_smul]
        congr 1
        have : (p : E) * p' = t * c := by exact_mod_cast ht.symm
        field_simp
        linear_combination this
      rw [this]; exact X.L'.smul_mem t hl
    · intro x y hx hy p' hp'
      rw [smul_add]; exact X.L'.add_mem (hx p' hp') (hy p' hp')

  have hii : ∀ z ∈ X.L', ∀ p' ∈ P', ((c : E)⁻¹ * p') • (((βi - 1) ^ r) *ᵥ z) ∈ X.L' := by
    intro z hz p' hp'
    rw [hadjpow, ← mulVec_mulVec, ← mulVec_smul]
    exact hBpow r _ (hi _ (hP z hz) p' hp')

  set σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv with hσdef
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = ReciprocityTheory.ChartRestriction.G.FD.cc (x : E) := fun x => rfl
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc (ReciprocityTheory.ChartRestriction.G.FD.cc x) = x := by
    intro x; simp [ReciprocityTheory.ChartRestriction.G.FD.cc]

  have hiii : ∀ p' ∈ P', ((σ c : E)⁻¹ * (σ p' : E)) • (((βm - 1) ^ r) *ᵥ v) ∈ X.L' := by
    intro p' hp'
    refine X.L'_dual _ fun z hz => ?_
    rw [herm_smul_left, herm_adjoint_pow X.Gm β hU r v z]
    have : (σ c : E)⁻¹ * (σ p' : E) = ReciprocityTheory.ChartRestriction.G.FD.cc ((c : E)⁻¹ * p') := by
      rw [hσ, hσ, ReciprocityTheory.ChartRestriction.G.FD.cc, ReciprocityTheory.ChartRestriction.G.FD.cc, ReciprocityTheory.ChartRestriction.G.FD.cc, map_mul, map_inv₀]
    rw [this, ← herm_smul_right]
    exact X.L'_int v hv _ (hii z hz p' hp')

  have hmul : P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) = Ideal.span {σ c} := by
    rw [← Ideal.map_mul, ← hPP', Ideal.map_span, Set.image_singleton]; rfl
  have hd : σ c ∈ P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) := by
    rw [hmul]; exact Ideal.mem_span_singleton_self _
  have hσc : (σ c : E) ≠ 0 := by
    intro h; apply hcE
    have := congrArg ReciprocityTheory.ChartRestriction.G.FD.cc h
    rw [hσ, hcc] at this
    simpa [ReciprocityTheory.ChartRestriction.G.FD.cc] using this
  have key : ∀ u, u ∈ P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) →
      ((σ c : E)⁻¹ * u) • (((βm - 1) ^ r) *ᵥ v) ∈ P.map (σ : 𝓞 E →+* 𝓞 E) • X.L' := by
    intro u hu
    refine Submodule.mul_induction_on hu ?_ ?_
    · intro q hq q' hq'
      obtain ⟨p', hp', rfl⟩ := (Ideal.mem_map_of_equiv σ q').mp hq'
      have : ((σ c : E)⁻¹ * ((q * σ p' : 𝓞 E) : E)) • (((βm - 1) ^ r) *ᵥ v) =
          q • (((σ c : E)⁻¹ * (σ p' : E)) • (((βm - 1) ^ r) *ᵥ v)) := by
        rw [hsm, smul_smul]; congr 1; push_cast; ring
      rw [this]
      exact Submodule.smul_mem_smul hq (hiii p' hp')
    · intro x y hx hy
      rw [show ((x + y : 𝓞 E) : E) = (x : E) + y by push_cast; rfl, mul_add, add_smul]
      exact Submodule.add_mem _ hx hy
  have := key _ hd
  rwa [inv_mul_cancel₀ hσc, one_smul] at this

end GlobalTheory.UnipConjIdeal
