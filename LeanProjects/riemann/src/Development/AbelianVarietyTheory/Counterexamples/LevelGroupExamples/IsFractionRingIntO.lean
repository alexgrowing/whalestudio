import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)
open Formalism.L2.Pj.PointsOfFlagModel

namespace GlobalTheory.IntegralPointCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {p : ℕ} {Y : Model Xo c β} {C : SCF p}

def embHom (P : PtC Y C) (τ : E →+* ℂ) : 𝓞 E →+* ↥C.S :=
  P.fK.comp ((τ.comp (algebraMap (𝓞 E) E)).codRestrict c.F.toSubring (fun a => c.conj τ a))

theorem embHom_apply (P : PtC Y C) (τ : E →+* ℂ) (a : 𝓞 E) : embHom P τ a = P.emb τ a := rfl

theorem lieMult (P : PtC Y C) (τ : E →+* ℂ) : LieMult Y.t.act P.x0 (embHom P τ) (D.mult τ) := by
  have h := (Y.oF.geom ↥C.S P.y (P.fK.comp (IntermediateField.inclusion c.le).toRingHom) (by
    rw [pullback.condition, ← Category.assoc, P.y_over]
    exact (Spec.map_comp _ _).symm)).1 (embHom P τ)
  have key : embHom P τ H.rt = (P.fK.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ ↔
      τ (H.rt : E) = H.rt0 := by
    rw [embHom_apply, PtC.emb, RingHom.comp_apply, P.fK.injective.eq_iff, Subtype.ext_iff]
    rfl
  refine (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ Y.t.act Y.oF.t.act Y.m.cart Y.m.act _ P.y _ _).1 ?_
  unfold Datum.mult
  split_ifs with e
  · exact h.1 (key.2 e)
  · exact h.2 (fun e' => e (key.1 e'))

theorem nonempty_flag (P : PtC Y C) : Nonempty P.Flag := by
  choose v hv hb using lieMult P
  exact ⟨⟨v, fun τ i => (hv τ i).1, fun τ i => (hv τ i).2, fun τ w h₁ h₂ => hb τ w ⟨h₁, h₂⟩⟩⟩

theorem ext_of_generic (P P' : PtC Y C) (h : P.y = P'.y) : P = P' := by
  have hf : P.fK = P'.fK := by
    have := P.y_over.symm.trans (h ▸ P'.y_over)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  have ha : P.alg = P'.alg := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have h1 := RingHom.congr_fun P.compat a
    have h2 := RingHom.congr_fun P'.compat a
    rw [hf] at h1
    exact h1.trans h2.symm
  have hpr := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have ht : P.yt = P'.yt := by
    have : IsDominant (spMap (intO ↥C.S).subtype) := by
      refine ⟨?_⟩
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)
    exact ext_of_isDominant_of_isSeparated Y.s (by rw [P.yt_over, P'.yt_over, ha]) (spMap (intO ↥C.S).subtype)
      (by rw [P.ext, P'.ext, h])
  cases P; cases P'
  simp only at h hf ha ht
  subst h hf ha ht
  rfl

theorem valuationRing_intO (K : Type) [NormedField K] [IsUltrametricDist K] : ValuationRing (intO K) := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  rcases le_total ‖(a : K)‖ ‖(b : K)‖ with h | h
  · by_cases hb : (b : K) = 0
    · refine ⟨0, Or.inl (Subtype.ext ?_)⟩
      simp [hb]
    · refine ⟨⟨a / b, ?_⟩, Or.inr (Subtype.ext ?_)⟩
      · change ‖(a : K) / b‖ ≤ 1
        rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · change (b : K) * (a / b) = a
        field_simp
  · by_cases ha : (a : K) = 0
    · refine ⟨0, Or.inr (Subtype.ext ?_)⟩
      simp [ha]
    · refine ⟨⟨b / a, ?_⟩, Or.inl (Subtype.ext ?_)⟩
      · change ‖(b : K) / a‖ ≤ 1
        rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · change (a : K) * (b / a) = b
        field_simp

theorem isFractionRing_intO (K : Type) [NormedField K] [IsUltrametricDist K] : IsFractionRing (intO K) K := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  rcases le_total ‖z‖ 1 with h | h
  · exact ⟨⟨z, h⟩, 1, by simp; rfl⟩
  · refine ⟨1, ⟨z⁻¹, ?_⟩, ?_⟩
    · change ‖z⁻¹‖ ≤ 1
      rw [norm_inv]; exact inv_le_one_of_one_le₀ h
    · change z = ((1 : intO K) : K) / z⁻¹
      simp

theorem isEmpty_of_isUnit (hp : 2 ≤ p) (h : IsUnit (p : O)) : IsEmpty (PtC Y C) := by
  refine ⟨fun P => ?_⟩
  obtain ⟨b, hb⟩ := h.exists_right_inv
  have h1 : (p : ↥C.S) * (P.alg b : ↥C.S) = 1 := by
    have := congrArg (fun z => ((P.alg z : intO ↥C.S) : ↥C.S)) hb
    simpa using this
  have h2 : ‖(P.alg b : ↥C.S)‖ ≤ 1 := (P.alg b).2
  have h3 := congrArg norm h1
  rw [norm_mul, C.norm_p, norm_one] at h3
  have h4 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h5 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h6 : 0 < (p : ℝ)⁻¹ := by positivity
  nlinarith

def toOne (C : SCF p) : SCF 1 where
  S := C.S
  norm_p := by simp

theorem main (P : PtC Y C) :
    Nonempty P.Flag ∧ (∀ P' : PtC Y C, P.y = P'.y → P = P') ∧ (2 ≤ p → ¬ IsUnit (p : O)) :=
  ⟨nonempty_flag P, ext_of_generic P, fun hp h => (isEmpty_of_isUnit hp h).elim P⟩

end GlobalTheory.IntegralPointCheck
