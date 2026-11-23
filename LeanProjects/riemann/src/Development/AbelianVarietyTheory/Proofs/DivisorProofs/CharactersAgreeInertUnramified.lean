import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInert
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadratic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertChars

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_mul_of_at {v : Pl F} {y : AE F E} (hy : At (evFin F v) y) :
    y = algebraMap (AF F) (AE F E) (GlobalTheory.EmbChart.atPlace v 1) * y := by
  have h0 : evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
    rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have h1 : (1 - GlobalTheory.EmbChart.atPlace v 1) • y = 0 := hy _ h0
  rw [Algebra.smul_def, map_sub, map_one, sub_mul, one_mul, sub_eq_zero] at h1
  exact h1

private lemma tensorProduct_map_eq_zero_of_at_of_atPlace_eq_zero {R : Type} [CommRing R] [Algebra F R] {v : Pl F} (φ : AF F →ₐ[F] R)
    (hφ : φ (GlobalTheory.EmbChart.atPlace v 1) = 0) {y : AE F E} (hy : At (evFin F v) y) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) y = 0 := by
  rw [eq_mul_of_at hy, map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul,
    Algebra.algebraMap_self_apply, hφ, TensorProduct.zero_tmul, zero_mul]

theorem eq_ideleAt_of_at {v : Pl F} (z : (AE F E)ˣ) (hz : At (evFin F v) ((z : AE F E) - 1)) :
    z = GlobalTheory.Doubling.ideleAt F E v (GlobalTheory.Doubling.unitFin F E v z) := by
  have hev : ∀ {R : Type} [CommRing R] [Algebra F R] (φ : AF F →ₐ[F] R), φ (GlobalTheory.EmbChart.atPlace v 1) = 0 →
      Algebra.TensorProduct.map φ (AlgHom.id F E) (z : AE F E) = 1 := by
    intro R _ _ φ hφ
    have h := tensorProduct_map_eq_zero_of_at_of_atPlace_eq_zero φ hφ hz
    rwa [map_sub, map_one, sub_eq_zero] at h
  apply GlobalTheory.Doubling.idele_ext
  · intro w
    rw [GlobalTheory.Doubling.unitInf_ideleAt]
    ext
    refine hev (evInf F w) ?_
    rw [GlobalTheory.EmbChart.atPlace_apply]
    show GlobalTheory.AutFunCompare.evW w (fstA F (pairA F 0 (singleFin v 1))) = 0
    exact map_zero _
  · intro u
    by_cases huv : u = v
    · subst huv
      rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
    · rw [GlobalTheory.Doubling.unitFin_ideleAt_ne huv]
      ext
      refine hev (evFin F u) ?_
      rw [GlobalTheory.EmbChart.atPlace_apply]
      exact evalV_singleFin_ne huv 1

end GlobalTheory.InertChars

namespace GlobalTheory.InertChars

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locIdele_eq_of_inert {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (α β : Chr F E) (hres : ∀ b : (AF F)ˣ, α (ideleMap F E b) = β (ideleMap F E b))
    (hα : UnrAt α w) (hβ : UnrAt β w) (y : (w.adicCompletion E)ˣ) :
    α (locIdele F w y) = β (locIdele F w y) := by
  unfold UnrAt at hα hβ
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  obtain ⟨a, ha⟩ := GlobalTheory.LFun.InertValue.exists_isUnifAt hw h
  have hπ : α (locIdele F w (Units.map (complMap h).toMonoidHom a)) =
      β (locIdele F w (Units.map (complMap h).toMonoidHom a)) := by
    rw [GlobalTheory.LFun.InertValue.locIdele_complMap hw h a]
    exact hres _
  generalize Units.map (complMap h).toMonoidHom a = π at ha hπ
  have hunit : ∀ u : (w.adicCompletion E)ˣ, Valued.v (u : w.adicCompletion E) = 1 →
      α (locIdele F w u) = β (locIdele F w u) := by
    intro u hu
    have h1 : locChar α w u = 1 := hα u hu
    have h2 : locChar β w u = 1 := hβ u hu
    rw [← h2] at h1
    have h3 := congrArg (fun x : ℂˣ => (x : ℂ)) h1
    simp only [locChar, MonoidHom.comp_apply, Circle.toUnits_apply, Units.val_mk0] at h3
    exact Circle.ext h3
  have key : ∀ (u : (w.adicCompletion E)ˣ) (n : ℤ), Valued.v (u : w.adicCompletion E) = 1 →
      α (locIdele F w (u * π ^ n)) = β (locIdele F w (u * π ^ n)) := by
    intro u n hu'
    rw [map_mul, map_mul, map_mul, map_zpow, map_zpow, map_zpow, hunit u hu', hπ]
  have hy0 : Valued.v (y : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (y : w.adicCompletion E) = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hy0).symm⟩
  have hu : Valued.v ((y * π ^ k : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    have hπv : Valued.v (π : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := ha
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπv, hk, ← WithZero.exp_zsmul,
      ← WithZero.exp_add, smul_neg, smul_eq_mul, mul_one, add_neg_cancel, WithZero.exp_zero]
  have hy : y = (y * π ^ k) * π ^ (-k) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hy]
  exact key _ _ hu

theorem beta_eq_alpha_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
      ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → X.β z = X.α z := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv z hz
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  have hpow : ((-1 : ℂ)) ^ a = (-1) ^ a' := by
    have he := hT.geo.even
    rw [Nat.even_add] at he
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, (he.mp ha).neg_one_pow]
    · have ha' : Odd a' := Nat.not_even_iff_odd.mp (fun h' => Nat.not_even_iff_odd.mpr ha (he.mpr h'))
      rw [ha.neg_one_pow, ha'.neg_one_pow]
  have hres : ∀ b : (AF F)ˣ, X.β (ideleMap F E b) = X.α (ideleMap F E b) := by
    intro b
    have e1 : ((X.α (ideleMap F E b) : Circle) : ℂ) = _ := hT.chars.resα b
    have e2 : ((X.β (ideleMap F E b) : Circle) : ℂ) = _ := hT.chars.resβ b
    apply Circle.ext
    rw [e1, e2, hpow]
  have hnot : ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl F))) := by
    rw [h]
    exact hv
  rw [eq_ideleAt_of_at z hz, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw]
  exact locIdele_eq_of_inert hw X.β X.α hres (hT.chars.unrβ w hnot) (hT.chars.unrα w hnot) _

end GlobalTheory.InertChars
