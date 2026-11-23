import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2PresentationRelationsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilUnipotentTorusPreserveTestStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierPreservesTestAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGroupSignMulAndNegOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilTorusMulUnipotentCommuteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierCompSmulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableQuadraticGaussIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFOpNOpFOpGaussStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralSqEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralTransformWeilStatement

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def testSub (X : Type) [TopologicalSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {f | IsTest f}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' := fun c f hf => ⟨hf.1.comp (fun z => c • z), hf.2.smul_left (f := fun _ => c)⟩

theorem absK_unit (A : Et F E) (s : A.Kˣ) : A.absK (s : A.K) = distribHaarChar A.K s := by
  unfold Et.absK
  rw [dif_pos s.isUnit]
  congr 2
  ext
  rfl

theorem fOp_smul (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (c : ℂ) (φ : A.L → ℂ) :
    fOp A ψ x μ (c • φ) = c • fOp A ψ x μ φ := by
  funext y
  simp only [fOp, fourB, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

theorem nOp_smul (A : Et F E) (ψ : AddChar F ℂ) (x z : A.K) (c : ℂ) (φ : A.L → ℂ) :
    nOp A ψ x z (c • φ) = c • nOp A ψ x z φ := by
  funext y
  simp only [nOp, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.JR.WeilQuad

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem absK_neg_one (A : Et F E) : A.absK ((-1 : A.Kˣ) : A.K) = 1 := by
  rw [absK_unit]
  have h : distribHaarChar A.K (-1 : A.Kˣ) ^ 2 = 1 := by
    rw [← map_pow]; simp
  have h0 := (distribHaarChar_pos (A := A.K) (g := (-1 : A.Kˣ))).le
  have : distribHaarChar A.K (-1 : A.Kˣ) = 1 := (pow_eq_one_iff_of_nonneg h0 two_ne_zero).1 h
  rw [this]; rfl

end GlobalTheory.JR.WeilQuad

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem omega_sq (A : Et F E) {ψ : AddChar F ℂ} {x : A.Kˣ} {μ : Measure A.L} {ω : A.K → ℂ}
    (H : Hyp A ψ x μ ω) (s : A.Kˣ) : ω s = 1 ∨ ω s = -1 := by
  by_cases h : ∃ y, A.NL y = s
  · exact Or.inl ((H.2.2.2.2 s).1 h)
  · exact Or.inr ((H.2.2.2.2 s).2 h)

theorem omega_one (A : Et F E) {ψ : AddChar F ℂ} {x : A.Kˣ} {μ : Measure A.L} {ω : A.K → ℂ}
    (H : Hyp A ψ x μ ω) : ω ((1 : A.Kˣ) : A.K) = 1 :=
  (H.2.2.2.2 1).1 ⟨1, by simp [Et.NL]⟩

theorem omega_inv (A : Et F E) {ψ : AddChar F ℂ} {x : A.Kˣ} {μ : Measure A.L} {ω : A.K → ℂ}
    (H : Hyp A ψ x μ ω) (hm : ∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) (s : A.Kˣ) :
    ω ((s⁻¹ : A.Kˣ) : A.K) = ω s := by
  have h1 := hm s s⁻¹
  rw [mul_inv_cancel, omega_one A H] at h1
  rcases omega_sq A H s with h | h <;> rw [h] at h1 ⊢
  · linear_combination -h1
  · linear_combination h1

end GlobalTheory.JR.WeilQuad

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem nOp_zero (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (φ : A.L → ℂ) : nOp A ψ x 0 φ = φ := by
  funext y; simp [nOp, Et.psiK]

theorem nOp_add (A : Et F E) (ψ : AddChar F ℂ) (x a b : A.K) (φ : A.L → ℂ) :
    nOp A ψ x (a + b) φ = nOp A ψ x a (nOp A ψ x b φ) := by
  funext y
  simp only [nOp, Et.psiK, add_mul, map_add, AddChar.map_add_eq_mul]; ring

theorem absK_mul (A : Et F E) (a b : A.Kˣ) : A.absK ((a * b : A.Kˣ) : A.K) = A.absK a * A.absK b := by
  simp only [absK_unit, map_mul, NNReal.coe_mul]

theorem absK_inv (A : Et F E) (a : A.Kˣ) : A.absK ((a⁻¹ : A.Kˣ) : A.K) = (A.absK a)⁻¹ := by
  simp only [absK_unit, map_inv, NNReal.coe_inv]

theorem absK_ne (A : Et F E) (a : A.Kˣ) : (A.absK a : ℂ) ≠ 0 := by
  rw [absK_unit]; exact_mod_cast (distribHaarChar_pos (A := A.K) (g := a)).ne'

theorem mOp_one (A : Et F E) {ψ : AddChar F ℂ} {x : A.Kˣ} {μ : Measure A.L} {ω : A.K → ℂ}
    (H : Hyp A ψ x μ ω) (φ : A.L → ℂ) : mOp A ω 1 φ = φ := by
  funext y
  simp only [mOp]
  rw [omega_one A H, absK_unit, map_one]
  simp

theorem mOp_mul (A : Et F E) {ω : A.K → ℂ}
    (hmul : ∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) (a b : A.Kˣ) (φ : A.L → ℂ) :
    mOp A ω (a * b) φ = mOp A ω a (mOp A ω b φ) := by
  funext y
  simp only [mOp]
  rw [hmul, absK_mul, smul_smul, Units.val_mul, mul_comm (b : A.K) (a : A.K)]
  push_cast; ring

theorem rel_ww (A : Et F E) {ψ : AddChar F ℂ} {x : A.Kˣ} {μ : Measure A.L} {ω : A.K → ℂ}
    (H : Hyp A ψ x μ ω) (hneg : ω ((-1 : A.Kˣ) : A.K) = 1) {G₁ : ℂ} (hsq : G₁ ^ 2 = 1) (φ : A.L → ℂ) (hφ : IsTest φ) :
    G₁⁻¹ • fOp A ψ x μ (G₁⁻¹ • fOp A ψ x μ φ) = mOp A ω (-1) φ := by
  funext y
  rw [fOp_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mOp]
  rw [hneg, absK_neg_one, Units.val_neg, Units.val_one, neg_one_smul]
  have h := H.2.2.2.1.2 φ hφ y
  simp only [fOp] at h ⊢
  rw [h]
  have : G₁⁻¹ * G₁⁻¹ = 1 := by rw [← mul_inv, ← sq, hsq, inv_one]
  rw [← mul_assoc, this]; push_cast; ring

end GlobalTheory.JR.WeilQuad

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem rel_wm (A : Et F E) {ψ : AddChar F ℂ} {x : A.Kˣ} {μ : Measure A.L} {ω : A.K → ℂ}
    (H : Hyp A ψ x μ ω) (hmul : ∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) (G₁ : ℂ) (s : A.Kˣ)
    (φ : A.L → ℂ)
    (h5 : ∀ y, fOp A ψ x μ (fun y' => φ ((s : A.K) • y')) y =
      ((A.absK s : ℂ) ^ 2)⁻¹ * fOp A ψ x μ φ (((s⁻¹ : A.Kˣ) : A.K) • y)) :
    G₁⁻¹ • fOp A ψ x μ (mOp A ω s φ) = mOp A ω s⁻¹ (G₁⁻¹ • fOp A ψ x μ φ) := by
  funext y
  have hm : mOp A ω s φ = (ω s * (A.absK s : ℂ)) • (fun y' => φ ((s : A.K) • y')) := by
    funext y'; simp [mOp]
  rw [hm, fOp_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mOp]
  rw [h5 y, omega_inv A H hmul, absK_inv]
  have := absK_ne A s
  push_cast
  field_simp

theorem rel_wnw (A : Et F E) {ψ : AddChar F ℂ} {x : A.Kˣ} {μ : Measure A.L} {ω : A.K → ℂ}
    (H : Hyp A ψ x μ ω) (hmul : ∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t)
    (hneg : ω ((-1 : A.Kˣ) : A.K) = 1) {G₁ : ℂ} (hG0 : G₁ ≠ 0) (u : A.Kˣ) (G : ℂ)
    (hGv : G = G₁ * ω u * ((A.absK u : ℂ))⁻¹) (φ : A.L → ℂ)
    (h8 : ∀ z, fOp A ψ x μ (nOp A ψ x u (fOp A ψ x μ φ)) z = G * A.psiK ψ (-((u⁻¹ : A.Kˣ) : A.K) * x * A.NL z) *
      fOp A ψ x μ (nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) φ) ((-((u⁻¹ : A.Kˣ) : A.K)) • z)) :
    G₁⁻¹ • fOp A ψ x μ (nOp A ψ x u (G₁⁻¹ • fOp A ψ x μ φ)) =
      nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) (mOp A ω (-u⁻¹) (G₁⁻¹ • fOp A ψ x μ (nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) φ))) := by
  funext z
  rw [nOp_smul, fOp_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h8 z, hGv]
  have hw : (-u⁻¹ : A.Kˣ) = (-1) * u⁻¹ := by rw [neg_one_mul]
  simp only [nOp, mOp]
  rw [hw, hmul, absK_mul, hneg, absK_neg_one, omega_inv A H hmul, absK_inv, ← hw, Units.val_neg]
  simp only [Pi.smul_apply, smul_eq_mul]
  have := absK_ne A u
  push_cast
  field_simp

end GlobalTheory.JR.WeilQuad

namespace GlobalTheory.JR.WeilQuad

open Classical in

theorem weilField_main : WeilField := by
  intro F E _ _ _ _ _ A hK hL ψ hψ x μ hμ ω hω
  have H : Hyp A ψ x μ ω := ⟨hK, hL, hψ, hμ, hω⟩
  have h2a := GlobalTheory.T.quadraticWeil_unipotent_torus_preserve_test F E A ψ x μ ω H
  have h2b := GlobalTheory.T.quadraticWeilFourier_preserves_test_additive F E A ψ x μ ω H
  obtain ⟨hmul, hneg⟩ := GlobalTheory.T.normGroupSign_mul_and_neg_one F E A ψ x μ ω H
  obtain ⟨G₁, hG₁⟩ := GlobalTheory.T.exists_stable_quadraticGaussIntegral F E A ψ x μ ω H 1
  have hsq := GlobalTheory.T.stableQuadraticGaussIntegral_sq_eq_one F E A ψ x μ ω H G₁ hG₁
  have hG0 : G₁ ≠ 0 := by rintro rfl; norm_num at hsq
  let S := testSub A.L
  let Nz : A.K → Module.End ℂ S := fun z =>
    { toFun := fun f => ⟨nOp A ψ x z f, (h2a f f.2).1 z⟩
      map_add' := fun f g => Subtype.ext (funext fun y => by
        change nOp A ψ x z ((f : A.L → ℂ) + g) y = nOp A ψ x z f y + nOp A ψ x z g y
        simp [nOp, mul_add])
      map_smul' := fun c f => Subtype.ext (by
        change nOp A ψ x z (c • (f : A.L → ℂ)) = c • nOp A ψ x z f
        exact nOp_smul A ψ x z c f) }
  let Ms : A.Kˣ → Module.End ℂ S := fun s =>
    { toFun := fun f => ⟨mOp A ω s f, (h2a f f.2).2 s⟩
      map_add' := fun f g => Subtype.ext (funext fun y => by
        change mOp A ω s ((f : A.L → ℂ) + g) y = mOp A ω s f y + mOp A ω s g y
        simp [mOp, mul_add])
      map_smul' := fun c f => Subtype.ext (funext fun y => by
        change mOp A ω s (c • (f : A.L → ℂ)) y = c • mOp A ω s f y
        simp [mOp]; ring) }
  let Tw : Module.End ℂ S :=
    { toFun := fun f => ⟨G₁⁻¹ • fOp A ψ x μ f, S.smul_mem _ (h2b f f.2).1⟩
      map_add' := fun f g => Subtype.ext (by
        change G₁⁻¹ • fOp A ψ x μ ((f : A.L → ℂ) + g) = G₁⁻¹ • fOp A ψ x μ f + G₁⁻¹ • fOp A ψ x μ g
        rw [(h2b f f.2).2 g g.2, smul_add])
      map_smul' := fun c f => Subtype.ext (by
        change G₁⁻¹ • fOp A ψ x μ (c • (f : A.L → ℂ)) = c • (G₁⁻¹ • fOp A ψ x μ f)
        rw [fOp_smul, smul_smul, smul_smul, mul_comm]) }
  have e1 : Nz 0 = 1 := LinearMap.ext fun f => Subtype.ext (nOp_zero A ψ x f)
  have e2 : ∀ a b, Nz (a + b) = Nz a * Nz b := fun a b =>
    LinearMap.ext fun f => Subtype.ext (nOp_add A ψ x a b f)
  have e3 : Ms 1 = 1 := LinearMap.ext fun f => Subtype.ext (mOp_one A H f)
  have e4 : ∀ a b, Ms (a * b) = Ms a * Ms b := fun a b =>
    LinearMap.ext fun f => Subtype.ext (mOp_mul A hmul a b f)
  have e5 : ∀ s z, Ms s * Nz z = Nz ((s : A.K) ^ 2 * z) * Ms s := fun s z =>
    LinearMap.ext fun f => Subtype.ext (GlobalTheory.T.quadraticWeilTorus_mul_unipotent_commute F E A ψ x μ ω H s z f)
  have e6 : Tw * Tw = Ms (-1) := LinearMap.ext fun f => Subtype.ext (rel_ww A H hneg hsq f f.2)
  have e7 : ∀ s, Tw * Ms s = Ms s⁻¹ * Tw := fun s => LinearMap.ext fun f =>
    Subtype.ext (rel_wm A H hmul G₁ s f (GlobalTheory.T.quadraticWeilFourier_comp_smul F E A ψ x μ ω H s f f.2))
  have e8 : ∀ u : A.Kˣ, Tw * Nz u * Tw = Nz (-((u⁻¹ : A.Kˣ) : A.K)) * Ms (-u⁻¹) * Tw * Nz (-((u⁻¹ : A.Kˣ) : A.K)) :=
    fun u => LinearMap.ext fun f => Subtype.ext (by
      obtain ⟨G, hG⟩ := GlobalTheory.T.exists_stable_quadraticGaussIntegral F E A ψ x μ ω H u
      exact rel_wnw A H hmul hneg hG0 u G (GlobalTheory.T.stableQuadraticGaussIntegral_transform_weil F E A ψ x μ ω H u G G₁ hG hG₁) f
        (GlobalTheory.T.quadraticWeil_fOp_nOp_fOp_gauss F E A ψ x μ ω H u G hG f f.2))
  obtain ⟨ρ, hρn, hρm, hρw⟩ := GlobalTheory.T.exists_hom_specialLinearGroup_of_relations A.K hK (Module.End ℂ S) Nz Ms Tw e1 e2 e3 e4 e5 e6 e7 e8
  refine ⟨G₁⁻¹, fun g φ => if h : IsTest φ then ((ρ g ⟨φ, h⟩ : S) : A.L → ℂ) else 0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g f hf
    simp only [dif_pos hf]
    exact (ρ g ⟨f, hf⟩).2
  · intro f hf
    simp [dif_pos hf]
  · intro g h f hf
    have hh : IsTest ((ρ h ⟨f, hf⟩ : S) : A.L → ℂ) := (ρ h ⟨f, hf⟩).2
    simp only [dif_pos hf, dif_pos hh, map_mul, Module.End.mul_apply]
  · intro g c f f' hf hf'
    have hc : IsTest (c • f + f') := S.add_mem (S.smul_mem c hf) hf'
    simp only [dif_pos hf, dif_pos hf', dif_pos hc]
    have : (⟨c • f + f', hc⟩ : S) = c • ⟨f, hf⟩ + ⟨f', hf'⟩ := rfl
    rw [this, map_add, map_smul]
    rfl
  · intro φ hφ
    refine ⟨fun z y => ?_, fun s y => ?_, fun y => ?_⟩
    · simp only [dif_pos hφ, hρn]; rfl
    · simp only [dif_pos hφ, hρm]; rfl
    · simp only [dif_pos hφ, hρw]; rfl

end GlobalTheory.JR.WeilQuad

end
