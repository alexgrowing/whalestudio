import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare.RealChart

theorem tensor_span {F E M : Type} [Field F] [Field E] [Algebra F E] [AddCommGroup M] [Module F M] (δ : E)
    (h : ∀ x : E, ∃ u v : F, x = u • (1 : E) + v • δ) (a : M ⊗[F] E) :
    ∃ a₀ a₁ : M, a = a₀ ⊗ₜ[F] (1 : E) + a₁ ⊗ₜ[F] δ := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul m x =>
    obtain ⟨u, v, rfl⟩ := h x
    exact ⟨u • m, v • m, by simp only [TensorProduct.tmul_add, TensorProduct.smul_tmul]⟩
  | add a b ha hb =>
    obtain ⟨a₀, a₁, rfl⟩ := ha
    obtain ⟨b₀, b₁, rfl⟩ := hb
    exact ⟨a₀ + b₀, a₁ + b₁, by simp only [TensorProduct.add_tmul]; abel⟩

theorem zero_tmul_add {F E M : Type} [Field F] [Field E] [Algebra F E] [CommRing M] [Algebra F M] (x y : E) :
    (0 : M) ⊗ₜ[F] x + (0 : M) ⊗ₜ[F] y = 0 := by simp

theorem tensor_prod_ext {F E R A B : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [CommRing A] [CommRing B]
    [Algebra F R] [Algebra F A] [Algebra F B] (p : R →ₐ[F] A) (q : R →ₐ[F] B) (i : A →ₗ[F] R) (j : B →ₗ[F] R)
    (h : ∀ x, i (p x) + j (q x) = x) (a : R ⊗[F] E)
    (h1 : Algebra.TensorProduct.map p (AlgHom.id F E) a = 0)
    (h2 : Algebra.TensorProduct.map q (AlgHom.id F E) a = 0) : a = 0 := by
  have key : ∀ a : R ⊗[F] E,
      a = i.rTensor E (Algebra.TensorProduct.map p (AlgHom.id F E) a) +
        j.rTensor E (Algebra.TensorProduct.map q (AlgHom.id F E) a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul m x => simp [← TensorProduct.add_tmul, h]
    | add a b ha hb =>
      simp only [map_add]
      rw [add_add_add_comm, ← ha, ← hb]
  rw [key a, h1, h2]; simp

theorem adele_tensor_ext {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (a : AF F ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) a = 0)
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) a = 0) : a = 0 :=
  tensor_prod_ext (fstA F) (sndA F) (LinearMap.inl F (Ainf F) (Af F)) (LinearMap.inr F (Ainf F) (Af F))
    (fun x => Prod.ext (add_zero x.1) (zero_add x.2)) a h1 h2

theorem star_sqrtMinusD (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have := D.host.isCMField_hostE
  have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
  rw [h2, map_neg, h1]
  simp

theorem sqrt_d_pos (D : D7) : 0 < Real.sqrt D.host.d :=
  Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))

theorem sqrtMinusD_ne (D : D7) : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [h, map_zero] at h1
  have := congrArg Complex.im h1
  have h2 := sqrt_d_pos D
  simp only [Complex.zero_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.ofReal_re] at this
  linarith

theorem host_span (D : D7) (x : D.host.E) :
    ∃ u v : D.host.F, x = u • (1 : D.host.E) + v • D.host.sqrtMinusD := by
  have hδ := sqrtMinusD_ne D
  have h2 : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  obtain ⟨u, hu⟩ := (D.sp.cm.fixed ((x + star x) / 2)).1 (by
    show star ((x + star x) / 2) = _
    rw [star_div₀, star_add, star_star, h2, add_comm])
  obtain ⟨v, hv⟩ := (D.sp.cm.fixed ((x - star x) / (2 * D.host.sqrtMinusD))).1 (by
    show star ((x - star x) / (2 * D.host.sqrtMinusD)) = _
    rw [star_div₀, star_sub, star_star, star_mul', h2, star_sqrtMinusD]
    field_simp
    ring)
  refine ⟨u, v, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def]
  erw [hu, hv]
  field_simp
  ring

variable {D : D7} {θ : InfFam D}

theorem comp_tmul (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : Ainf D.host.F) (y : D.host.E) :
    θ τ (a ⊗ₜ[D.host.F] y) = θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ y := by
  rw [← (hθ τ).1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

def emb (D : D7) (e : D.host.E) : Ainf D.host.F →+ AE D where
  toFun a := pairA D.host.F a 0 ⊗ₜ[D.host.F] e
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' a b := by
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext rfl (add_zero _).symm

theorem continuous_emb (e : D.host.E) : Continuous (emb D e) := by
  have h1 : Continuous fun a : Ainf D.host.F => pairA D.host.F a 0 :=
    Continuous.prodMk continuous_id continuous_const
  have h2 : Continuous fun a : AF D.host.F => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  refine (h2.comp h1).congr fun a => ?_
  show pairA D.host.F a 0 • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) = pairA D.host.F a 0 ⊗ₜ[D.host.F] e
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem finPart_emb (e : D.host.E) (a : Ainf D.host.F) : finPart D (emb D e a) = 0 :=
  TensorProduct.zero_tmul _ e

theorem infPart_emb (e : D.host.E) (a : Ainf D.host.F) : infPart D (emb D e a) = a ⊗ₜ[D.host.F] e := rfl

def reP (ι : Type) : (ι → ℂ) →+ (ι → ℝ) where
  toFun z i := (z i).re
  map_zero' := rfl
  map_add' _ _ := rfl

def imaginary (ι : Type) (c : ℝ) : (ι → ℂ) →+ (ι → ℝ) where
  toFun z i := (z i).im / c
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [add_div]

theorem exists_chart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ → (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) → (∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0) → ∃ σ : (D.what₂.Tau → ℂ) →+ AE D, Chart θ σ := by
  intro D θ hθ ρ hρ h1 h0
  have hd := sqrt_d_pos D
  let σ : (D.what₂.Tau → ℂ) →+ AE D :=
    { toFun := fun z => emb D 1 (ρ (reP _ z)) + emb D D.host.sqrtMinusD (ρ (imaginary _ (Real.sqrt D.host.d) z))
      map_zero' := by rw [(reP _).map_zero, (imaginary _ _).map_zero, ρ.map_zero, (emb D _).map_zero, (emb D _).map_zero, add_zero]
      map_add' := fun x y => by
        rw [(reP _).map_add, (imaginary _ _).map_add, ρ.map_add, ρ.map_add, (emb D _).map_add, (emb D _).map_add,
          add_add_add_comm] }
  have hσ : ∀ z, σ z = emb D 1 (ρ (reP _ z)) + emb D D.host.sqrtMinusD (ρ (imaginary _ (Real.sqrt D.host.d) z)) :=
    fun _ => rfl
  refine ⟨σ, hθ, ?_, fun z => ?_, fun z τ => ?_, fun a hf hi => ?_⟩
  · have c1 : Continuous (reP D.what₂.Tau) :=
      continuous_pi fun τ => Complex.continuous_re.comp (continuous_apply τ)
    have c2 : Continuous (imaginary D.what₂.Tau (Real.sqrt D.host.d)) :=
      continuous_pi fun τ => (Complex.continuous_im.comp (continuous_apply τ)).div_const _
    exact ((continuous_emb _).comp (hρ.comp c1)).add ((continuous_emb _).comp (hρ.comp c2))
  · rw [hσ, RingHom.map_add, finPart_emb, finPart_emb, add_zero]
  · rw [hσ, RingHom.map_add, infPart_emb, infPart_emb, RingHom.map_add, comp_tmul hθ τ _ D.host.sqrtMinusD, h1, h1,
      tauE_sqrtMinusD]
    show ((z τ).re : ℂ) + (((z τ).im / Real.sqrt D.host.d : ℝ) : ℂ) * _ = _
    have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [Complex.ofReal_div, mul_comm Complex.I, ← mul_assoc, div_mul_cancel₀ _ h2, Complex.re_add_im]
  · obtain ⟨b₀, b₁, hb⟩ := tensor_span D.host.sqrtMinusD (host_span D) (infPart D a)
    have key : ∀ τ, θ τ (b₀ ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 ∧ θ τ (b₁ ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
      intro τ
      have e := hi τ
      rw [hb, RingHom.map_add, comp_tmul hθ τ _ D.host.sqrtMinusD, tauE_sqrtMinusD] at e
      have r0 := Complex.conj_eq_iff_im.1 (conj_tmul_one hθ τ b₀)
      have r1 := Complex.conj_eq_iff_im.1 (conj_tmul_one hθ τ b₁)
      generalize θ τ (b₀ ⊗ₜ[D.host.F] (1 : D.host.E)) = p at *
      generalize θ τ (b₁ ⊗ₜ[D.host.F] (1 : D.host.E)) = q at *
      generalize Real.sqrt D.host.d = s at *
      have e1 := congrArg Complex.re e
      have e2 := congrArg Complex.im e
      simp [r0, r1, hd.ne'] at e1 e2
      exact ⟨Complex.ext e1 r0, Complex.ext e2 r1⟩
    have z0 := h0 b₀ fun τ => (key τ).1
    have z1 := h0 b₁ fun τ => (key τ).2
    rw [z0, z1] at hb
    exact adele_tensor_ext a (hb.trans (zero_tmul_add _ _)) hf

end GlobalTheory.FockCompare.RealChart

end
