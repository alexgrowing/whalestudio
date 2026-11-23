import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

abbrev thC (n : ℕ) : Monoid.End (GL (Fin n) ℂ) := thetaR (starRingEnd ℂ) n

theorem nil_sq_mul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ nilrad W₁ W₂) : X * X * X = 0 := by
  have h : ∀ y, (X * X * X) *ᵥ y = 0 := fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hX.2.2 _ (hX.2.1 _ (hX.1 y))
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

def uOf {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (X : nilrad W₁ W₂) : GL (Fin n) ℂ where
  val := 1 + X.1
  inv := 1 - X.1 + X.1 * X.1
  val_inv := by
    have h := nil_sq_mul X.2
    noncomm_ring
    rw [← mul_assoc, h]; simp
  inv_val := by
    have h := nil_sq_mul X.2
    noncomm_ring
    rw [← mul_assoc, h]; simp

@[simp] theorem uOf_val {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (X : nilrad W₁ W₂) :
    (uOf X).val = 1 + X.1 := rfl

theorem continuous_uOf {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} :
    Continuous (uOf : nilrad W₁ W₂ → GL (Fin n) ℂ) := by
  have h : Continuous fun X : nilrad W₁ W₂ => X.1 := continuous_subtype_val
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add h
  · have : Continuous fun X : nilrad W₁ W₂ => (1 - X.1 + X.1 * X.1 : Matrix (Fin n) (Fin n) ℂ) :=
      (continuous_const.sub h).add (h.matrix_mul h)
    exact this

def NilChange : Prop := ∀ (n : ℕ) (d : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thC n d).val.charpoly.Separable → W₁ ≠ ⊥ → W₁ ≤ W₂ →
  perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
  ∃ Φ : nilrad W₁ W₂ → nilrad W₁ W₂, Continuous Φ ∧
    (∀ X, uOf (Φ X) = (uOf X)⁻¹ * (d * thC n (uOf X) * d⁻¹)) ∧
    ∀ [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
      [ν.IsAddHaarMeasure], ∃ c : NNReal, ν.map Φ = (c : ENNReal) • ν

def QuotVanish : Prop := ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (μ : Measure (GL (Fin n) ℂ)) [μ.IsHaarMeasure] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thC n d).val.charpoly.Separable → W₁ ≠ ⊥ → W₁ ≤ W₂ →
  perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
  ∀ F : GL (Fin n) ℂ → ℂ, Measurable F → (∀ t ∈ twCent (thC n) d, ∀ x, F (t * x) = F x) →
    (∀ x k, thC n k = k → F (x * k) = F x) →
    (∀ [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
      [ν.IsAddHaarMeasure] (q : GL (Fin n) ℂ), ∫ X, F (uOf X * q) ∂ν = 0) →
    quotIntegral μ (twCent (thC n) d) μd F = 0

theorem mem_img' (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ img g W ↔ (g⁻¹ : GL (Fin n) ℂ).val *ᵥ y ∈ W := by
  have e1 : ∀ z : Fin n → ℂ, (g⁻¹ : GL (Fin n) ℂ).val *ᵥ (g.val *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  have e2 : ∀ z : Fin n → ℂ, g.val *ᵥ ((g⁻¹ : GL (Fin n) ℂ).val *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, e1]; exact hx
  · intro h
    exact ⟨_, h, by rw [Matrix.toLin'_apply, e2]⟩

theorem img_mul (a b : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    img (a * b) W = img a (img b W) := by
  ext y
  simp only [mem_img', _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem img_one (W : Submodule ℂ (Fin n → ℂ)) : img (1 : GL (Fin n) ℂ) W = W := by
  ext y
  simp [mem_img']

theorem thC_val (q : GL (Fin n) ℂ) : (thC n q).val = (q⁻¹ : GL (Fin n) ℂ).valᴴ := by
  rw [thC, thetaR_val]; ext i j; simp [Matrix.conjTranspose_apply]

theorem mem_perp' (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ perp (starRingEnd ℂ) W ↔ ∀ x ∈ W, star x ⬝ᵥ y = 0 := Iff.rfl

theorem perp_img (q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    perp (starRingEnd ℂ) (img q W) = img (thC n q) (perp (starRingEnd ℂ) W) := by
  have hi : ((thC n q)⁻¹ : GL (Fin n) ℂ).val = q.valᴴ := by
    rw [← map_inv, thC_val, inv_inv]
  ext y
  rw [mem_img', mem_perp', mem_perp', hi]
  constructor
  · intro h x hx
    have := h (q.val *ᵥ x) ⟨x, hx, by rw [Matrix.toLin'_apply]⟩
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at this
    exact this
  · rintro h _ ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    exact h x hx

theorem perpD_twConj (d q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    perpD (starRingEnd ℂ) (twConj (thC n) q d) (img q⁻¹ W) =
      img q⁻¹ (perpD (starRingEnd ℂ) d W) := by
  rw [perpD, perpD, perp_img, ← img_mul, twConj, map_inv]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [img_mul]

theorem img_le_img (g : GL (Fin n) ℂ) {W W' : Submodule ℂ (Fin n → ℂ)} (h : W ≤ W') :
    img g W ≤ img g W' := Submodule.map_mono h

theorem img_ne_bot (g : GL (Fin n) ℂ) {W : Submodule ℂ (Fin n → ℂ)} (h : W ≠ ⊥) : img g W ≠ ⊥ := by
  intro h0
  apply h
  have : img g⁻¹ (img g W) = W := by rw [← img_mul, inv_mul_cancel, img_one]
  rw [← this, h0]
  exact Submodule.map_bot _

theorem conj_mem (p : GL (Fin n) ℂ) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ nilrad W₁ W₂) :
    p.val * X * (p⁻¹ : GL (Fin n) ℂ).val ∈ nilrad (img p W₁) (img p W₂) := by
  have hpp : ∀ y : Fin n → ℂ, (p⁻¹ : GL (Fin n) ℂ).val *ᵥ (p.val *ᵥ y) = y := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  have e : ∀ y : Fin n → ℂ, (p.val * X * (p⁻¹ : GL (Fin n) ℂ).val) *ᵥ y =
      p.val *ᵥ (X *ᵥ ((p⁻¹ : GL (Fin n) ℂ).val *ᵥ y)) := fun y => by
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [e, mem_img', hpp]
    exact hX.1 _
  · rw [mem_img'] at hy
    rw [e, mem_img', hpp]
    exact hX.2.1 _ hy
  · rw [mem_img'] at hy
    rw [e, hX.2.2 _ hy, Matrix.mulVec_zero]

theorem img_inv_img (q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : img q (img q⁻¹ W) = W := by
  rw [← img_mul, mul_inv_cancel, img_one]

def cnF (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) := ⟨(q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val, by
    have := conj_mem q⁻¹ X.2
    rwa [inv_inv] at this⟩

def cnB (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    nilrad W₁ W₂ := ⟨q.val * Z.1 * (q⁻¹ : GL (Fin n) ℂ).val, by
    have := conj_mem q Z.2
    rwa [img_inv_img, img_inv_img] at this⟩

theorem cnF_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    (cnF q W₁ W₂ X).1 = (q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val := rfl

theorem cnB_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    (cnB q W₁ W₂ Z).1 = q.val * Z.1 * (q⁻¹ : GL (Fin n) ℂ).val := rfl

theorem cnF_add (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X Y : nilrad W₁ W₂) :
    cnF q W₁ W₂ (X + Y) = cnF q W₁ W₂ X + cnF q W₁ W₂ Y :=
  Subtype.ext (by
    simp only [Submodule.coe_add, cnF_val, mul_add, add_mul])

theorem cnB_add (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (X Y : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    cnB q W₁ W₂ (X + Y) = cnB q W₁ W₂ X + cnB q W₁ W₂ Y :=
  Subtype.ext (by
    simp only [Submodule.coe_add, cnB_val, mul_add, add_mul])

theorem cnB_cnF (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    cnB q W₁ W₂ (cnF q W₁ W₂ X) = X :=
  Subtype.ext (by
    have h1 : q.val * (q⁻¹ : GL (Fin n) ℂ).val = 1 := by rw [← Units.val_mul]; simp
    rw [cnB_val, cnF_val]
    calc _ = (q.val * (q⁻¹ : GL (Fin n) ℂ).val) * X.1 * (q.val * (q⁻¹ : GL (Fin n) ℂ).val) := by
          simp only [mul_assoc]
      _ = X.1 := by rw [h1]; simp)

theorem cnF_cnB (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) : cnF q W₁ W₂ (cnB q W₁ W₂ Z) = Z :=
  Subtype.ext (by
    have h1 : (q⁻¹ : GL (Fin n) ℂ).val * q.val = 1 := by rw [← Units.val_mul]; simp
    rw [cnF_val, cnB_val]
    calc _ = ((q⁻¹ : GL (Fin n) ℂ).val * q.val) * Z.1 * ((q⁻¹ : GL (Fin n) ℂ).val * q.val) := by
          simp only [mul_assoc]
      _ = Z.1 := by rw [h1]; simp)

def conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    nilrad W₁ W₂ ≃+ nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) :=
  AddMonoidHom.toAddEquiv (AddMonoidHom.mk' (cnF q W₁ W₂) (cnF_add q W₁ W₂))
    (AddMonoidHom.mk' (cnB q W₁ W₂) (cnB_add q W₁ W₂))
    (AddMonoidHom.ext fun X => cnB_cnF q W₁ W₂ X) (AddMonoidHom.ext fun Z => cnF_cnB q W₁ W₂ Z)
theorem conjNil_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    (conjNil q W₁ W₂ X).1 = (q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val := rfl

theorem continuous_conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    Continuous (conjNil q W₁ W₂) :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem continuous_conjNil_symm (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    Continuous (conjNil q W₁ W₂).symm :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem uOf_conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    uOf (conjNil q W₁ W₂ X) = q⁻¹ * uOf X * q := by
  apply Units.ext
  have h1 : (q⁻¹ : GL (Fin n) ℂ).val * q.val = 1 := by rw [← Units.val_mul]; simp
  simp only [uOf_val, conjNil_val, Units.val_mul, mul_add, add_mul, mul_one, h1]

theorem continuous_thC : Continuous (thC n) := by
  have hv : ∀ h : Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ),
      Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) := id
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : Continuous fun g : GL (Fin n) ℂ => (g⁻¹ : GL (Fin n) ℂ).valᴴ :=
      (Units.continuous_val.comp continuous_inv).matrix_conjTranspose
    exact this.congr fun g => (thC_val g).symm
  · have : Continuous fun g : GL (Fin n) ℂ => (g : GL (Fin n) ℂ).valᴴ :=
      Units.continuous_val.matrix_conjTranspose
    refine this.congr fun g => ?_
    have : (((thC n g)⁻¹ : GL (Fin n) ℂ)).val = g.valᴴ := by
      rw [← map_inv, thC_val, inv_inv]
    exact this.symm

end GlobalTheory.CompanionTheory.LocVan
end
