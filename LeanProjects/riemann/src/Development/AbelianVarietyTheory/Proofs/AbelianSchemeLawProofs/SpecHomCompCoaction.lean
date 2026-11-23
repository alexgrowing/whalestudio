import Mathlib

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TensorProduct Algebra.TensorProduct

namespace GlobalTheory.AffineQuotient

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

abbrev specOver (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    Over (Spec (CommRingCat.of R)) :=
  (Spec (.of S)).asOver (Spec (.of R))

section

variable {S T T' : Type} [CommRing S] [CommRing T] [CommRing T'] [Algebra R S] [Algebra R T]
  [Algebra R T']

def specHom (φ : S →ₐ[R] T) : specOver R T ⟶ specOver R S :=
  (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver _

lemma specHom_left (φ : S →ₐ[R] T) :
    (specHom φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

lemma specHom_comp (φ : S →ₐ[R] T) (ψ : T →ₐ[R] T') :
    specHom (ψ.comp φ) = specHom ψ ≫ specHom φ := by
  ext1
  rw [Over.comp_left, specHom_left, specHom_left, specHom_left, ← Spec.map_comp]
  rfl

lemma specHom_injective : Function.Injective (specHom : (S →ₐ[R] T) → _) := by
  intro φ ψ h
  have := Spec.map_injective congr(($h).left)
  ext x
  exact congr($this x)

end

variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]

lemma specHom_lift_comul {T : Type} [CommRing T] [Algebra R T] (φ ψ : Λ →ₐ[R] T) :
    specHom ((Algebra.TensorProduct.lift φ ψ fun _ _ ↦ .all _ _).comp
      (Bialgebra.comulAlgHom R Λ)) = specHom φ * specHom ψ := by
  have := (Spec.mapMulEquiv (R := R) (S := Λ) (T := T)).map_mul (WithConv.toConv φ)
    (WithConv.toConv ψ)
  refine Eq.trans ?_ this
  change specHom _ = specHom _
  congr 1
  rw [AlgHom.convMul_def, ← AlgHom.comp_assoc]
  congr 1
  ext <;> simp

lemma specHom_counit {T : Type} [CommRing T] [Algebra R T] :
    specHom ((Algebra.ofId R T).comp (Bialgebra.counitAlgHom R Λ)) =
      toUnit _ ≫ η[specOver R Λ] := by
  ext1
  rw [Over.comp_left, one_spec_asOver_spec_left, specHom_left]
  exact Spec.map_comp (CommRingCat.ofHom (Bialgebra.counitAlgHom R Λ).toRingHom)
    (CommRingCat.ofHom (algebraMap R T))

variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A]
  (i : specOver R Λ ⟶ A) (v : specOver R B ⟶ A) (ρ : B →ₐ[R] B ⊗[R] Λ)
  (hρ : specHom ρ ≫ v = (specHom includeRight ≫ i) * (specHom includeLeft ≫ v))

include hρ

lemma specHom_comp_coaction {T : Type} [CommRing T] [Algebra R T] (φ : B ⊗[R] Λ →ₐ[R] T) :
    specHom (φ.comp ρ) ≫ v =
      (specHom (φ.comp includeRight) ≫ i) * (specHom (φ.comp includeLeft) ≫ v) := by
  rw [specHom_comp, specHom_comp, specHom_comp, Category.assoc, hρ, comp_mul, Category.assoc,
    Category.assoc]

lemma coaction_counit [IsMonHom i] [Mono v] (b : B) :
    TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b := by
  let φ : B ⊗[R] Λ →ₐ[R] B := Algebra.TensorProduct.lift (AlgHom.id R B)
    ((Algebra.ofId R B).comp (Bialgebra.counitAlgHom R Λ)) fun _ _ ↦ .all _ _
  have h := specHom_comp_coaction i v ρ hρ φ
  rw [lift_comp_includeRight', lift_comp_includeLeft, specHom_counit, Category.assoc,
    IsMonHom.one_hom, ← Hom.one_def, _root_.one_mul, cancel_mono] at h
  have h1 : φ (ρ b) = b := congr($(specHom_injective h) b)
  refine Eq.trans ?_ h1
  generalize ρ b = z
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [φ, Algebra.smul_def, _root_.mul_comm]

lemma coaction_assoc [IsCommMonObj A] [IsMonHom i] [Mono v] (b : B) :
    TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b) := by
  let l : B →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeLeft
  let r₁ : Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeRight.comp includeLeft
  let r₂ : Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeRight.comp includeRight
  let φ₀ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := Algebra.TensorProduct.lift l r₁ fun _ _ ↦ .all _ _
  let φ₁ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) :=
    Algebra.TensorProduct.lift (φ₀.comp ρ) r₂ fun _ _ ↦ .all _ _
  let φ₂ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) :=
    Algebra.TensorProduct.lift l ((Algebra.TensorProduct.lift r₁ r₂ fun _ _ ↦ .all _ _).comp
      (Bialgebra.comulAlgHom R Λ)) fun _ _ ↦ .all _ _
  have h₀ := specHom_comp_coaction i v ρ hρ φ₀
  have h₁ := specHom_comp_coaction i v ρ hρ φ₁
  have h₂ := specHom_comp_coaction i v ρ hρ φ₂
  rw [lift_comp_includeRight', lift_comp_includeLeft] at h₀ h₁ h₂
  rw [h₀, ← _root_.mul_assoc, _root_.mul_comm (specHom r₂ ≫ i), ← MonObj.mul_comp] at h₁
  rw [specHom_lift_comul, ← h₁, cancel_mono] at h₂
  have h : φ₂ (ρ b) = φ₁ (ρ b) := congr($(specHom_injective h₂) b)
  have e₁ (z : B ⊗[R] Λ) :
      TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ z) = φ₁ z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, φ₁,
        Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply]
      generalize ρ x = w
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, add_tmul, add_mul, hx, hy]
      | tmul x y => simp [φ₀, l, r₁, r₂]
  have e₂ (z : B ⊗[R] Λ) : (Coalgebra.comul (R := R) (A := Λ)).lTensor B z = φ₂ z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [LinearMap.lTensor_tmul, φ₂, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
        Bialgebra.comulAlgHom_apply]
      generalize Coalgebra.comul (R := R) y = w
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, tmul_add, mul_add, hx, hy]
      | tmul x y => simp [l, r₁, r₂]
  rw [e₁, e₂, h]

lemma coaction_free [Mono i] [Module.Finite R Λ] :
    Function.Surjective (productMap (includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) := by
  let m := productMap (includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ
  have : Epi (CommRingCat.ofHom m.toRingHom) := by
    refine ⟨fun {T} φ ψ h ↦ ?_⟩
    have hm (z) : φ (m z) = ψ (m z) := congr($h z)
    let : Algebra R T := (φ.hom.comp (algebraMap R (B ⊗[R] Λ))).toAlgebra
    let φ' : B ⊗[R] Λ →ₐ[R] T := ⟨φ.hom, fun _ ↦ rfl⟩
    let ψ' : B ⊗[R] Λ →ₐ[R] T := ⟨ψ.hom, fun r ↦ by
      have := hm (algebraMap R _ r)
      rw [AlgHom.commutes] at this
      exact this.symm⟩
    have h₁ : φ'.comp includeLeft = ψ'.comp (includeLeft : B →ₐ[R] B ⊗[R] Λ) := by
      ext b
      have := hm (b ⊗ₜ 1)
      rw [productMap_left_apply] at this
      exact this
    have h₂ : φ'.comp ρ = ψ'.comp ρ := by
      ext b
      have := hm (1 ⊗ₜ b)
      rw [productMap_right_apply] at this
      exact this
    have h₃ := specHom_comp_coaction i v ρ hρ φ'
    rw [h₂, h₁, specHom_comp_coaction i v ρ hρ ψ', mul_left_inj, cancel_mono] at h₃
    have h₄ := specHom_injective h₃
    have : φ' = ψ' := Algebra.TensorProduct.ext h₁ h₄.symm
    ext1
    exact congr(($this).toRingHom)
  refine RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom m.toRingHom) ?_
  refine RingHom.Finite.of_comp_finite
    (f := (includeLeftRingHom : B →+* B ⊗[R] B)) ?_
  have : (CommRingCat.ofHom m.toRingHom).hom.comp (includeLeftRingHom : B →+* B ⊗[R] B) =
      algebraMap B (B ⊗[R] Λ) := by
    ext b
    simp [m]
  rw [this, RingHom.finite_algebraMap]
  infer_instance

omit hρ in

lemma isPushout_equalizer {T : Type} [CommRing T] [Algebra R T] (α β : B →ₐ[R] T)
    (h₁ : Function.Surjective (productMap β α))
    (h₂ : RingHom.ker (productMap β α) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer α β,
      z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}) :
    IsPushout (CommRingCat.ofHom (α.toRingHom.eqLocus β.toRingHom).subtype)
      (CommRingCat.ofHom (α.toRingHom.eqLocus β.toRingHom).subtype)
      (CommRingCat.ofHom α.toRingHom) (CommRingCat.ofHom β.toRingHom) := by
  refine ⟨⟨by ext x; exact x.2⟩, ⟨PushoutCocone.isColimitAux' _ fun s ↦ ?_⟩⟩
  have hs (b : B) (hb : α b = β b) : s.inl b = s.inr b := congr($(s.condition) ⟨b, hb⟩)
  let : Algebra R s.pt := (s.inl.hom.comp (algebraMap R B)).toAlgebra
  let φ : B →ₐ[R] s.pt := ⟨s.inl.hom, fun _ ↦ rfl⟩
  let ψ : B →ₐ[R] s.pt := ⟨s.inr.hom, fun r ↦ (hs _ (by simp)).symm⟩
  have hk : RingHom.ker (productMap β α).toRingHom ≤ RingHom.ker (productMap ψ φ).toRingHom := by
    refine h₂.le.trans (Ideal.span_le.2 ?_)
    rintro _ ⟨b, hb, rfl⟩
    have : ψ b = φ b := (hs b hb).symm
    simpa [sub_eq_zero, RingHom.mem_ker] using this
  let d : T →+* s.pt := (productMap β α).toRingHom.liftOfSurjective h₁
    ⟨(productMap ψ φ).toRingHom, hk⟩
  have hd (z) : d (productMap β α z) = productMap ψ φ z :=
    RingHom.liftOfRightInverse_comp_apply (productMap β α).toRingHom _ _ _ z
  refine ⟨CommRingCat.ofHom d, ?_, ?_, fun {m} hm₁ hm₂ ↦ ?_⟩
  · ext b
    have := hd (1 ⊗ₜ b)
    rw [productMap_right_apply, productMap_right_apply] at this
    exact this
  · ext b
    have := hd (b ⊗ₜ 1)
    rw [productMap_left_apply, productMap_left_apply] at this
    exact this
  · ext t
    obtain ⟨z, rfl⟩ := h₁ t
    refine Eq.trans ?_ (hd z).symm
    have e₁ (b) : m.hom (α b) = φ b := congr($hm₁ b)
    have e₂ (b) : m.hom (β b) = ψ b := congr($hm₂ b)
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      rw [productMap_apply_tmul, productMap_apply_tmul, ← e₁, ← e₂]
      exact map_mul m.hom _ _

end GlobalTheory.AffineQuotient
