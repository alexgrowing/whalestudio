import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointResPf

noncomputable section
namespace LateralTheory.E.LeafCoordsPointResPf
open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (P : Ideal B) [P.IsPrime]

def delta0 (hIP : I ≤ P) : I →ₗ[B] P.ResidueField ⊗[B] Ω[B⁄A] where
  toFun x := (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)
  map_add' x y := by simp [TensorProduct.tmul_add]
  map_smul' b x := by
    simp only [SetLike.val_smul, smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, RingHom.id_apply]
    have : (1 : P.ResidueField) ⊗ₜ[B] ((x : B) • KaehlerDifferential.D A B b) = 0 := by
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
        Ideal.algebraMap_residueField_eq_zero.mpr (hIP x.2), TensorProduct.zero_tmul]
    rw [this, add_zero, TensorProduct.tmul_smul]

def delta (hIP : I ≤ P) : P.ResidueField ⊗[B] I →ₗ[P.ResidueField] P.ResidueField ⊗[B] Ω[B⁄A] :=
  LinearMap.liftBaseChange P.ResidueField (delta0 (A := A) I P hIP)

theorem delta_tmul (hIP : I ≤ P) (k : P.ResidueField) (x : I) :
    delta (A := A) I P hIP (k ⊗ₜ x) = k • ((1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) := by
  simp [delta, delta0]

def cot (hIP : I ≤ P) : (RingHom.ker (algebraMap B (B ⧸ I))).Cotangent →ₗ[B] P.ResidueField ⊗[B] I :=
  Submodule.liftQ _ ((TensorProduct.mk B P.ResidueField I 1) ∘ₗ
    Submodule.inclusion (p := RingHom.ker (algebraMap B (B ⧸ I))) (p' := I)
      (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hx))) (by
    intro z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro a ha m _
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.map_smul_of_tower]
      rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
        Ideal.algebraMap_residueField_eq_zero.mpr (hIP (Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp ha))),
        TensorProduct.zero_tmul]
    · intro x y hx hy; exact add_mem hx hy)

theorem delta_injective (n m : ℕ) (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B)
    (hBI : Algebra.IsStandardSmoothOfRelativeDimension m A (B ⧸ I)) (hIP : I ≤ P) :
    Function.Injective (delta (A := A) I P hIP) := by
  obtain ⟨l, hl⟩ := conormal_retraction I n m hB hBI
  let ρ0 : Ω[B⁄A] →ₗ[B] P.ResidueField ⊗[B] I :=
    cot I P hIP ∘ₗ (l.restrictScalars B) ∘ₗ TensorProduct.mk B (B ⧸ I) Ω[B⁄A] 1
  let ρ := LinearMap.liftBaseChange P.ResidueField ρ0
  have h1 : ∀ x : I, ρ ((1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) =
      (1 : P.ResidueField) ⊗ₜ[B] x := by
    intro x
    have hx : (x : B) ∈ RingHom.ker (algebraMap B (B ⧸ I)) :=
      RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr x.2)
    have e1 : (1 : B ⧸ I) ⊗ₜ[B] KaehlerDifferential.D A B (x : B) =
        KaehlerDifferential.kerCotangentToTensor A B (B ⧸ I)
          ((RingHom.ker (algebraMap B (B ⧸ I))).toCotangent ⟨x, hx⟩) :=
      (KaehlerDifferential.kerCotangentToTensor_toCotangent A B (B ⧸ I) ⟨x, hx⟩).symm
    have e2 := LinearMap.congr_fun hl ((RingHom.ker (algebraMap B (B ⧸ I))).toCotangent ⟨x, hx⟩)
    simp only [ρ, ρ0, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.mk_apply, LinearMap.coe_restrictScalars]
    rw [e1]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at e2
    rw [e2]
    rfl
  have key : ∀ z, ρ (delta (A := A) I P hIP z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k x =>
      rw [delta_tmul, LinearMap.map_smul, h1, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact Function.LeftInverse.injective key

theorem range_delta (hIP : I ≤ P) : LinearMap.range (delta (A := A) I P hIP) =
    Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) := by
  rw [LinearMap.range_eq_map, ← span_one_tmul (M := I) P, Submodule.map_span, ← Set.range_comp]
  congr 1; ext; simp [delta_tmul]

def LeafResSpanD : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P →
    FiniteDimensional P.ResidueField (Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))) ∧
    Module.finrank P.ResidueField (Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))) ≤ d

theorem LeafResDimI_of (hS : LeafResSpanD) : LeafResDimI := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  obtain ⟨hfin, hle⟩ := hS d e A B I hB hBI P hIP
  have hinj := delta_injective (A := A) I P _ _ hB hBI hIP
  have e := LinearEquiv.ofInjective _ hinj
  rw [range_delta] at e
  have : FiniteDimensional P.ResidueField (P.ResidueField ⊗[B] I) := LinearEquiv.finiteDimensional e.symm
  rw [e.finrank_eq]; exact hle

theorem LeafCoordsPointRes_of'' (hS : LeafResSpanD) (hY : LeafResY) : LeafCoordsPointRes :=
  LeafCoordsPointRes_of' (LeafResDimI_of hS) hY

end LateralTheory.E.LeafCoordsPointResPf
