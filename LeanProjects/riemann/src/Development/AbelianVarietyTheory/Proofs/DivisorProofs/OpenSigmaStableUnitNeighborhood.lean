import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAEMulMem
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.IdeleCongr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intAE_mul {s t : FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hs : s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) (ht : t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : s * t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  first
  | exact @_root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem
  | exact _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem
  | (apply _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem ..)

theorem intAE_one : (1 : FiniteAdeleRing (𝓞 F) F ⊗[F] E) ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  refine AddSubgroup.subset_closure ⟨1, fun v => ?_, 1, ?_⟩
  · rw [map_one]; exact one_mem _
  · rw [Algebra.TensorProduct.one_def]; simp

theorem intAE_nat (m : ℕ) : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  rw [← nsmul_one]; exact nsmul_mem intAE_one m

theorem sigR_intAE (σ : E →ₐ[F] E) {z : FiniteAdeleRing (𝓞 F) F ⊗[F] E} (h : z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, RingOfIntegers.mapRingHom (σ : E →+* E) x, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_cA (σ : E →ₐ[F] E) (y : AdeleRing (𝓞 F) F ⊗[F] E) : HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.cA σ y) = HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ (HeckeCharacterZeroLocus.ThmBIn.finPart F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

end GlobalTheory.IdeleCongr

namespace GlobalTheory.IdeleCongr

theorem exists_open_congruence_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (m : ℕ), 0 < m → ∃ U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, IsOpen (U : Set (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) ∧
      (∀ x ∈ U, Units.map (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ).toRingHom.toMonoidHom x ∈ U) ∧
      ∀ x ∈ U, ∃ s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E,
        HeckeCharacterZeroLocus.ThmBIn.finPart F E (x : AdeleRing (𝓞 F) F ⊗[F] E) = 1 + (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * s := by
  intro F E _ _ _ _ _ σ m hm
  haveI : IsModuleTopology (HeckeCharacterZeroLocus.ThmBIn.AF F) (HeckeCharacterZeroLocus.ThmBIn.AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (HeckeCharacterZeroLocus.ThmBIn.AE F E) := IsModuleTopology.isTopologicalRing (HeckeCharacterZeroLocus.ThmBIn.AF F) _
  obtain ⟨Φ, hΦc, -, hint⟩ := GlobalTheory.HeckeInhabitant.exists_fin (F := F) (E := E)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  let c : FiniteAdeleRing (𝓞 F) F ⊗[F] E := HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹)
  have hmc : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * c = 1 := by
    have : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) = HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)) := by
      rw [map_natCast, map_natCast]
    rw [this, ← map_mul, ← map_mul, mul_inv_cancel₀ hm0, map_one, map_one]
  let C : AdeleRing (𝓞 F) F ⊗[F] E → Prop := fun y =>
    (HeckeCharacterZeroLocus.ThmBIn.finPart F E y - 1) * c ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E
  have hdec : ∀ z : FiniteAdeleRing (𝓞 F) F ⊗[F] E, z = 1 + m * ((z - 1) * c) := fun z => by
    linear_combination (1 - z) * hmc
  have hint' : ∀ y, C y → HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := fun y hy => by
    rw [hdec (HeckeCharacterZeroLocus.ThmBIn.finPart F E y)]
    exact add_mem intAE_one (intAE_mul (intAE_nat m) hy)
  have hCmul : ∀ y z, C y → C z → C (y * z) := fun y z hy hz => by
    have e : (HeckeCharacterZeroLocus.ThmBIn.finPart F E (y * z) - 1) * c = HeckeCharacterZeroLocus.ThmBIn.finPart F E y * ((HeckeCharacterZeroLocus.ThmBIn.finPart F E z - 1) * c)
        + (HeckeCharacterZeroLocus.ThmBIn.finPart F E y - 1) * c := by
      rw [map_mul]; ring
    show _ ∈ _
    rw [e]
    exact add_mem (intAE_mul (hint' y hy) hz) hy
  have hC1 : C 1 := by
    show _ ∈ _
    rw [map_one, sub_self, zero_mul]
    exact zero_mem _
  let U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ :=
    { carrier := {x | C x ∧ C ((x⁻¹ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) : AdeleRing (𝓞 F) F ⊗[F] E)}
      one_mem' := ⟨by rw [Units.val_one]; exact hC1, by rw [inv_one, Units.val_one]; exact hC1⟩
      mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul]; exact hCmul _ _ hx.1 hy.1,
        by rw [mul_inv_rev, Units.val_mul]; exact hCmul _ _ hy.2 hx.2⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩ }
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hcont : Continuous fun y : AdeleRing (𝓞 F) F ⊗[F] E => (y - 1) * HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹ :=
    (continuous_id.sub continuous_const).mul continuous_const
  have hCo : IsOpen {y | C y} := by
    have h1 : IsOpen {y : AdeleRing (𝓞 F) F ⊗[F] E |
        ∀ P, Valued.v (Φ ((y - 1) * HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹) P) ≤ 1} := (hO.preimage hΦc).preimage hcont
    convert h1 using 1
    ext y
    simp only [Set.mem_setOf_eq]
    rw [← hint, map_mul, map_sub, map_one]
  have hσ : ∀ y, (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) y
      = HeckeCharacterZeroLocus.ThmBIn.cA σ y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => rfl
  have hsc : HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ c = c := by
    change HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ (HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹)) = _
    rw [← finPart_cA, GlobalTheory.HeckeInhabitant.cA_inc, map_inv₀, map_natCast]
  have hCσ : ∀ y, C y → C (HeckeCharacterZeroLocus.ThmBIn.cA σ y) := fun y hy => by
    show _ ∈ _
    rw [finPart_cA, ← hsc, ← map_one (HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ), ← map_sub, ← map_mul]
    exact sigR_intAE σ hy
  refine ⟨U, ?_, fun x hx => ⟨?_, ?_⟩, fun x hx => ⟨_, hx.1, hdec _⟩⟩
  · exact (hCo.preimage Units.continuous_val).inter (hCo.preimage Units.continuous_coe_inv)
  · change C ((Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) (x : AdeleRing (𝓞 F) F ⊗[F] E))
    rw [hσ]; exact hCσ _ hx.1
  · rw [← map_inv]
    change C ((Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) ((x⁻¹ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) : AdeleRing (𝓞 F) F ⊗[F] E))
    rw [hσ]; exact hCσ _ hx.2

end GlobalTheory.IdeleCongr
