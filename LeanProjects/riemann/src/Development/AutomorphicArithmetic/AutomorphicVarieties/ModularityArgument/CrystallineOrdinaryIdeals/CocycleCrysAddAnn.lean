import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankDualInvariantsScalarRepEqFinrankKerSmulStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SpanCharacterSubCyclotomicEqOfPositiveWeightStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.PositiveScalarRepOfCharacterPositiveWeightStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleMemCrystallineSupSubrepOfPositiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology TensorProduct

noncomputable section
namespace GlobalTheory.CrysAnn

variable {l : ℕ} [Fact l.Prime]

theorem actC_resCoef {G E B : Type} [Group G] [Field E] [Algebra ℚ_[l] E] [CommRing B] [Algebra ℚ_[l] B]
    [Algebra E B] [IsScalarTower ℚ_[l] E B] (φ : G →* GQ l) (ρ : Representation B G B) (g : G)
    (y : B ⊗[ℚ_[l]] Bcr l) : actC φ (resCoef E ρ) g y = actC φ ρ g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [actC, resCoef]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def smulRep {G E B : Type} [Group G] [Field E] [CommRing B] [Algebra E B] (N : Type) [AddCommGroup N]
    [Module B N] [Module E N] [IsScalarTower E B N] (χ : G →* Bˣ) : Representation E G N where
  toFun g := (LinearMap.lsmul B N (χ g : B)).restrictScalars E
  map_one' := by ext; simp
  map_mul' g h := by
    ext x
    simp [mul_smul]
    exact smul_comm _ _ _

end GlobalTheory.CrysAnn

open GlobalTheory.CrysAnn in

theorem GlobalTheory.CrysAnn.cocycle_crys_add_ann : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → ∀ c ∈ Z1 (chRep χ), ∃ c' : G → B, (∀ g, ((χ σ : B) - (cycA l l B (φ σ) : B)) * c' g = 0) ∧ c - c' ∈ finiteCocycles φ (chRep χ) ∧ (2 ≤ w → c' = 0) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχc w hw hχI σ hσ c hc
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  set δ : B := if w = 1 then (χ σ : B) - (cycA l l B (φ σ) : B) else 1 with hδ
  have hspan : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (((cycA l l E).comp φ g : Eˣ) : E)) =
      Ideal.span {δ} := by
    have h := GlobalTheory.T.span_character_sub_cyclotomic_eq_of_positive_weight φ hφ π hπ χ hχc w hw hχI σ hσ
    have e : ∀ g, algebraMap E B (((cycA l l E).comp φ g : Eˣ) : E) = (cycA l l B (φ g) : B) := fun g =>
      congrArg Units.val (algebraMap_cycA (E := E) (B := B) (φ g))
    simp only [e, h, hδ]
    split_ifs <;> simp
  let I : Submodule B B := LinearMap.ker (LinearMap.lsmul B B δ)
  letI : TopologicalSpace I := moduleTopology ℚ_[l] I
  haveI : IsModuleTopology ℚ_[l] I := ⟨rfl⟩
  haveI : IsTopologicalAddGroup I := IsModuleTopology.topologicalAddGroup ℚ_[l] I
  haveI : ContinuousConstSMul E I := ⟨fun a => IsModuleTopology.continuous_of_linearMap
    ((LinearMap.lsmul E I a).restrictScalars ℚ_[l])⟩
  haveI : FiniteDimensional ℚ_[l] I :=
    Module.Finite.of_injective (I.subtype.restrictScalars ℚ_[l]) Subtype.val_injective
  let ρV : Representation E G B := resCoef E (chRep χ)
  let ρW : Representation E G I := smulRep I χ
  have hV := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ χ hχc w hw hχI ρV (fun g x => rfl)
  have hW := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ χ hχc w hw hχI ρW (fun g x => rfl)
  have dV := GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul χ ((cycA l l E).comp φ) ρV (fun g x => rfl) δ hspan
  have dW := GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul χ ((cycA l l E).comp φ) ρW (fun g x => rfl) δ hspan
  have kW : LinearMap.ker ((LinearMap.lsmul B I δ).restrictScalars E) = ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact Subtype.ext x.2
  have hdim : finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρV) := by
    rw [dV, dW, kW, finrank_top]
    exact (LinearEquiv.refl E I).finrank_eq
  let i : I →ₗ[E] B := I.subtype.restrictScalars E
  obtain ⟨cW, -, hf⟩ := GlobalTheory.T.cocycle_mem_crystalline_sup_subrep_of_positive hP φ hφ ρW ρV hW.1 hV.1 hW.2 hV.2 i Subtype.val_injective
    (fun g x => rfl) hdim c hc
  have hz : w ≠ 1 → ∀ g, (cW g : B) = 0 := by
    intro h1 g
    have := (cW g).2
    simp only [I, LinearMap.mem_ker, LinearMap.lsmul_apply, hδ, if_neg h1, one_smul] at this
    exact this
  refine ⟨fun g => (cW g : B), fun g => ?_, ?_, fun h2 => funext fun g => hz (by omega) g⟩
  · by_cases h1 : w = 1
    · have := (cW g).2
      simp only [I, LinearMap.mem_ker, LinearMap.lsmul_apply, hδ, if_pos h1, smul_eq_mul] at this
      exact this
    · show _ * (cW g : B) = 0
      rw [hz h1 g, mul_zero]
  · obtain ⟨⟨hc1, hc2⟩, x, hx⟩ := hf
    exact ⟨⟨hc1, hc2⟩, x, fun g => (hx g).trans (by rw [actC_resCoef])⟩
