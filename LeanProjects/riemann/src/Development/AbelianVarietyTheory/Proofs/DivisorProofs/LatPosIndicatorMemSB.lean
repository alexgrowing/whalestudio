import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictionAndProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosHomApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ThK.AdaptEv.VacuumBlock

theorem latPos_indicator_mem_SB : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ) {ι κ₁ : Type} [Fintype ι] [Fintype κ₁]
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)) (eq : Fin n × Fin d ≃ ι ⊕ κ₁),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∀ v : Pl F, Set.indicator (GlobalTheory.ThK.AdaptEv.VacuumBlock.latPos X W co eq v : Set (ι → Fv F v)) 1 ∈ SB (ι → Fv F v) := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' ι κ₁ _ _ co eq hX hW hrat v
  obtain ⟨hOpen, hCpt⟩ := GlobalTheory.LatOpenCpt.main σ B X W r s r' s' hX hW
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.mk co (fun _ => 0) 0 ∅) hrat v
  set Λ := (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W v).map (GlobalTheory.LatVac.locCo co v) with hΛ
  let π : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → (ι → Fv F v) :=
    fun w i => w.1 (eq.symm (Sum.inl i))
  have hπc : Continuous π := by fun_prop
  have hπo : IsOpenMap π := by
    have h1 : IsOpenMap (fun w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) => w.1) := isOpenMap_fst
    have h2 : IsOpenMap (fun x : (Fin n × Fin d → Fv F v) => (blockHomeo (R := Fv F v) eq x).1) :=
      isOpenMap_fst.comp (blockHomeo (R := Fv F v) eq).isOpenMap
    exact h2.comp h1
  have hset : ((latPos X W co eq v : AddSubgroup (ι → Fv F v)) : Set (ι → Fv F v)) = π '' (Λ : Set _) := by
    simp only [latPos, AddSubgroup.coe_map]
    rfl
  have ho : IsOpen ((latPos X W co eq v : AddSubgroup (ι → Fv F v)) : Set (ι → Fv F v)) := by
    rw [hset]; exact hπo _ hOpen
  have hk : IsCompact ((latPos X W co eq v : AddSubgroup (ι → Fv F v)) : Set (ι → Fv F v)) := by
    rw [hset]; exact hCpt.image hπc
  have hc : IsClosed ((latPos X W co eq v : AddSubgroup (ι → Fv F v)) : Set (ι → Fv F v)) :=
    AddSubgroup.isClosed_of_isOpen _ ho
  generalize ((latPos X W co eq v : AddSubgroup (ι → Fv F v)) : Set (ι → Fv F v)) = U at ho hk hc ⊢
  refine ⟨IsLocallyConstant.iff_isOpen_fiber.2 fun y => ?_, ?_⟩
  · by_cases h1 : (1 : ℂ) = y
    · have : U.indicator 1 ⁻¹' {y} = U := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, ← h1]
      rw [this]; exact ho
    · by_cases h0 : (0 : ℂ) = y
      · have : U.indicator 1 ⁻¹' {y} = Uᶜ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, ← h0]
        rw [this]; exact hc.isOpen_compl
      · have : U.indicator 1 ⁻¹' {y} = ∅ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx] <;> assumption
        rw [this]; exact isOpen_empty
  · exact hk.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal Set.support_indicator_subset hc)

end GlobalTheory.ThK.AdaptEv.VacuumBlock
