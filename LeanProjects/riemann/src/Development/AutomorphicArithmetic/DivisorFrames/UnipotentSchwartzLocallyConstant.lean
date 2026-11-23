import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerActionLocallyConstant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

theorem UpperTheory.unipotent_schwartz_locally_constant :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
        (H : Plane E n n₁) (H' : Plane E d d₁), Continuous B.ψ → ∀ (v : Pl F), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        IsLocallyConstant fun s : Fv F v ⊗[F] E => locOp v (M.co.rho B.ψ (partFin v (uS σ H H' v s))) φ := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W M H H' hc v φ hφ
  have hχl : IsLocallyConstant (GlobalTheory.LatVac.psiAt B.ψ v) :=
    GlobalTheory.SchrSB.isLocallyConstant_addChar _ (GlobalTheory.SchrSB.continuous_psiAt B.ψ hc v)
  have hχ0 : ∀ᶠ y in 𝓝 (0 : Fv F v), GlobalTheory.LatVac.psiAt B.ψ v y = 1 := by simpa using hχl.eventually_eq 0
  have hS := GlobalTheory.SchrLocConst.schr_isLocallyConstant _ hχ0 φ hφ
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  let L : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun s => GlobalTheory.LatVac.locCo M.co v (uS σ H H' v s)
      map_add' := fun s t => by rw [uS, uS, uS, map_add, map_add, add_smul, map_add]
      map_smul' := fun a t => by
        rw [RingHom.id_apply, ← GlobalTheory.VanishLocCont.locCo_smul, uS, uS, GlobalTheory.VanishLocCont.liftT_smul, map_smul (cA σ),
          smul_assoc] }
  have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
  have h := hS.comp_continuous hL
  convert h using 1
  funext s
  rw [(locOp_rho M.co hc v _ hφ).2]
  rfl
