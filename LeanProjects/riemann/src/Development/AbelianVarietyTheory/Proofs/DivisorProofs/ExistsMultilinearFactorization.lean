import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne

noncomputable section

namespace GlobalTheory.PureML

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F]

theorem eventually_evFin_mem (a : AF F) :
    ∀ᶠ v in Filter.cofinite, evFin F v a ∈ v.adicCompletionIntegers F :=
  a.2.2

theorem finprod_eq_mul {κ : Type} [Finite κ] (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hstd : ∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (T : Finset (Pl F)) (x : κ → AF F) :
    ∃ c : ℂ, ∀ (φ : ∀ v : T, (κ → Fv F v) → ℂ) (g : ∀ v : Pl F, (κ → Fv F v) → ℂ),
      (∀ v (h : v ∈ T), g v = φ ⟨v, h⟩) → (∀ v ∉ T, g v = vac v) →
      (∏ᶠ v, g v fun i => evFin F v (x i)) = c * ∏ v : T, φ v fun i => evFin F v.1 (x i) := by
  classical
  have hev : ∀ᶠ v in Filter.cofinite, vac v (fun i => evFin F v (x i)) = 1 := by
    have h1 : ∀ᶠ v in Filter.cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun i => eventually_evFin_mem (x i)
    filter_upwards [hstd, h1] with v hv h1v
    rw [hv]
    exact Set.indicator_of_mem (s := {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}) h1v 1
  have hS := Filter.eventually_cofinite.1 hev
  refine ⟨∏ v ∈ hS.toFinset \ T, vac v (fun i => evFin F v (x i)), fun φ g hT hout => ?_⟩
  have hsub : Function.mulSupport (fun v => g v fun i => evFin F v (x i)) ⊆ ↑(T ∪ (hS.toFinset \ T)) := by
    intro v hv
    by_contra hn
    simp only [Finset.coe_union, Finset.coe_sdiff, Set.Finite.coe_toFinset, Set.mem_union, Set.mem_diff,
      Set.mem_setOf_eq, Finset.mem_coe, not_or, not_and, not_not] at hn
    rw [Function.mem_mulSupport, hout v hn.1] at hv
    exact hv (not_not.1 fun h => hn.1 (hn.2 h))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_union Finset.disjoint_sdiff, mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => by rw [hout v (Finset.mem_sdiff.1 hv).2]
  · rw [← Finset.prod_coe_sort T]
    exact Finset.prod_congr rfl fun v _ => by rw [hT v.1 v.2]

end GlobalTheory.PureML

end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

theorem GlobalTheory.PureML.pure_multilinear : open Classical in ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ → ∀ T : Finset (Pl F), ∃ Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] MultilinearMap ℂ (fun v : T => (Fin n × Fin d → Fv F v) → ℂ) ((Fin n × Fin d → AF F) → ℂ), ∀ f φ, Ψ f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (fun v => if h : v ∈ T then φ ⟨v, h⟩ else M.vac v) := by
  intro F E _ _ _ _ _ σ n d Y W M ψ hM T
  choose c hc using fun x => GlobalTheory.PureML.finprod_eq_mul M.vac hM.std T x
  let P : (Fin n × Fin d → AF F) → MultilinearMap ℂ (fun v : T => (Fin n × Fin d → Fv F v) → ℂ) ℂ :=
    fun x => (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap
      (fun v => LinearMap.proj (R := ℂ) (φ := fun _ : (Fin n × Fin d → Fv F v.1) => ℂ) (fun i => evFin F v.1 (x i)))
  refine ⟨{ toFun := fun f => MultilinearMap.pi (fun x => (f (fun i => evI F (x i)) * c x) • P x),
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro f g; ext φ x; simp [add_mul, add_smul]
  · intro a f; ext φ x; simp [mul_assoc, smul_smul]
  · intro f φ; funext x
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hc x φ _ (fun v h => by simp [h]) (fun v h => by simp [h])]
    simp [P, MultilinearMap.mkPiAlgebra_apply]
    ring
