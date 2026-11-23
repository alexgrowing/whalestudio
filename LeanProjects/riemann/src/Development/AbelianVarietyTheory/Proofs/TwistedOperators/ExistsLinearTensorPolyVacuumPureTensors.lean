import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweGlobal.TensorMap

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem finite_nonint {κ : Type} [Finite κ] (x : κ → AF F) :
    {w : Pl F | ¬ ∀ i, evFin F w (x i) ∈ w.adicCompletionIntegers F}.Finite := by
  have h : ∀ i, {w : Pl F | evFin F w (x i) ∉ w.adicCompletionIntegers F}.Finite := fun i =>
    Filter.eventually_cofinite.1 (x i).2.2
  refine (Set.finite_iUnion h).subset ?_
  intro w hw
  push_neg at hw
  obtain ⟨i, hi⟩ := hw
  exact Set.mem_iUnion.2 ⟨i, hi⟩

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

open Classical in

def vacOff (M : Model σ Y W) (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) : ℂ :=
  ∏ᶠ w, if w ∈ T then (1 : ℂ) else M.vac w fun i => evFin F w (x i)

def prodT (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) :
    MultilinearMap ℂ (fun v : T => ↥(SB (Fin n × Fin d → Fv F v.1))) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap fun v =>
    (LinearMap.proj (fun i => evFin F v.1 (x i)) : ((Fin n × Fin d → Fv F v.1) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (SB _).subtype

theorem prodT_apply (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    prodT T x φ = ∏ v : T, (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) fun i => evFin F v.1 (x i) := by
  simp [prodT]

def multi (M : Model σ Y W) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d)) :
    MultilinearMap ℂ (fun v : T => ↥(SB (Fin n × Fin d → Fv F v.1))) ((Fin n × Fin d → AF F) → ℂ) :=
  MultilinearMap.pi fun x => (f (fun i => evI F (x i)) * vacOff M T x) • prodT T x

theorem multi_apply (M : Model σ Y W) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (x : Fin n × Fin d → AF F) :
    multi M T f φ x = f (fun i => evI F (x i)) * vacOff M T x * prodT T x φ := by
  simp [multi]

def multiL (M : Model σ Y W) (T : Finset (Pl F)) :
    SInf F (Fin n × Fin d) →ₗ[ℂ]
      MultilinearMap ℂ (fun v : T => ↥(SB (Fin n × Fin d → Fv F v.1))) ((Fin n × Fin d → AF F) → ℂ) where
  toFun := multi M T
  map_add' f g := by
    ext φ x
    simp only [multi_apply, MultilinearMap.add_apply, Pi.add_apply, SchwartzMap.add_apply]
    ring
  map_smul' c f := by
    ext φ x
    simp only [multi_apply, MultilinearMap.smul_apply, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

open Classical in

theorem finprod_split (M : Model σ Y W)
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (T : Finset (Pl F)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
    (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) (h2 : ∀ v ∉ T, φ' v = M.vac v) (x : Fin n × Fin d → AF F) :
    ∏ᶠ w, φ' w (fun i => evFin F w (x i)) = vacOff M T x * prodT T x φ := by
  set ρ : Pl F → ℂ := fun w => if w ∈ T then (1 : ℂ) else M.vac w fun i => evFin F w (x i) with hρdef
  set θ : Pl F → ℂ := fun w => if w ∈ T then φ' w (fun i => evFin F w (x i)) else 1 with hθdef
  have e : (fun w => φ' w (fun i => evFin F w (x i))) = fun w => θ w * ρ w := by
    funext w
    by_cases hw : w ∈ T
    · simp [θ, ρ, hw]
    · simp [θ, ρ, hw, h2 w hw]
  have hρ : (Function.mulSupport ρ).Finite := by
    refine ((Filter.eventually_cofinite.1 hstd).union (finite_nonint x)).subset ?_
    intro w hw
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hw
    by_cases hwT : w ∈ T
    · simp [ρ, hwT]
    · simp only [ρ, hwT, if_false, hc.1]
      exact Set.indicator_of_mem (s := {x : Fin n × Fin d → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F}) hc.2 1
  have hθ : Function.mulSupport θ ⊆ (T : Set (Pl F)) := by
    intro w hw
    by_contra hc
    exact hw (by simp [θ, show w ∉ T from hc])
  rw [e, finprod_mul_distrib (T.finite_toSet.subset hθ) hρ, mul_comm]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset θ hθ, prodT_apply, ← Finset.prod_coe_sort T]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp [θ, v.2, h1 v.1 v.2]

def tensL (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) :
    ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₗ[ℂ]
      ((Fin n × Fin d → AF F) → ℂ) :=
  TensorProduct.lift ((PiTensorProduct.lift.toLinearMap ∘ₗ multiL M T) ∘ₗ (M.Pol ψ emb).subtype)

theorem tensL_tmul (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (T : Finset (Pl F)) (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    tensL M ψ emb T (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = multi M T (f : SInf F (Fin n × Fin d)) φ := by
  simp [tensL, multiL]

theorem exists_tensL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w),
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    ∃ L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ]
        ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') ∧
      GlobalTheory.HoweGlobal.algAt M ψ emb T ≤ LinearMap.range L := by
  intro F E _ _ _ _ _ σ n d Y W M ψ emb hstd T
  have hchar : ∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
      (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
      tensL M ψ emb T (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : SInf F (Fin n × Fin d)) φ' := by
    intro f φ φ' h1 h2
    funext x
    rw [tensL_tmul, multi_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, finprod_split M hstd T φ φ' h1 h2 x, mul_assoc]
  refine ⟨tensL M ψ emb T, hchar, Submodule.span_le.2 ?_⟩
  rintro Φ ⟨f, φ, hf, hφ, hv, rfl⟩
  exact ⟨⟨f, hf⟩ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun v : T => ⟨φ v.1, hφ v.1⟩),
    hchar ⟨f, hf⟩ _ φ (fun _ _ => rfl) hv⟩

end GlobalTheory.HoweGlobal.TensorMap
