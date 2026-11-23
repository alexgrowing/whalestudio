import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolMatchLin

open Classical in

noncomputable def extMul {ι : Type} (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)]
    (S T : Finset ι) (h : S ⊆ T) (z : ∀ v, M v) :
    MultilinearMap ℂ (fun v : S => M v) (PiTensorProduct ℂ fun v : T => M v) where
  toFun x := PiTensorProduct.tprod ℂ (fun v : T => if hv : (v : ι) ∈ S then x ⟨v, hv⟩ else z v)
  map_update_add' x i y y' := by
    have key : ∀ w, (fun v : T => if hv : (v : ι) ∈ S then Function.update x i w ⟨v, hv⟩ else z v) =
        Function.update (fun v : T => if hv : (v : ι) ∈ S then x ⟨v, hv⟩ else z v) ⟨i, h i.2⟩ w := by
      intro w
      funext v
      by_cases hv : (v : ι) ∈ S
      · rw [dif_pos hv]
        by_cases hvi : v = ⟨i, h i.2⟩
        · subst hvi
          simp
        · have hne : (⟨v, hv⟩ : S) ≠ i := fun e => hvi (Subtype.ext (by rw [← e]))
          rw [Function.update_of_ne hne, Function.update_of_ne hvi, dif_pos hv]
      · have hvi : v ≠ ⟨i, h i.2⟩ := fun e => hv (by rw [e]; exact i.2)
        rw [dif_neg hv, Function.update_of_ne hvi, dif_neg hv]
    simp only [key]
    exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
  map_update_smul' x i c y := by
    have key : ∀ w, (fun v : T => if hv : (v : ι) ∈ S then Function.update x i w ⟨v, hv⟩ else z v) =
        Function.update (fun v : T => if hv : (v : ι) ∈ S then x ⟨v, hv⟩ else z v) ⟨i, h i.2⟩ w := by
      intro w
      funext v
      by_cases hv : (v : ι) ∈ S
      · rw [dif_pos hv]
        by_cases hvi : v = ⟨i, h i.2⟩
        · subst hvi
          simp
        · have hne : (⟨v, hv⟩ : S) ≠ i := fun e => hvi (Subtype.ext (by rw [← e]))
          rw [Function.update_of_ne hne, Function.update_of_ne hvi, dif_pos hv]
      · have hvi : v ≠ ⟨i, h i.2⟩ := fun e => hv (by rw [e]; exact i.2)
        rw [dif_neg hv, Function.update_of_ne hvi, dif_neg hv]
    simp only [key]
    exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _

open Classical in
theorem extMul_apply {ι : Type} (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)]
    (S T : Finset ι) (h : S ⊆ T) (z : ∀ v, M v) (x : ∀ v : S, M v) :
    extMul M S T h z x = PiTensorProduct.tprod ℂ (fun v : T => if hv : (v : ι) ∈ S then x ⟨v, hv⟩ else z v) := by
  classical
  rfl

end GlobalTheory.PolMatchLin

namespace GlobalTheory.PolMatchLin

theorem extMul_tprod {ι : Type} (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)]
    (S T : Finset ι) (h : S ⊆ T) (z : ∀ v, M v) (u : ∀ v, M v) (hu : ∀ v ∈ T, v ∉ S → u v = z v) :
    PiTensorProduct.lift (extMul M S T h z) (PiTensorProduct.tprod ℂ fun v : S => u v) =
      PiTensorProduct.tprod ℂ fun v : T => u v := by
  classical
  rw [PiTensorProduct.lift.tprod, extMul_apply]
  congr 1
  funext v
  by_cases hv : (v : ι) ∈ S
  · rw [dif_pos hv]
  · rw [dif_neg hv, hu v v.2 hv]

theorem polMatch_smul_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ Φ Φ' Ψ Ψ' (c : ℂ), PolMatch B G X R Rf Φ Φ' → PolMatch B G X R Rf Ψ Ψ' → PolMatch B G X R Rf (c • Φ + Ψ) (c • Φ' + Ψ') := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ Φ' Ψ Ψ' c h1 h2
  classical
  obtain ⟨T₁, hT₁, m, m', f, φ, f', φ', hf, hf', rfl, rfl, e1⟩ := h1
  obtain ⟨T₂, hT₂, k, k', g, ψ, g', ψ', hg, hg', rfl, rfl, e2⟩ := h2
  set T := T₁ ∪ T₂ with hT
  have h₁ : T₁ ⊆ T := Finset.subset_union_left
  have h₂ : T₂ ⊆ T := Finset.subset_union_right
  set z : ∀ v, Rf.Pi v := fun v => Rf.p v (G.M.vac v) with hz
  have trL : ∀ (S : Finset (Pl F)) (hS : S ⊆ T) {n : ℕ} (h : Fin n → SInf F _) (χ : Fin n → ∀ v : Pl F, (_ → Fv F v) → ℂ),
      (∀ i, ∀ v ∉ S, χ i v = G.M.vac v) →
      LinearMap.lTensor R.Pi (PiTensorProduct.lift (extMul Rf.Pi S T hS z))
          (∑ i, R.p (h i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : S => Rf.p v (χ i v))) =
        ∑ i, R.p (h i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (χ i v)) := by
    intro S hS n h χ hχ
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, extMul_tprod Rf.Pi S T hS z (fun v => Rf.p v (χ i v))]
    intro v _ hv
    rw [hχ i v hv]
  have trR : ∀ (S : Finset (Pl F)) (hS : S ⊆ T), X.T ⊆ S → ∀ {n : ℕ} (h : Fin n → SInf F _)
      (χ : Fin n → ∀ v : Pl F, (_ → Fv F v) → ℂ),
      (∀ i, ∀ v ∉ S, χ i v = G.M'.vac v) →
      LinearMap.lTensor R.Pi (PiTensorProduct.lift (extMul Rf.Pi S T hS z))
          (∑ i, R.p' (h i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : S => Rf.p' v (χ i v))) =
        ∑ i, R.p' (h i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (χ i v)) := by
    intro S hS hXS n h χ hχ
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, extMul_tprod Rf.Pi S T hS z (fun v => Rf.p' v (χ i v))]
    intro v _ hv
    rw [hχ i v hv, hz]
    exact ((hM.fin.sph v fun hvX => hv (hXS hvX)).1).symm
  have k1 := congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.lift (extMul Rf.Pi T₁ T h₁ z))) e1
  rw [trL T₁ h₁ f φ (fun i => (hf i).2.2), trR T₁ h₁ hT₁ f' φ' (fun j => (hf' j).2.2)] at k1
  have k2 := congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.lift (extMul Rf.Pi T₂ T h₂ z))) e2
  rw [trL T₂ h₂ g ψ (fun i => (hg i).2.2), trR T₂ h₂ hT₂ g' ψ' (fun j => (hg' j).2.2)] at k2
  refine ⟨T, hT₁.trans h₁, m + k, m' + k', Fin.append (c • f) g, Fin.append φ ψ, Fin.append (c • f') g',
    Fin.append φ' ψ', ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf i).1, (hf i).2.1, fun v hv => (hf i).2.2 v fun hv' => hv (h₁ hv')⟩
    · simp only [Fin.append_right]
      exact ⟨(hg i).1, (hg i).2.1, fun v hv => (hg i).2.2 v fun hv' => hv (h₂ hv')⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf' i).1, (hf' i).2.1, fun v hv => (hf' i).2.2 v fun hv' => hv (h₁ hv')⟩
    · simp only [Fin.append_right]
      exact ⟨(hg' i).1, (hg' i).2.1, fun v hv => (hg' i).2.2 v fun hv' => hv (h₂ hv')⟩
  · funext x
    simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · funext x
    simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, map_smul, ← TensorProduct.smul_tmul']
    rw [← Finset.smul_sum, ← Finset.smul_sum, k1, k2]

end GlobalTheory.PolMatchLin
