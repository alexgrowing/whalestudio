import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyExistsMulIsLowerTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalTotalDegreeLe

noncomputable section

open MvPolynomial GlobalTheory.MvPoly GlobalTheory.Harm Matrix

namespace GlobalTheory.DefLift

namespace Compl

theorem exists_sub_perp {E : Type*} [AddCommGroup E] [Module ℂ E] (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x, B x x = 0 → x = 0) (W : Submodule ℂ E) [FiniteDimensional ℂ W] (P : E) :
    ∃ Q ∈ W, ∀ w ∈ W, B (P - Q) w = 0 := by
  let b := Module.finBasis ℂ W
  let L : E →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearMap.pi fun i => B.flip (b i)
  have hL (P) (h : L P = 0) (w) (hw : w ∈ W) : B P w = 0 := by
    have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
    rw [map_sum, Submodule.subtype_apply] at this
    change _ = w at this
    rw [← this, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, map_smulₛₗ]
    exact smul_eq_zero_of_right _ (congrFun h i)
  have hinj : Function.Injective (L ∘ₗ W.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hB _ (hL x hx x x.2))
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
    (L P)
  exact ⟨x, x.2, hL _ (by rw [map_sub, ← hx]; simp)⟩

theorem totalDegree_aeval_le {σ : Type*} (f : σ → MvPolynomial σ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.AevalTotalDegreeBound.main
  | exact _root_.GlobalTheory.AevalTotalDegreeBound.main
  | (apply _root_.GlobalTheory.AevalTotalDegreeBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalTotalDegreeBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalTotalDegreeBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalTotalDegreeBound.main ..)

variable {ι : Type} {m n : ℕ}

theorem totalDegree_subst_le (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ) (P : Pol ι m n) :
    (subst a b P).totalDegree ≤ P.totalDegree := by
  refine totalDegree_aeval_le _ (fun v => ?_) P
  refine totalDegree_finsetSum_le fun i _ => totalDegree_finsetSum_le fun c _ => ?_
  exact (totalDegree_smul_le _ _).trans (totalDegree_X _).le

theorem totalDegree_colSub_le (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (P : Pol ι m n) :
    (colSub m τ g P).totalDegree ≤ P.totalDegree := by
  unfold colSub
  rw [AlgHom.toLinearMap_apply]
  exact totalDegree_subst_le _ _ _

theorem fockInner_subst [Fintype ι] (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ)
    (P Q : Pol ι m n) :
    fockInner (subst a b P) Q = fockInner P (subst (fun τ => star (a τ)) (fun τ => star (b τ)) Q) := by
  classical
  refine fockInner_algHom_of_linear _ _
    (fun v w => if v.1 = w.1 then b v.1 w.2.1 v.2.1 * a v.1 v.2.2 w.2.2 else 0) ?_ ?_ P Q
  · rintro ⟨t, i, k⟩
    simp [subst, Fintype.sum_prod_type]
  · rintro ⟨t, i, k⟩
    simp [subst, Fintype.sum_prod_type, apply_ite star, mul_comm]

theorem fockInner_colSub [Fintype ι] (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (P Q : Pol ι m n) :
    fockInner (colSub m τ g P) Q = fockInner P (colSub m τ g⁻¹ Q) := by
  unfold colSub
  simp only [AlgHom.toLinearMap_apply]
  rw [fockInner_subst]
  congr 3
  · funext ρ
    split_ifs
    · rfl
    · simp
  · funext ρ
    simp

end Compl

open Compl in

theorem exists_colStable_disjoint (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (U W : Submodule ℂ (X →ₗ[ℂ] Pol ι m n))
    (hU : ∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) (hW : ∀ Φ ∈ W, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ W) (hlt : U < W) :
    ∃ U' : Submodule ℂ (X →ₗ[ℂ] Pol ι m n), U' ≠ ⊥ ∧ U' ≤ W ∧ U ⊓ U' = ⊥ ∧
      ∀ Φ ∈ U', ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U' := by
  classical
  let b := Module.finBasis ℂ X
  let B : (X →ₗ[ℂ] Pol ι m n) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun Φ Ψ => ∑ i, fockInner (Φ (b i)) (Ψ (b i)))
      (fun _ _ _ => by simp [fockInner_add_left, Finset.sum_add_distrib])
      (fun _ _ _ => by simp [fockInner_smul_left, Finset.mul_sum])
      (fun _ _ _ => by simp [fockInner_add_right, Finset.sum_add_distrib])
      (fun _ _ _ => by simp [fockInner_smul_right, Finset.mul_sum])
  have hBa (Φ Ψ) : B Φ Ψ = ∑ i, fockInner (Φ (b i)) (Ψ (b i)) := rfl
  have hB (Φ) (h : B Φ Φ = 0) : Φ = 0 := by
    rw [hBa] at h
    simp only [fockInner_self] at h
    have h' : ∑ i, fockNormSq (Φ (b i)) = 0 := by
      rw [← RCLike.ofReal_sum] at h
      exact RCLike.ofReal_eq_zero.mp h
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => fockNormSq_nonneg _] at h'
    exact b.ext fun i => fockNormSq_eq_zero.mp (h' i (Finset.mem_univ i))
  have hadj (Φ Ψ τ g) : B (colSub m τ g ∘ₗ Φ) Ψ = B Φ (colSub m τ g⁻¹ ∘ₗ Ψ) := by
    simp only [hBa, LinearMap.comp_apply, fockInner_colSub]
  clear hBa
  clear_value B
  obtain ⟨β, hβW, hβU⟩ := SetLike.exists_of_lt hlt
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ∀ i, (β (b i)).totalDegree ≤ d :=
    ⟨_, fun i => Finset.le_sup (f := fun i => (β (b i)).totalDegree) (Finset.mem_univ i)⟩
  obtain ⟨R, hRf, hR⟩ : ∃ R : Submodule ℂ (Pol ι m n), FiniteDimensional ℂ R ∧ ∀ P, P ∈ R ↔ P.totalDegree ≤ d :=
    ⟨restrictTotalDegree (ι × Fin m × Fin n) ℂ d, inferInstance, fun P => mem_restrictTotalDegree _ _ _⟩
  let ψ : (X →ₗ[ℂ] R) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n) :=
    { toFun := fun Ψ => R.subtype ∘ₗ Ψ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let D : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := LinearMap.range ψ
  have hD (Φ) : Φ ∈ D ↔ ∀ x, Φ x ∈ R := by
    constructor
    · rintro ⟨Ψ, rfl⟩ x
      exact (Ψ x).2
    · intro h
      exact ⟨Φ.codRestrict R h, rfl⟩
  haveI : FiniteDimensional ℂ D := inferInstance
  clear_value D
  have hDs (Φ) (h : Φ ∈ D) (τ g) : colSub m τ g ∘ₗ Φ ∈ D := by
    rw [hD] at h ⊢
    intro x
    have := h x
    rw [hR] at this ⊢
    rw [LinearMap.comp_apply]
    exact (totalDegree_colSub_le τ g _).trans this
  have hβD : β ∈ D := by
    rw [hD]
    intro x
    rw [← b.sum_repr x, map_sum]
    refine R.sum_mem fun i _ => ?_
    rw [map_smul]
    exact R.smul_mem _ ((hR _).2 (hd i))
  haveI : FiniteDimensional ℂ (U ⊓ D : Submodule ℂ _) := Submodule.finiteDimensional_inf_right _ _
  let T : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := ⨅ w ∈ U ⊓ D, LinearMap.ker (B.flip w)
  have hT (Φ) : Φ ∈ T ↔ ∀ w ∈ U ⊓ D, B Φ w = 0 := by simp [T, Submodule.mem_iInf]
  obtain ⟨Q, hQ, hperp⟩ := exists_sub_perp B hB (U ⊓ D) β
  refine ⟨W ⊓ D ⊓ T, ?_, inf_le_left.trans inf_le_left, ?_, ?_⟩
  · intro h
    have hm : β - Q ∈ W ⊓ D ⊓ T :=
      ⟨⟨W.sub_mem hβW (hlt.le hQ.1), D.sub_mem hβD hQ.2⟩, (hT _).2 hperp⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at hm
    exact hβU (hm ▸ hQ.1)
  · rw [Submodule.eq_bot_iff]
    rintro Φ ⟨h1, ⟨-, h2⟩, h3⟩
    exact hB Φ ((hT Φ).1 h3 Φ ⟨h1, h2⟩)
  · rintro Φ ⟨⟨h1, h2⟩, h3⟩ τ g
    refine ⟨⟨hW Φ h1 τ g, hDs Φ h2 τ g⟩, (hT _).2 fun w hw => ?_⟩
    rw [hadj]
    exact (hT Φ).1 h3 _ ⟨hU w hw.1 τ _, hDs w hw.2 τ _⟩

end GlobalTheory.DefLift

end
