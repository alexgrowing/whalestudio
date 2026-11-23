import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.TorusSupportAvg

section Generic

variable {K V Ω : Type} [AddCommGroup K] [AddCommGroup V]

def IsCharAvg (ψ : AddChar K ℂ) (G : V →+ (Ω → K)) (h : Ω → ℂ) : Prop :=
  ∃ (N : ℕ) (a : Fin N → ℂ) (w : Fin N → V), ∑ m, a m = 1 ∧ ∀ Y, ∑ m, a m * ψ (G (w m) Y) = h Y

theorem isCharAvg_one (ψ : AddChar K ℂ) (G : V →+ (Ω → K)) : IsCharAvg ψ G 1 :=
  ⟨1, fun _ => 1, fun _ => 0, by simp, fun Y => by simp⟩

theorem isCharAvg_mul {ψ : AddChar K ℂ} {G : V →+ (Ω → K)} {h₁ h₂ : Ω → ℂ}
    (h1 : IsCharAvg ψ G h₁) (h2 : IsCharAvg ψ G h₂) : IsCharAvg ψ G (h₁ * h₂) := by
  obtain ⟨N₁, a₁, w₁, hs₁, hv₁⟩ := h1
  obtain ⟨N₂, a₂, w₂, hs₂, hv₂⟩ := h2
  refine ⟨N₁ * N₂, fun m => a₁ (finProdFinEquiv.symm m).1 * a₂ (finProdFinEquiv.symm m).2,
    fun m => w₁ (finProdFinEquiv.symm m).1 + w₂ (finProdFinEquiv.symm m).2, ?_, ?_⟩
  · rw [finProdFinEquiv.symm.sum_comp (fun p => a₁ p.1 * a₂ p.2), Fintype.sum_prod_type,
      ← Finset.sum_mul_sum, hs₁, hs₂, one_mul]
  · intro Y
    rw [finProdFinEquiv.symm.sum_comp (fun p => a₁ p.1 * a₂ p.2 * ψ (G (w₁ p.1 + w₂ p.2) Y)),
      Fintype.sum_prod_type, Pi.mul_apply, ← hv₁, ← hv₂, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, Pi.add_apply, AddChar.map_add_eq_mul]
    ring

theorem isCharAvg_prod {ψ : AddChar K ℂ} {G : V →+ (Ω → K)} {ι : Type} (s : Finset ι) (h : ι → Ω → ℂ)
    (hs : ∀ j ∈ s, IsCharAvg ψ G (h j)) : IsCharAvg ψ G (∏ j ∈ s, h j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCharAvg_one ψ G
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact isCharAvg_mul (hs j (Finset.mem_insert_self j s))
      (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))

theorem isCharAvg_poly (ψ : AddChar K ℂ) (G : V →+ (Ω → K)) (P : Polynomial ℂ) (hP : P.eval 1 = 1) (w₀ : V) :
    IsCharAvg ψ G (fun Y => P.eval (ψ (G w₀ Y))) := by
  refine ⟨P.natDegree + 1, fun m => P.coeff m, fun m => (m : ℕ) • w₀, ?_, ?_⟩
  · rw [Fin.sum_univ_eq_sum_range (fun i => P.coeff i), ← hP, Polynomial.eval_eq_sum_range]
    simp
  · intro Y
    dsimp only
    rw [Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun i => P.coeff i * ψ (G w₀ Y) ^ i)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_nsmul, Pi.smul_apply, AddChar.map_nsmul_eq_pow]

end Generic

def killPoly (Z : Finset ℂ) : Polynomial ℂ :=
  ∏ ζ ∈ Z.filter (· ≠ 1), (Polynomial.C (1 - ζ)⁻¹ * (Polynomial.X - Polynomial.C ζ))

theorem killPoly_eval_one (Z : Finset ℂ) : (killPoly Z).eval 1 = 1 := by
  unfold killPoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_one fun ζ hζ => ?_
  have : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm (Finset.mem_filter.1 hζ).2)
  simp [this]

theorem killPoly_eval_eq_zero {Z : Finset ℂ} {z : ℂ} (hz : z ∈ Z) (h1 : z ≠ 1) : (killPoly Z).eval z = 0 := by
  unfold killPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_filter.2 ⟨hz, h1⟩) (by simp)

theorem finite_image_of_isLocallyConstant {Ω : Type} [TopologicalSpace Ω] {g : Ω → ℂ} (hg : IsLocallyConstant g)
    {S : Set Ω} (hS : IsCompact S) : (g '' S).Finite := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  rw [Set.image_eq_range]
  exact (hg.comp_continuous continuous_subtype_val).range_finite

theorem rank_ne_of_vecMul_eq_zero {K : Type} [Field K] {n d : ℕ} {c : Fin n → K} (hc : c ≠ 0)
    {Y : Matrix (Fin n) (Fin d) K} (h : Matrix.vecMul c Y = 0) : Y.rank ≠ n := by
  rw [← Matrix.rank_transpose, Matrix.rank]
  have hker : c ∈ LinearMap.ker Yᵀ.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, h]
  have hne : LinearMap.ker Yᵀ.mulVecLin ≠ ⊥ := by
    intro hb; rw [hb, Submodule.mem_bot] at hker; exact hc hker
  have hpos : 0 < Module.finrank K (LinearMap.ker Yᵀ.mulVecLin) := by
    rw [Nat.pos_iff_ne_zero]; exact fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
  have hrn := LinearMap.finrank_range_add_finrank_ker Yᵀ.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  omega

end GlobalTheory.TorusSupportAvg

namespace GlobalTheory.TorusSupportAvg

theorem exists_charAvg_mul_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ (n d : ℕ) (c : Fin n → Fv F v), c ≠ 0 → ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
    (∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → f Y = 0) →
    ∃ (N : ℕ) (a : Fin N → ℂ) (w : Fin N → Fin d → Fv F v), ∑ m, a m = 1 ∧
      ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (∑ m, a m * ψ₀ (∑ k, ∑ l, Y k l * c k * w m l)) * f Y = 0 := by
  intro F _ _ v ψ₀ hψ hne n d c hc f hf hrank
  classical
  have hlc : IsLocallyConstant ψ₀ :=
    @SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.isLocallyConstant_addChar _ _ (GlobalTheory.LocalData.complRel v) _ (GlobalTheory.LocalData.isLocalField v) ψ₀ hψ
  obtain ⟨hloc, hcs⟩ : IsLocallyConstant f ∧ HasCompactSupport f := hf
  let G : (Fin d → Fv F v) →+ (Matrix (Fin n) (Fin d) (Fv F v) → Fv F v) :=
    AddMonoidHom.mk' (fun w Y => ∑ k, ∑ l, Y k l * c k * w l) (by
      intro w₁ w₂; funext Y; simp [mul_add, Finset.sum_add_distrib])
  have hG : ∀ w Y, G w Y = ∑ k, ∑ l, Y k l * c k * w l := fun _ _ => rfl
  have hGc : ∀ w, Continuous (G w) := by
    intro w
    show Continuous fun Y : Matrix (Fin n) (Fin d) (Fv F v) => ∑ k, ∑ l, Y k l * c k * w l
    exact continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ =>
      ((continuous_id.matrix_elem k l).mul continuous_const).mul continuous_const

  set S := Function.support f with hSdef
  have hSc : IsCompact S := by
    have hcl : IsClosed S := by
      have := (hloc.isClopen_fiber 0).isOpen.isClosed_compl
      convert this using 1
      ext x; simp [S, Function.mem_support]
    exact hcs.of_isClosed_subset hcl (subset_tsupport f)

  obtain ⟨t₀, ht₀⟩ : ∃ t, ψ₀ t ≠ 1 := by
    by_contra h; push_neg at h; exact hne (by ext x; simp [h x])
  have hex : ∀ Y ∈ S, ∃ w, ψ₀ (G w Y) ≠ 1 := by
    intro Y hY
    have hr : Y.rank = n := by by_contra h; exact hY (hrank Y h)
    have hv : Matrix.vecMul c Y ≠ 0 := fun h => rank_ne_of_vecMul_eq_zero hc h hr
    obtain ⟨l, hl⟩ : ∃ l, Matrix.vecMul c Y l ≠ 0 := by
      by_contra h; push_neg at h; exact hv (funext h)
    refine ⟨Pi.single l (t₀ / Matrix.vecMul c Y l), ?_⟩
    have : G (Pi.single l (t₀ / Matrix.vecMul c Y l)) Y = t₀ := by
      rw [hG]
      simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← Finset.sum_mul]
      have e : ∑ k, Y k l * c k = Matrix.vecMul c Y l := by
        simp only [Matrix.vecMul, dotProduct]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [e]; field_simp
    rw [this]; exact ht₀
  choose! wch hwch using hex
  have hopen : ∀ Y, IsOpen {Y' | ψ₀ (G (wch Y) Y') ≠ 1} := fun Y =>
    isOpen_compl_singleton.preimage (hψ.comp (hGc _))
  obtain ⟨t, htS, hcov⟩ := hSc.elim_nhds_subcover (fun Y => {Y' | ψ₀ (G (wch Y) Y') ≠ 1})
    (fun Y hY => (hopen Y).mem_nhds (hwch Y hY))
  have hfin : ∀ j, ((fun Y => ψ₀ (G (wch j) Y)) '' S).Finite := fun j =>
    finite_image_of_isLocallyConstant (hlc.comp_continuous (hGc _)) hSc
  have hrep := isCharAvg_prod (ψ := ψ₀) (G := G) t
    (fun j Y => (killPoly (hfin j).toFinset).eval (ψ₀ (G (wch j) Y)))
    (fun j _ => isCharAvg_poly ψ₀ G _ (killPoly_eval_one _) (wch j))
  obtain ⟨N, a, w, hs, hval⟩ := hrep
  refine ⟨N, a, w, hs, fun Y => ?_⟩
  have hv := hval Y
  simp only [hG] at hv
  rw [hv]
  by_cases hY : f Y = 0
  · rw [hY, mul_zero]
  · have hYS : Y ∈ S := hY
    obtain ⟨j, hj, hjY⟩ : ∃ j ∈ t, ψ₀ (G (wch j) Y) ≠ 1 := by
      have := hcov hYS
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
      obtain ⟨j, hj, h⟩ := this
      exact ⟨j, hj, h⟩
    rw [Finset.prod_apply, Finset.prod_eq_zero hj, zero_mul]
    exact killPoly_eval_eq_zero ((hfin j).mem_toFinset.2 ⟨Y, hYS, rfl⟩) hjY

end GlobalTheory.TorusSupportAvg
