import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Matrix

noncomputable section

namespace GlobalTheory.TauFrame

theorem exists_sub_basis {C : Type} [Field C] {d r : ℕ} (f : Fin d → Fin r → C)
    (hf : Submodule.span C (Set.range f) = ⊤) :
    ∃ κ : Fin r → Fin d, LinearIndependent C (fun k => f (κ k)) := by
  obtain ⟨ι, a, ha, hsp, hli⟩ := exists_linearIndependent' C f
  haveI : Finite ι := Finite.of_injective a ha
  haveI := Fintype.ofFinite ι
  have hb := Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hsp, hf]))
  rw [Module.finrank_fin_fun] at hb
  let e : Fin r ≃ ι := (Fintype.equivFinOfCardEq hb.symm).symm
  exact ⟨a ∘ e, hli.comp e e.injective⟩

section Norm

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_sum_le {n : ℕ} (f : Fin n → C) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ‖f i‖ ≤ c) :
    ‖∑ i, f i‖ ≤ c :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc (fun i _ => h i)

theorem norm_mul_le {a b c : ℕ} (A : Matrix (Fin a) (Fin b) C) (B : Matrix (Fin b) (Fin c) C)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hA : ∀ i j, ‖A i j‖ ≤ x) (hB : ∀ i j, ‖B i j‖ ≤ y) (i j) :
    ‖(A * B) i j‖ ≤ x * y := by
  rw [Matrix.mul_apply]
  refine norm_sum_le _ (mul_nonneg hx hy) fun k => ?_
  rw [norm_mul]
  exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) hx

theorem norm_mulVec_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) C) (v : Fin b → C)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (i) : ‖A.mulVec v i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine norm_sum_le _ zero_le_one fun k => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _ _) (norm_nonneg _) (hv _)

theorem exists_bound_lt {a : ℕ} (A : Matrix (Fin a) (Fin a) C) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ i j, ‖A i j‖ < ρ) : ∃ x, 0 ≤ x ∧ x < ρ ∧ ∀ i j, ‖A i j‖ ≤ x := by
  refine ⟨‖fun p : Fin a × Fin a => A p.1 p.2‖, norm_nonneg _, ?_, fun i j => ?_⟩
  · exact (pi_norm_lt_iff hρ).2 fun p => h _ _
  · exact norm_le_pi_norm (fun p : Fin a × Fin a => A p.1 p.2) (i, j)

end Norm

theorem mem_mul {C : Type} [Field C] (F : Subfield C) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) C)
    (B : Matrix (Fin b) (Fin c) C) (hA : ∀ i j, A i j ∈ F) (hB : ∀ i j, B i j ∈ F) (i j) :
    (A * B) i j ∈ F := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA _ _) (hB _ _)

variable {l : ℕ} [Fact l.Prime]

def subC (F : IntermediateField ℚ_[l] (Om l)) : Subfield (PadicComplex l) :=
  F.toSubfield.map (algebraMap (Om l) (PadicComplex l))

theorem mem_subC {F : IntermediateField ℚ_[l] (Om l)} {y : PadicComplex l} :
    y ∈ subC F ↔ y ∈ inC F := Iff.rfl

theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {σ : GQ l} (hσ : σ ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ subC F) : act σ y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 := ha.1 σ x
  have h2 : σ x = x := hσ ⟨x, hx⟩
  rw [h2] at h1
  exact h1

theorem map_mul' {a b c : ℕ} (f : PadicComplex l ≃+* PadicComplex l)
    (A : Matrix (Fin a) (Fin b) (PadicComplex l)) (B : Matrix (Fin b) (Fin c) (PadicComplex l)) :
    (A * B).map f = A.map f * B.map f := by
  ext i j
  simp [Matrix.mul_apply]

theorem frame_of_idem (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (ha : IsActC act) (K : FinExt l) (m d r : ℕ)
    (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (Dm E : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (hD : IsDec act χ K m M Dm U g)
    (hEM : ∀ σ ∈ Gj K m, E * M σ = M σ * E) (hEσ : ∀ σ ∈ Gj K m, E.map (act σ) = E)
    (hEF : ∀ i j, (Dm⁻¹ * E * Dm) i j ∈ subC (Ks K m))
    (R : Matrix (Fin r) (Fin d) (PadicComplex l)) (S : Matrix (Fin d) (Fin r) (PadicComplex l))
    (hR : ∀ i j, R i j ∈ subC (Ks K m) ∧ ‖R i j‖ ≤ 1)
    (hS : ∀ i j, S i j ∈ subC (Ks K m) ∧ ‖S i j‖ ≤ 1)
    (hRS : R * S = 1) (hRe : R * (Dm⁻¹ * E * Dm) = R) (heSR : (Dm⁻¹ * E * Dm) * S * R = Dm⁻¹ * E * Dm)
    (e : Fin d → Fin d → PadicComplex l) (u : Fin d → ℤ) (hli : LinearIndependent (PadicComplex l) e)
    (hfix : ∀ σ ∈ Gj K m, ∀ k, twAct act χ (u k) M σ (e k) = e k) (J : Set ℤ)
    (hJ : ∀ k, E.mulVec (e k) ≠ 0 → u k ∈ J) :
    Frame χ K m (fun σ => R * U σ * S) g ∧ HTBasis act χ (Gj K m) (fun σ => R * U σ * S) J ∧
    (∀ σ ∈ Gj K m, (R * Dm⁻¹) * M σ = (R * U σ * S) * (R * Dm⁻¹).map (act σ)) ∧
    ball l r ⊆ (R * Dm⁻¹).mulVec '' ball l d ∧
    (∀ x ∈ ball l d, (l : PadicComplex l) • (R * Dm⁻¹).mulVec x ∈ ball l r) ∧
    ∃ Q : Matrix (Fin d) (Fin r) (PadicComplex l), Q * (R * Dm⁻¹) = E := by
  obtain ⟨hdet, hDi, hDl, ⟨hgen, hcont, hint, hmul, hH, hg⟩, hrel⟩ := hD
  set e' := Dm⁻¹ * E * Dm with he'
  have h1 : Dm * Dm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : Dm⁻¹ * Dm = 1 := Matrix.nonsing_inv_mul _ hdet
  have hDe : Dm * e' = E * Dm := by
    rw [he', ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hfixm : ∀ σ ∈ Gj K m, ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) (PadicComplex l)),
      (∀ i j, X i j ∈ subC (Ks K m)) → X.map (act σ) = X := by
    intro σ hσ a b X hX
    ext i j
    exact act_fix ha hσ (hX i j)
  have hcomm : ∀ σ ∈ Gj K m, e' * U σ = U σ * e' := by
    intro σ hσ
    have : Dm * (e' * U σ) = Dm * (U σ * e') := by
      rw [← Matrix.mul_assoc, hDe, Matrix.mul_assoc, hrel σ hσ, ← Matrix.mul_assoc, hEM σ hσ,
        Matrix.mul_assoc, ← Matrix.mul_assoc Dm, hrel σ hσ, Matrix.mul_assoc]
      congr 1
      conv_lhs => rw [← hEσ σ hσ]
      conv_rhs => rw [← hfixm σ hσ e' hEF]
      rw [← map_mul', ← map_mul', hDe]
    have h3 := congrArg (fun X => Dm⁻¹ * X) this
    simpa only [← Matrix.mul_assoc, h2, Matrix.one_mul] using h3
  have hkey : ∀ σ ∈ Gj K m, R * U σ * S * R = R * U σ := by
    intro σ hσ
    have h3 : R * U σ = R * U σ * e' := by
      rw [Matrix.mul_assoc, ← hcomm σ hσ, ← Matrix.mul_assoc, hRe]
    calc R * U σ * S * R = R * U σ * (e' * S * R) := by
          conv_lhs => rw [h3]
          simp only [Matrix.mul_assoc]
      _ = R * U σ := by rw [heSR, ← h3]
  have heq : ∀ σ ∈ Gj K m, (R * Dm⁻¹) * M σ = (R * U σ * S) * (R * Dm⁻¹).map (act σ) := by
    intro σ hσ
    have h3 : Dm.map (act σ) * Dm⁻¹.map (act σ) = 1 := by
      rw [← map_mul', h1]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have h4 : Dm⁻¹ * M σ = U σ * Dm⁻¹.map (act σ) := by
      calc Dm⁻¹ * M σ = Dm⁻¹ * (M σ * Dm.map (act σ)) * Dm⁻¹.map (act σ) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, h3, Matrix.mul_one]
        _ = _ := by rw [← hrel σ hσ, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [map_mul', hfixm σ hσ R (fun i j => (hR i j).1), ← Matrix.mul_assoc, hkey σ hσ,
      Matrix.mul_assoc, h4, Matrix.mul_assoc]
  have hsec : R * Dm⁻¹ * (Dm * S) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Dm⁻¹, h2, Matrix.one_mul, hRS]
  refine ⟨⟨hgen, ?_, ?_, ?_, ?_, ?_⟩, ?_, heq, ?_, ?_, ?_⟩
  · intro a b
    simp only [Matrix.mul_apply]
    refine continuousOn_finset_sum _ fun k _ => ContinuousOn.mul ?_ continuousOn_const
    exact continuousOn_finset_sum _ fun j _ => ContinuousOn.mul continuousOn_const (hcont _ _)
  · intro σ hσ a b
    refine ⟨mem_subC.1 (mem_mul _ _ _ (mem_mul _ _ _ (fun i j => (hR i j).1)
      (fun i j => mem_subC.2 (hint σ hσ i j).1)) (fun i j => (hS i j).1) a b), ?_⟩
    have := norm_mul_le (R * U σ) S (mul_nonneg zero_le_one zero_le_one) zero_le_one
      (norm_mul_le R (U σ) zero_le_one zero_le_one (fun i j => (hR i j).2)
        (fun i j => (hint σ hσ i j).2)) (fun i j => (hS i j).2) a b
    simpa using this
  · intro σ hσ τ hτ
    simp only
    rw [hmul σ hσ τ hτ, ← Matrix.mul_assoc (R * U σ * S), ← Matrix.mul_assoc (R * U σ * S),
      hkey σ hσ]
    simp only [Matrix.mul_assoc]
  · intro σ hσ
    simp only
    rw [hH σ hσ, Matrix.mul_one, hRS]
  · intro a b
    have hrho : 0 < rho1 l :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
    obtain ⟨x, hx0, hx, hxb⟩ := exists_bound_lt (U g - 1) hrho hg
    have h3 : R * U g * S - 1 = R * (U g - 1) * S := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRS]
    simp only
    rw [h3]
    have := norm_mul_le (R * (U g - 1)) S (mul_nonneg zero_le_one hx0) zero_le_one
      (norm_mul_le R (U g - 1) zero_le_one hx0 (fun i j => (hR i j).2) hxb)
      (fun i j => (hS i j).2) a b
    exact lt_of_le_of_lt (by simpa using this) hx
  · set Pm := R * Dm⁻¹ with hPm
    have hsp : Submodule.span (PadicComplex l) (Set.range fun k => Pm.mulVec (e k)) = ⊤ := by
      have h3 : Submodule.span (PadicComplex l) (Set.range e) = ⊤ :=
        hli.span_eq_top_of_card_eq_finrank' (by simp)
      have h4 : (Set.range fun k => Pm.mulVec (e k)) = Pm.mulVecLin '' Set.range e := by
        rw [← Set.range_comp]; rfl
      rw [h4, ← Submodule.map_span, h3, Submodule.map_top, LinearMap.range_eq_top]
      intro y
      refine ⟨(Dm * S).mulVec y, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hsec, Matrix.one_mulVec]
    obtain ⟨κ, hκ⟩ := exists_sub_basis _ hsp
    refine ⟨fun k => Pm.mulVec (e (κ k)), fun k => u (κ k), hκ, fun k => hJ _ fun h0 => ?_, ?_⟩
    · apply hκ.ne_zero k
      have h3 : Pm * E = Pm := by
        calc Pm * E = R * e' * Dm⁻¹ := by
              rw [hPm, he']; simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
          _ = Pm := by rw [hRe]
      show Pm.mulVec (e (κ k)) = 0
      rw [← h3, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    · intro σ hσ k
      have h3 := hfix σ hσ (κ k)
      unfold twAct at h3 ⊢
      have hmap : (fun a => act σ (Pm.mulVec (e (κ k)) a)) =
          (Pm.map (act σ)).mulVec (fun a => act σ (e (κ k) a)) := by
        funext a
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      simp only
      rw [hmap, Matrix.mulVec_mulVec, ← heq σ hσ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, h3]
  · intro y hy
    refine ⟨Dm.mulVec (S.mulVec y), norm_mulVec_le _ _ hDi
      (norm_mulVec_le _ _ (fun i j => (hS i j).2) hy), ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hsec, Matrix.one_mulVec]
  · intro x hx
    have h3 : (l : PadicComplex l) • (R * Dm⁻¹).mulVec x =
        R.mulVec (((l : PadicComplex l) • Dm⁻¹).mulVec x) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    rw [h3]
    exact norm_mulVec_le _ _ (fun i j => (hR i j).2) (norm_mulVec_le _ _ (fun i j => hDl i j) hx)
  · refine ⟨Dm * e' * S, ?_⟩
    calc Dm * e' * S * (R * Dm⁻¹) = Dm * (e' * S * R) * Dm⁻¹ := by simp only [Matrix.mul_assoc]
      _ = E := by rw [heSR, hDe, Matrix.mul_assoc, h1, Matrix.mul_one]

end GlobalTheory.TauFrame
