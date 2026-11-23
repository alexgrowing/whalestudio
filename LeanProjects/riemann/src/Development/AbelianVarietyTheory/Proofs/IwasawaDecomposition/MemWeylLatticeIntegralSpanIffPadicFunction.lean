import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.GlobalTheory.GL4.PZBasis
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.IntSpanDelW

open Formalism.L2.GlobalTheoryTheory.TraceIntegrality

variable {ι : Type} [Fintype ι] {n : ℕ}

def evM {p : ℕ} [Fact p.Prime] (P : MvPolynomial (ι × Fin n × Fin n) ℂ_[p]) :
    (ι → Matrix (Fin n) (Fin n) ℂ_[p]) → ℂ_[p] :=
  fun y => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P

theorem ten_int_map (R : Type) [CommRing R] (f : ι → MvPolynomial (Fin n × Fin n) ℤ) :
    Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom R) (f τ)) =
      MvPolynomial.map (Int.castRingHom R) (Formalism.MainNotions.flipTwoThree.ten f) := by
  unfold Formalism.L2.Forms.ten Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => (MvPolynomial.map_rename _ _ _).symm

theorem prod_eval_eq_evM {p : ℕ} [Fact p.Prime] (f : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (y : ι → Matrix (Fin n) (Fin n) ℂ_[p]) :
    ∏ τ, MvPolynomial.eval (fun k : Fin n × Fin n => y τ k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ)) =
      evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Formalism.MainNotions.flipTwoThree.ten f)) y := by
  unfold evM Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.map_rename, MvPolynomial.eval_rename]
  rfl

theorem mem_vlIntSpan_iff {K : Type} [Field K] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl)
    (lam : ι → DomWeight n) (Z : ZBasis lam) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    P ∈ vlIntSpan σ Pl w lam ↔ ∃ c : Z.J0 → K, (∀ i, c i ∈ intW Pl w) ∧
      P = ∑ i, σ (c i) • MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ i) := by
  constructor
  · intro hP
    induction hP using AddSubgroup.closure_induction with
    | mem P hP =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hP
      have hx : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]
        exact Submodule.subset_span ⟨f, hf, rfl⟩
      obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
      refine ⟨fun i => r * (z i : K), fun i => mul_mem hr (intCast_mem _ _), ?_⟩
      rw [ten_int_map, ← hz, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
    | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      refine ⟨c + c', fun i => add_mem (hc i) (hc' i), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨-c, fun i => neg_mem (hc i), ?_⟩
      simp [neg_smul, Finset.sum_neg_distrib]
  · rintro ⟨c, hc, rfl⟩
    have key : ∀ x ∈ Submodule.span ℤ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ,
        (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}, ∀ r ∈ intW Pl w,
        σ r • MvPolynomial.map (Int.castRingHom ℂ) x ∈ vlIntSpan σ Pl w lam := by
      intro x hx r hr
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        refine AddSubgroup.subset_closure ⟨r, f, hr, hf, ?_⟩
        rw [ten_int_map]
      | zero =>
        rw [map_zero, smul_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [map_add, smul_add]
        exact add_mem hx hy
      | smul a x _ hx =>
        rw [map_zsmul, smul_comm]
        exact zsmul_mem hx a
    refine sum_mem fun i _ => key _ ?_ _ (hc i)
    rw [← Z.span_eq]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem mem_delW_iff {p : ℕ} [Fact p.Prime] (lam : ι → DomWeight n) (Z : ZBasis lam)
    (F : (ι → Matrix (Fin n) (Fin n) ℂ_[p]) → ℂ_[p]) :
    F ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW) ↔ ∃ d : Z.J0 → ℂ_[p], (∀ i, ‖d i‖ ≤ 1) ∧
      F = fun y => ∑ i, d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y := by
  constructor
  · intro hF
    induction hF using AddSubgroup.closure_induction with
    | mem F hF =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hF
      have hx : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]
        exact Submodule.subset_span ⟨f, fun τ => hf τ, rfl⟩
      obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
      refine ⟨fun i => r * (z i : ℂ_[p]), fun i => ?_, ?_⟩
      · rw [norm_mul]
        exact mul_le_one₀ hr (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)
      · funext y
        rw [prod_eval_eq_evM, ← hz]
        simp only [evM, map_sum, map_zsmul, zsmul_eq_mul, map_mul, map_intCast, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    | zero => exact ⟨0, fun _ => by simp, by funext y; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, rfl⟩ := hx
      obtain ⟨d', hd', rfl⟩ := hy
      refine ⟨d + d', fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hd i) (hd' i)), ?_⟩
      funext v
      simp [add_mul, Finset.sum_add_distrib]
    | neg x _ hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine ⟨-d, fun i => by rw [Pi.neg_apply, norm_neg]; exact hd i, ?_⟩
      funext v
      simp [neg_mul, Finset.sum_neg_distrib]
  · rintro ⟨d, hd, rfl⟩
    have key : ∀ x ∈ Submodule.span ℤ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ,
        (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}, ∀ a : ℂ_[p], ‖a‖ ≤ 1 →
        (fun y => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) y) ∈
          WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW) := by
      intro x hx a ha
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        refine AddSubgroup.subset_closure ⟨a, f, ha, fun τ => hf τ, ?_⟩
        funext y
        rw [prod_eval_eq_evM]
      | zero =>
        have e : (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) 0) y) = 0 := by
          funext y
          simp [evM]
        rw [e]
        exact zero_mem _
      | add x y _ _ hx hy =>
        have e : (fun v : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (x + y)) v) =
            (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) v) +
              (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) y) v) := by
          funext v
          simp [evM, mul_add]
        rw [e]
        exact add_mem hx hy
      | smul z x _ hx =>
        have e : (fun v : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (z • x)) v) =
            z • (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) v) := by
          funext v
          simp only [evM, map_zsmul, zsmul_eq_mul, map_mul, map_intCast, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e]
        exact zsmul_mem hx z
    have e : (fun y => ∑ i, d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y) =
        ∑ i, (fun y => d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y) := by
      funext y
      simp [Finset.sum_apply]
    rw [e]
    refine sum_mem fun i _ => key _ ?_ _ (hd i)
    rw [← Z.span_eq]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem map_mem_vlIntSpan_iff_delW : ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl) {p : ℕ} [Fact p.Prime] (φ : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖φ x‖ ≤ 1) → ∀ {n : ℕ} (lam : ι → DomWeight n) (G : MvPolynomial (ι × Fin n × Fin n) K), G ∈ Formalism.L2.DIV.VV K lam → (MvPolynomial.map σ G ∈ vlIntSpan σ Pl w lam ↔ (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ G)) ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW)) := by
  classical
  intro K ι _ _ _ σ Pl w p _ φ hφ n lam G hG
  choose r e hr using fun τ => exists_weylBasis n (lam τ).natW (natW_anti (lam τ))
  set Z := zOf lam e with hZ
  have hG' : G ∈ Submodule.span K (Set.range fun i => MvPolynomial.map (Int.castRingHom K) (Z.bZ i)) := by
    rw [Z.span_F K]
    exact hG
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hG'
  have hmap : ∀ (L : Type) [Field L] (s : K →+* L), MvPolynomial.map s G =
      ∑ i, s (c i) • MvPolynomial.map (Int.castRingHom L) (Z.bZ i) := by
    intro L _ s
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, ← MvPolynomial.smul_eq_C_mul]
    have h : s.comp (Int.castRingHom K) = Int.castRingHom L := RingHom.ext_int _ _
    rw [h]
  show _ ↔ evM (MvPolynomial.map φ G) ∈ _
  rw [mem_vlIntSpan_iff σ Pl w lam Z, mem_delW_iff lam Z]
  constructor
  · rintro ⟨c', hc', he⟩
    have hcc : c = c' := by
      rw [hmap ℂ σ] at he
      have h0 : ∑ i, (σ (c i) - σ (c' i)) • MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ i) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, he, sub_self]
      funext i
      exact σ.injective (sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (Z.li ℂ) _ h0 i))
    subst hcc
    refine ⟨fun i => φ (c i), fun i => (hφ _).1 (hc' i), ?_⟩
    funext y
    rw [hmap ℂ_[p] φ]
    simp [evM, MvPolynomial.smul_eval]
  · rintro ⟨d, hd, he⟩
    have hpoly : MvPolynomial.map φ G = ∑ i, d i • MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i) := by
      apply MvPolynomial.funext
      intro x
      have h1 := congrFun he (fun τ a b => x (τ, a, b))
      rw [map_sum]
      simp only [MvPolynomial.smul_eval]
      exact h1
    rw [hmap ℂ_[p] φ] at hpoly
    have hcd : ∀ i, φ (c i) = d i := by
      have h0 : ∑ i, (φ (c i) - d i) • MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hpoly, sub_self]
      exact fun i => sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (Z.li ℂ_[p]) _ h0 i)
    exact ⟨c, fun i => (hφ _).2 ((hcd i).symm ▸ hd i), hmap ℂ σ⟩

end GlobalTheory.Mem.IntSpanDelW
