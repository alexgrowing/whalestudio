import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.JExExists
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem ml {R : Type} [CommRing R] (x y : Matrix.SpecialLinearGroup (Fin 2) R) (i k : Fin 2) :
    (x * y).1 i k = x.1 i 0 * y.1 0 k + x.1 i 1 * y.1 1 k := by
  show (x.1 * y.1) i k = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.ConvolutionTheory.R2.H.genV :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K) (g : G1 K), IntAt v g → g ∈ Subgroup.closure ({x : G1 K | ∃ b, IsInt (cp v b) ∧ x = nU b} ∪ {wW K}) := by
  intro K _ _ v g hg
  obtain ⟨⟨j, hj⟩, hJ⟩ := jEx K v
  obtain ⟨-, -, -, je⟩ := hJ j hj
  clear hJ
  obtain ⟨sa, sm, sc, -⟩ := sgLaws K v
  have s0 : sg v (0 : Kv v) = 0 := by simpa using (sm 0 0).symm
  set C := Subgroup.closure ({x : G1 K | ∃ b, IsInt (cp v b) ∧ x = nU b} ∪ {wW K}) with hC
  have hw : wW K ∈ C := Subgroup.subset_closure (Or.inr rfl)
  have hn : ∀ b, IsInt (cp v b) → nU b ∈ C := fun b hb => Subgroup.subset_closure (Or.inl ⟨b, hb, rfl⟩)
  let nv : Kv v → Matrix.SpecialLinearGroup (Fin 2) (Kv v) := fun b => ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩
  let lv : Kv v → Matrix.SpecialLinearGroup (Fin 2) (Kv v) := fun b => ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two]⟩
  let wv : Matrix.SpecialLinearGroup (Fin 2) (Kv v) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  have jn : ∀ b, j (nv b) = nU (sg v b) := fun b => by
    ext i k : 1
    rw [je]
    fin_cases i <;> fin_cases k <;> simp [nv, nU, s0]
  have jl : ∀ b, j (lv b) * wW K = wW K * nU (-sg v b) := fun b => by
    have : j (lv b) = ⟨!![1, 0; sg v b, 1], by simp [Matrix.det_fin_two]⟩ := by
      ext i k : 1
      rw [je]
      fin_cases i <;> fin_cases k <;> simp [lv, s0]
    rw [this]
    ext i k : 1
    refine (ml _ _ i k).trans (Eq.trans ?_ (ml _ _ i k).symm)
    fin_cases i <;> fin_cases k <;> simp [wW, nU]
  have one : IsInt (1 : Kv v) := (map_one (Valued.v (R := Kv v))).le
  have h1 : ∀ x : Matrix.SpecialLinearGroup (Fin 2) (Kv v), (∀ i k, IsInt (x i k)) → Valued.v (x 1 0) = 1 → j x ∈ C := fun x hx hc => by
    have c0 : x 1 0 ≠ 0 := fun e => by simp [e] at hc
    have hd := x.det_coe
    rw [Matrix.det_fin_two] at hd
    have e : x = nv ((x 0 0 - 1) / x 1 0) * lv (x 1 0) * nv ((x 1 1 - 1) / x 1 0) := by
      ext i k : 1
      simp only [ml]
      fin_cases i <;> fin_cases k <;> simp [nv, lv] <;> field_simp
      all_goals first | ring1 | linear_combination hd | linear_combination (-1 : Kv v) * hd
    have hi : ∀ y, IsInt y → IsInt (cp v (sg v ((y - 1) / x 1 0))) := fun y hy => by
      rw [sc]
      show Valued.v _ ≤ 1
      rw [map_div₀, hc, div_one]
      exact Valuation.map_sub_le _ hy one
    rw [e, map_mul, map_mul, jn, jn, eq_mul_inv_of_mul_eq (jl _)]
    refine C.mul_mem (C.mul_mem (hn _ (hi _ (hx 0 0))) (C.mul_mem (C.mul_mem hw (hn _ ?_)) (C.inv_mem hw))) (hn _ (hi _ (hx 1 1)))
    rw [map_neg, sc]
    show Valued.v _ ≤ 1
    rw [Valuation.map_neg, hc]
  have zero : IsInt (0 : Kv v) := by simp [IsInt]
  have hwv : j wv ∈ C := h1 wv (fun i k => by fin_cases i <;> fin_cases k <;> simp [wv, IsInt]) (by simp [wv])
  have h2 : ∀ x : Matrix.SpecialLinearGroup (Fin 2) (Kv v), (∀ i k, IsInt (x i k)) → j x ∈ C := fun x hx => by
    by_cases hc : Valued.v (x 1 0) = 1
    · exact h1 x hx hc
    have hd := x.det_coe
    rw [Matrix.det_fin_two] at hd
    have ha : Valued.v (x 0 0) = 1 := by
      by_contra ha
      have a1 : Valued.v (x 0 0 * x 1 1) < 1 := by
        rw [map_mul]
        exact mul_lt_one_of_lt_of_le (lt_of_le_of_ne (hx 0 0) ha) (hx 1 1)
      have a2 : Valued.v (x 0 1 * x 1 0) < 1 := by
        rw [map_mul, mul_comm]
        exact mul_lt_one_of_lt_of_le (lt_of_le_of_ne (hx 1 0) hc) (hx 0 1)
      have := Valuation.map_sub_lt _ a1 a2
      rw [hd, map_one] at this
      exact lt_irrefl _ this
    have e : ∀ k, (wv * x) 0 k = x 1 k ∧ (wv * x) 1 k = -x 0 k := fun k => by
      constructor <;> rw [ml] <;> simp [wv]
    have := h1 (wv * x) (fun i k => by
      fin_cases i
      · exact (e k).1 ▸ hx 1 k
      · show Valued.v ((wv * x) 1 k) ≤ 1
        rw [(e k).2, Valuation.map_neg]
        exact hx 0 k) (by rw [(e 0).2, Valuation.map_neg, ha])
    rw [map_mul] at this
    exact (C.mul_mem_cancel_left hwv).1 this
  let p : G1 K →* Matrix.SpecialLinearGroup (Fin 2) (Kv v) := Matrix.SpecialLinearGroup.map (cp v)
  have pa : ∀ k i l, p k i l = cp v (k i l) := fun _ _ _ => rfl
  have pj : ∀ x, p (j x) = x := fun x => by
    ext i k : 1
    rw [pa, je, map_add, sc]
    fin_cases i <;> fin_cases k <;> simp
  have cm : ∀ x k, p k = 1 → j x * k = k * j x := fun x k hk => by
    have hk' : ∀ i l y, k i l * sg v y = sg v ((1 : Matrix (Fin 2) (Fin 2) (Kv v)) i l * y) := fun i l y => by
      rw [sm, ← pa, hk]
      rfl
    ext i l : 1
    simp only [ml, je, add_mul, mul_add, mul_comm (sg v _), hk']
    fin_cases i <;> fin_cases l <;> simp [s0, Matrix.one_apply, add_comm]
  have h3 : ∀ k : G1 K, k * (j (p k))⁻¹ ∈ C := fun k => by
    have hk : k ∈ Subgroup.closure (Set.range (nU (F := K)) ∪ {wW K}) := (gen K).1 ▸ Subgroup.mem_top k
    have one' : ∀ k : G1 K, p (k * (j (p k))⁻¹) = 1 := fun k => by rw [map_mul, map_inv, pj, mul_inv_cancel]
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | rfl
      · have e1 : p (nU b) = nv (cp v b) := by
          ext i k : 1
          rw [pa]
          fin_cases i <;> fin_cases k <;> simp [nv, nU]
        have e2 : nU b = nU (b - sg v (cp v b)) * nU (sg v (cp v b)) := by
          ext i k : 1
          rw [ml]
          fin_cases i <;> fin_cases k <;> simp [nU]
        rw [e1, jn, mul_inv_eq_of_eq_mul e2]
        exact hn _ (by rw [map_sub, sc, sub_self]; exact zero)
      · have e1 : p (wW K) = wv := by
          ext i k : 1
          rw [pa]
          fin_cases i <;> fin_cases k <;> simp [wv, wW]
        rw [e1]
        exact C.mul_mem hw (C.inv_mem hwv)
    | one => simp
    | mul x y _ _ hx hy =>
      have e := cm (p x)⁻¹ _ (one' y)
      have e' : x * y * (j (p (x * y)))⁻¹ = x * (j (p x))⁻¹ * (y * (j (p y))⁻¹) := by
        rw [mul_assoc x (j (p x))⁻¹, ← map_inv j (p x), e, map_mul, map_mul, map_inv]
        group
      rw [e']
      exact C.mul_mem hx hy
    | inv x _ hx =>
      have e := cm (p x) _ (one' x)
      have e' : x⁻¹ * (j (p x⁻¹))⁻¹ = (x * (j (p x))⁻¹)⁻¹ := by
        rw [map_inv, map_inv, inv_inv]
        have : j (p x) * x = x * j (p x) := by
          have h := congrArg (· * j (p x)) e
          simpa [mul_assoc] using h
        rw [_root_.mul_inv_rev, inv_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← this, mul_inv_cancel_right]
      rw [e']
      exact C.inv_mem hx
  have := C.mul_mem (h3 g) (h2 (p g) fun i k => hg i k)
  rwa [inv_mul_cancel_right] at this
