import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.Reduce

theorem house_zero' {E : Type} [Field E] [NumberField E] : house (0 : E) = 0 := by simp [house]

theorem exists_small_frame : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E], OrthoSmall E → ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) E) (N₀ N : ℤ), (∀ a b, star (G a b) = G b a) → G.det ≠ 0 → N₀ ≠ 0 → N ≠ 0 → ∃ (S : Set E) (C : ℝ) (k : ℕ), S.Finite ∧ (0 : E) ∉ S ∧ ∀ (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (d : ℕ), 0 < d → Λ.FG → (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((N₀ : E) * ∑ a, ∑ b, x a * G a b * star (y b))) → (∀ y : Fin n → E, (∀ x ∈ Λ, IsIntegral ℤ ((N₀ : E) * ∑ a, ∑ b, y a * G a b * star (x b))) → (N : E) • y ∈ Λ) → (∀ i, (Pi.single i (d : E) : Fin n → E) ∈ Λ) → ∃ (P : Matrix (Fin n) (Fin n) E) (δ : Fin n → E), (∀ j, (fun i => P i j) ∈ Λ) ∧ (∀ i, δ i ∈ S) ∧ Pᵀ * G * P.map star = Matrix.diagonal δ ∧ ∀ i j, NumberField.house (P i j) ≤ C * (d : ℝ) ^ k := by
  intro E _ _ _ hO n G N₀ N hG hdet hN₀ hN
  have hN₀' : (N₀ : E) ≠ 0 := by exact_mod_cast hN₀
  obtain ⟨S, k, hS, hS0, H⟩ := hO n N hN
  let h : (Fin n → E) →ₗ[E] (Fin n → E) →ₗ⋆[E] E :=
    LinearMap.mk₂'ₛₗ _ _ (fun x y => (N₀ : E) * ∑ a, ∑ b, x a * G a b * star (y b))
      (fun x y z => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add])
      (fun c x y => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
      (fun x y z => by simp only [Pi.add_apply, star_add, Finset.sum_add_distrib, mul_add])
      (fun c x y => by
        simp only [Pi.smul_apply, smul_eq_mul, starRingEnd_apply, star_mul', Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
  have hh : ∀ x y, h x y = (N₀ : E) * ∑ a, ∑ b, x a * G a b * star (y b) := fun _ _ => rfl
  set K : ℝ := house (N₀ : E) * ∑ a, ∑ b, house (G a b) with hK
  have hK0 : 0 ≤ K := mul_nonneg (house_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => house_nonneg _)
  have hle : ∀ (x : Fin n → E) i, house (x i) ≤ ∑ j, house (x j) := fun x i =>
    Finset.single_le_sum (f := fun j => house (x j)) (fun _ _ => house_nonneg _) (Finset.mem_univ i)
  have hs0 : ∀ x : Fin n → E, 0 ≤ ∑ j, house (x j) := fun x => Finset.sum_nonneg fun _ _ => house_nonneg _
  refine ⟨(fun z => (N₀ : E)⁻¹ * z) '' S, (2 * (1 + K)) ^ k, k, hS.image _, ?_, ?_⟩
  · rintro ⟨z, hz, h0⟩
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact inv_ne_zero hN₀' h1
    · exact hS0 (h1 ▸ hz)
  intro Λ d hd hfg hint hdual hsing
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsz : Sized h (Λ.restrictScalars ℤ) N (fun x => (1 + K) * ∑ j, house (x j)) (2 * (1 + K) * d) :=
    { symm := fun x y => by
        simp only [hh, star_mul', star_sum, star_star, star_intCast, hG]
        rw [Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      nondeg := fun y hy => by
        refine Matrix.eq_zero_of_vecMul_eq_zero hdet (funext fun j => ?_)
        have := (mul_eq_zero.1 ((hh _ _).symm.trans (hy (Pi.single j 1)))).resolve_left hN₀'
        simpa [Pi.single_apply, apply_ite, Matrix.vecMul, dotProduct] using this
      fg := hfg.restrictScalars
      stable := fun a ha x hx => Λ.smul_mem (⟨a, ha⟩ : 𝓞 E) hx
      int := hint
      dual := hdual
      two_le := by nlinarith
      nonneg := fun x => mul_nonneg (by linarith) (hs0 x)
      add_le := fun x y => by
        rw [← mul_add, ← Finset.sum_add_distrib]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => house_add_le _ _) (by linarith)
      smul_le := fun a x => by
        rw [mul_left_comm, Finset.mul_sum _ _ (house a)]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => house_mul_le _ _) (by linarith)
      form_le := fun x y => by
        have h1 : house (∑ a, ∑ b, x a * G a b * star (y b)) ≤
            (∑ a, ∑ b, house (G a b)) * ((∑ j, house (x j)) * ∑ j, house (y j)) := by
          rw [Finset.sum_mul]
          refine (house_sum_le_sum_house _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          rw [Finset.sum_mul]
          refine (house_sum_le_sum_house _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          refine (house_mul_le _ _).trans ?_
          rw [house_star]
          calc house (x a * G a b) * house (y b) ≤ (house (x a) * house (G a b)) * house (y b) :=
                mul_le_mul_of_nonneg_right (house_mul_le _ _) (house_nonneg _)
            _ = house (G a b) * (house (x a) * house (y b)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (hle x a) (hle y b) (house_nonneg _) (hs0 x))
                (house_nonneg _)
        have h2 := mul_nonneg (hs0 x) (hs0 y)
        calc house (h x y) ≤ house (N₀ : E) * house (∑ a, ∑ b, x a * G a b * star (y b)) := house_mul_le _ _
          _ ≤ K * ((∑ j, house (x j)) * ∑ j, house (y j)) := by
            rw [hK, mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (house_nonneg _)
          _ ≤ ((1 + K) * (1 + K)) * ((∑ j, house (x j)) * ∑ j, house (y j)) :=
            mul_le_mul_of_nonneg_right (by nlinarith) h2
          _ = _ := by ring
      span := by
        rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        have h1 : ∑ j, house ((Pi.single i (d : E) : Fin n → E) j) = d := by
          rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, house_zero']) (by simp),
            Pi.single_eq_same]
          simpa using house_intCast (K := E) d
        have h2 : (Pi.basisFun E (Fin n)) i = (d : E)⁻¹ • (Pi.single i (d : E) : Fin n → E) := by
          have : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
          rw [← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ this, Pi.basisFun_apply]
        rw [h2]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hsing i, ?_⟩)
        rw [h1]; nlinarith }
  obtain ⟨v, h1, h2, h3⟩ := H _ h _ _ _ (by simp) hsz
  refine ⟨Matrix.of fun i j => v j i, fun i => (N₀ : E)⁻¹ * h (v i) (v i), h1, fun i => ⟨_, (h3 i).1, rfl⟩, ?_, ?_⟩
  · ext i j
    have e : ((Matrix.of fun i j => v j i)ᵀ * G * (Matrix.of fun i j => v j i).map star) i j =
        (N₀ : E)⁻¹ * h (v i) (v j) := by
      rw [hh, inv_mul_cancel_left₀ hN₀', Finset.sum_comm]
      simp [Matrix.mul_apply, Finset.sum_mul]
    rw [e, Matrix.diagonal_apply]
    split_ifs with hij
    · rw [hij]
    · rw [h2 i j hij, mul_zero]
  · intro i j
    rw [← mul_pow]
    have := hle (v j) i
    have h4 := hs0 (v j)
    refine le_trans ?_ (h3 j).2
    change house (v j i) ≤ _
    nlinarith

theorem house_mul_mul_le {E : Type} [Field E] [NumberField E] {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : Matrix (Fin n) (Fin n) E) (b : ℝ), (∀ i j, house (X i j) ≤ b) →
      ∀ i j, house ((A * X * B) i j) ≤ C * b := by
  have h0 : ∀ i j l k, 0 ≤ house (A i k) * house (B l j) := fun _ _ _ _ =>
    mul_nonneg (house_nonneg _) (house_nonneg _)
  have h1 : ∀ p : Fin n × Fin n, 0 ≤ ∑ l, ∑ k, house (A p.1 k) * house (B l p.2) := fun p =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => h0 _ _ _ _
  refine ⟨∑ p : Fin n × Fin n, ∑ l, ∑ k, house (A p.1 k) * house (B l p.2),
    Finset.sum_nonneg fun p _ => h1 p, fun X b hX i j => ?_⟩
  have hb : 0 ≤ b := (house_nonneg _).trans (hX i j)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun p _ => h1 p) (Finset.mem_univ (i, j))) hb)
  simp only [Matrix.mul_apply, Finset.sum_mul]
  refine (house_sum_le_sum_house _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  refine (house_sum_le_sum_house _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  calc house (A i k * X k l * B l j) ≤ house (A i k * X k l) * house (B l j) := house_mul_le _ _
    _ ≤ (house (A i k) * house (X k l)) * house (B l j) :=
      mul_le_mul_of_nonneg_right (house_mul_le _ _) (house_nonneg _)
    _ = house (A i k) * house (B l j) * house (X k l) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hX k l) (h0 _ _ _ _)

theorem exists_unitary_to_finite : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (n : ℕ) (G : Matrix (Fin n) (Fin n) E) (S : Set E) (ι : Type) (P : ι → Matrix (Fin n) (Fin n) E) (δ : ι → Fin n → E) (b : ι → ℝ), S.Finite → (0 : E) ∉ S → (∀ t i, δ t i ∈ S) → (∀ t, (P t)ᵀ * G * (P t).map star = Matrix.diagonal (δ t)) → (∀ t i j, NumberField.house (P t i j) ≤ b t) → ∃ (T : Set (GL (Fin n) E)) (C : ℝ), T.Finite ∧ 0 ≤ C ∧ ∀ t, ∃ (γ : GL (Fin n) E), ∃ Q ∈ T, ((γ⁻¹ * Q : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = P t ∧ (γ : Matrix (Fin n) (Fin n) E)ᵀ * G * (γ : Matrix (Fin n) (Fin n) E).map star = G ∧ ∀ i j, NumberField.house ((γ : Matrix (Fin n) (Fin n) E) i j) ≤ C * b t ∧ NumberField.house (((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) ≤ C * b t := by
  intro E _ _ _ n G S ι P δ b hS hS0 hδ hP hb
  have hD : ∀ t, (Matrix.diagonal (δ t)).det ≠ 0 := fun t => by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ h => hS0 (h ▸ hδ t i)
  have hdet : ∀ t, (P t).det ≠ 0 := fun t h => hD t (by
    rw [← hP t, det_mul, det_mul, det_transpose, h, zero_mul, zero_mul])
  let U : ι → GL (Fin n) E := fun t => Matrix.GeneralLinearGroup.mkOfDetNeZero (P t) (hdet t)
  have hU : ∀ t, (U t : Matrix (Fin n) (Fin n) E) = P t := fun _ => rfl
  have hinv : ∀ t, (((U t)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      (Matrix.diagonal (δ t))⁻¹ * ((P t).map star)ᵀ * Gᵀ := fun t => by
    have h1 := congrArg Matrix.transpose (hP t)
    rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose] at h1
    rw [Matrix.coe_units_inv, hU]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.nonsing_inv_mul _ (hD t).isUnit]
  have hfin : (Set.range δ).Finite := (Set.Finite.pi' fun _ : Fin n => hS).subset (by
    rintro _ ⟨t, rfl⟩; exact hδ t)
  haveI := hfin.fintype
  choose s hs using fun u : Set.range δ => u.2
  choose C₁ hC₁ h₁ using fun u : Set.range δ => house_mul_mul_le (P (s u) * (Matrix.diagonal u.1)⁻¹) Gᵀ
  choose C₂ hC₂ h₂ using fun u : Set.range δ =>
    house_mul_mul_le 1 (((U (s u))⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
  refine ⟨Set.range fun u => U (s u), ∑ u, (C₁ u + C₂ u), Set.finite_range _,
    Finset.sum_nonneg fun u _ => add_nonneg (hC₁ u) (hC₂ u), fun t => ?_⟩
  let u : Set.range δ := ⟨δ t, t, rfl⟩
  have hle : C₁ u + C₂ u ≤ ∑ u, (C₁ u + C₂ u) :=
    Finset.single_le_sum (f := fun u => C₁ u + C₂ u) (fun u _ => add_nonneg (hC₁ u) (hC₂ u)) (Finset.mem_univ u)
  refine ⟨U (s u) * (U t)⁻¹, _, ⟨u, rfl⟩, by simp [hU], ?_, fun i j => ?_⟩
  · have h1 : (P (s u))ᵀ * G * (P (s u)).map star = (P t)ᵀ * G * (P t).map star := by
      rw [hP, hP, hs u]
    have h2 : P t * (((U t)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := (U t).mul_inv
    have h3 : ∀ A B : Matrix (Fin n) (Fin n) E, (A * B).map star = A.map star * B.map star :=
      fun A B => Matrix.map_mul (f := starRingEnd E)
    rw [Units.val_mul, hU]
    generalize (((U t)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = Y at h2 ⊢
    calc (P (s u) * Y)ᵀ * G * (P (s u) * Y).map star = Yᵀ * ((P (s u))ᵀ * G * (P (s u)).map star) * Y.map star := by
          simp only [transpose_mul, h3, Matrix.mul_assoc]
      _ = (P t * Y)ᵀ * G * (P t * Y).map star := by
          rw [h1]; simp only [transpose_mul, h3, Matrix.mul_assoc]
      _ = G := by rw [h2, Matrix.map_one _ (star_zero _) (star_one _)]; simp
  · have hb0 : 0 ≤ b t := (house_nonneg _).trans (hb t i j)
    constructor
    · have := h₁ u ((P t).map star)ᵀ (b t) (fun i j => (house_star _).trans_le (hb t j i)) i j
      rw [Units.val_mul, hU, hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact this.trans (mul_le_mul_of_nonneg_right (by linarith [hC₂ u]) hb0)
    · have := h₂ u (P t) (b t) (hb t) i j
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hU]
      rw [Matrix.one_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_right (by linarith [hC₁ u]) hb0)

theorem exists_nat_integral {E : Type} [Field E] [NumberField E] {κ : Type} [Finite κ] (A : κ → E) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, IsIntegral ℤ ((m : E) * A i) := by
  classical
  haveI := Fintype.ofFinite κ
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image A)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ?_⟩
  have h1 := h (A i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [zsmul_eq_mul] at h1
  rw [← Int.cast_natCast, Int.natCast_natAbs]
  rcases abs_choice y with e | e <;> rw [e]
  · exact h1
  · rw [Int.cast_neg, neg_mul]; exact h1.neg

variable {D : D7}

theorem incl_mul_mem {e : D.host.E} (he : IsIntegral ℤ e) {x : Af D.host.F ⊗[D.host.F] D.host.E}
    (hx : x ∈ intAE D) : inclR (F := D.host.F) (Af D.host.F) e * x ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨a, ha, ⟨e, he⟩ * y, ?_⟩
    simp [inclR]
    rfl
  | zero => simp
  | add x y _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg x _ h => rw [mul_neg]; exact neg_mem h

theorem sig_mem {x : Af D.host.F ⊗[D.host.F] D.host.E}
    (hx : x ∈ intAE D) : sigR (Af D.host.F) D.sp.cm.sig x ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨a, ha, ⟨D.sp.cm.sig y,
      IsIntegral.map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom y.2⟩, ?_⟩
    simp [sigR]
    rfl
  | zero => simp
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg]; exact neg_mem h

theorem den_mul_mul {n : ℕ} {κ : Type} [Finite κ] (A B : κ → Matrix (Fin n) (Fin n) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ ∀ k (X : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) (d : ℕ),
      (∀ i j, d • X i j ∈ intAE D) → ∀ i j, (m * d) • ((A k).map (inclR (F := D.host.F) (Af D.host.F)) * X *
        (B k).map (inclR (F := D.host.F) (Af D.host.F))) i j ∈ intAE D := by
  obtain ⟨m, hm, h⟩ := exists_nat_integral fun p : κ × Fin n × Fin n × Fin n × Fin n =>
    A p.1 p.2.1 p.2.2.1 * B p.1 p.2.2.2.1 p.2.2.2.2
  refine ⟨m, hm, fun k X d hX i j => ?_⟩
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.smul_sum, Matrix.map_apply]
  refine sum_mem fun l _ => sum_mem fun q _ => ?_
  have := incl_mul_mem (h (k, i, q, l, j)) (hX q l)
  convert this using 1
  simp only [map_mul, map_natCast, nsmul_eq_mul, Nat.cast_mul]
  ring

theorem den_hat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hL : L.FG) :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)), ∀ i, m • z i ∈ intAE D := by
  obtain ⟨s, rfl⟩ := hL
  obtain ⟨m, hm, h⟩ := exists_nat_integral fun p : s × Fin n => p.1.1 p.2
  have h1 : ∀ x ∈ Submodule.span (𝓞 D.host.E) (s : Set (Fin n → D.host.E)), ∀ i,
      IsIntegral ℤ ((m : D.host.E) * x i) := by
    intro x hx i
    induction hx using Submodule.span_induction with
    | mem x hx => exact h (⟨x, hx⟩, i)
    | zero => simpa using isIntegral_zero
    | add x y _ _ h1 h2 => rw [Pi.add_apply, mul_add]; exact h1.add h2
    | smul c x _ h => rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]; exact IsIntegral.mul c.2 h
  refine ⟨m, hm, fun z hz i => ?_⟩
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨a, ha, ⟨_, h1 y hy i⟩, ?_⟩
    change m • a ⊗ₜ[D.host.F] y i = a ⊗ₜ[D.host.F] ((m : D.host.E) * y i)
    rw [← nsmul_eq_mul, TensorProduct.tmul_smul]
  | zero => simp
  | add x y _ _ h1 h2 => rw [Pi.add_apply, smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [Pi.neg_apply, smul_neg]; exact neg_mem h

theorem eq_of_isometry_inv {R : Type} [Monoid R] {J J' u u' c : R} (hJ : J' * J = 1) (hu : u' * u = 1)
    (h : c * J * u' = J) : J' * c * J = u := by
  calc J' * c * J = J' * (c * J * u') * u := by simp only [mul_assoc, hu, mul_one]
    _ = u := by rw [h, hJ, one_mul]

theorem finHom_eq (V : HSp D) (g : GA D V) :
    V.gram⁻¹.map (inclR (F := D.host.F) (Af D.host.F)) *
      Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (finHom V g⁻¹).1 *
        V.gram.map (inclR (F := D.host.F) (Af D.host.F)) = (finHom V g).1 := by
  refine eq_of_isometry_inv ?_ ?_ (GlobalTheory.Member.finHom_unitary V g⁻¹)
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (gram_det_ne V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem den_cT {n d : ℕ} (X : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (h : ∀ i j, d • X i j ∈ intAE D) (i j : Fin n) :
    d • Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) X i j ∈ intAE D := by
  have h5 := sig_mem (h j i)
  rw [map_nsmul] at h5
  exact h5

theorem bddDen_of_frame : ∀ (D : D7) (V : HSp D) (T : Set (GL (Fin V.rank) D.host.E)), T.Finite → ∃ d : ℕ, 0 < d ∧ ∀ (g γ : GA D V) (γ' : GL (Fin V.rank) D.host.E), ∀ Q ∈ T, GlobalTheory.Member.IsRat V γ γ' → (∀ j, (fun i => ((γ'⁻¹ * Q : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) ∈ Formalism.L2.Pj.latG V g) → BddDen V d (γ * g) := by
  intro D V T hT
  haveI := hT.to_subtype
  obtain ⟨m₀, h₀, H₀⟩ := den_hat _ (GlobalTheory.Member.latG_lattice_and_completion D V 1).1
  obtain ⟨m₁, h₁, H₁⟩ := den_mul_mul (D := D) (fun _ : T => 1)
    fun Q : T => ((Q.1⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
  obtain ⟨m₂, h₂, H₂⟩ := den_mul_mul (D := D) (fun _ : Unit => V.gram⁻¹) fun _ => V.gram
  refine ⟨m₂ * (m₁ * m₀), by positivity, fun g γ γ' Q hQ hr hcol => ?_⟩
  set ι := inclR (F := D.host.F) (E := D.host.E) (Af D.host.F) with hι
  have hZ : ∀ i j, m₀ • ((finHom V g⁻¹).1 * ((γ'⁻¹ * Q : GL (Fin V.rank) D.host.E) :
      Matrix (Fin V.rank) (Fin V.rank) D.host.E).map ι) i j ∈ intAE D := by
    intro i j
    have h1 := hcol j
    rw [← SetLike.mem_coe, (GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.1] at h1
    obtain ⟨z, hz, e⟩ := h1
    have e2 : (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
    rw [e] at e2
    have := H₀ z hz i
    rw [← e2] at this
    exact this
  have hinv : ∀ i j, (m₁ * m₀) • (finHom V (γ * g)⁻¹).1 i j ∈ intAE D := by
    intro i j
    have := H₁ ⟨Q, hQ⟩ _ _ hZ i j
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_assoc, ← Matrix.map_mul,
      ← Units.val_mul, mul_inv_cancel_right,
      ← GlobalTheory.Member.RatElt.fin_eq ((GlobalTheory.Member.RatElt.rational_elements D V).2.2.2.1 γ γ' γ γ' hr hr).2,
      ← Units.val_mul, ← map_mul, ← _root_.mul_inv_rev] at this
    exact this
  intro i j
  constructor
  · have := H₂ () _ _ (den_cT _ hinv) i j
    rw [finHom_eq] at this
    exact this
  · rw [mul_smul]
    exact AddSubgroup.nsmul_mem _ (hinv i j) _

theorem exists_int_bounds {E : Type} [Field E] [NumberField E]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) :
    ∃ N₀ m : ℤ, N₀ ≠ 0 ∧ m ≠ 0 ∧ (∀ z ∈ J, IsIntegral ℤ ((N₀ : E) * z)) ∧
      ∀ z : E, IsIntegral ℤ z → (m : E) * z ∈ J := by
  have key : ∀ I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, I ≠ 0 → ∃ m : ℤ, m ≠ 0 ∧ (m : E) ∈ I := by
    intro I hI
    obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
    have hn : Ideal.absNorm (Ideal.span {x}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hx0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x}))
    refine ⟨Ideal.absNorm (Ideal.span {x}), by exact_mod_cast hn, ?_⟩
    have h : c • algebraMap (𝓞 E) E x ∈ I := Submodule.smul_mem (I : Submodule (𝓞 E) E) c hx
    rw [Algebra.smul_def, ← map_mul, hc] at h
    simpa using h
  obtain ⟨N₀, h0, h1⟩ := key J⁻¹ (inv_ne_zero hJ)
  obtain ⟨m, h2, h3⟩ := key J hJ
  refine ⟨N₀, m, h0, h2, fun z hz => ?_, fun z hz => ?_⟩
  · have := FractionalIdeal.mul_mem_mul h1 hz
    rw [inv_mul_cancel₀ hJ, FractionalIdeal.mem_one_iff] at this
    obtain ⟨r, hr⟩ := this
    rw [← hr]; exact r.2
  · have h : (⟨z, hz⟩ : 𝓞 E) • (m : E) ∈ J := Submodule.smul_mem (J : Submodule (𝓞 E) E) _ h3
    rw [Algebra.smul_def, mul_comm] at h
    exact h

theorem normInf_le {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
    (hθ : IsInfFam θ) {γ : GA D V} {γ' : GL (Fin V.rank) D.host.E} (h : GlobalTheory.Member.IsRat V γ γ') {K : ℝ}
    (hK : ∀ i j, house ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) ≤ K ∧
      house (((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) ≤ K) :
    normInf θ V γ ≤ (∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (2 : ℝ)) * K := by
  obtain ⟨-, -, -, h4, h5⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  have e : ∀ (γ : GA D V) γ', GlobalTheory.Member.IsRat V γ γ' → ∀ τ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) γ i j‖ ≤
      house ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
    intro γ γ' h τ i j
    have h1 : infMat D.sp.cm.sig V.gram (θ τ) γ = _ := (h5 γ γ' h).2 _ _ (hθ τ)
    rw [h1]
    exact norm_le_pi_norm (canonicalEmbedding D.host.E _) (tauE D τ)
  simp only [normInf, Finset.sum_mul]
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 := e γ γ' h τ i j
  have h2 := e _ _ (h4 γ γ' γ γ' h h).2 τ i j
  linarith [(hK i j).1, (hK i j).2]

theorem isRat_of_unitary {D : D7} (V : HSp D) (γ : GL (Fin V.rank) D.host.E)
    (h : (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)ᵀ * V.gramᵀ *
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map star = V.gramᵀ) :
    ∃ x ∈ GQ V, GlobalTheory.Member.IsRat V x γ := by
  have : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  have h1 : γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    have h2 := congrArg Matrix.transpose h
    rw [transpose_mul, transpose_mul, transpose_transpose, transpose_transpose, ← Matrix.mul_assoc] at h2
    exact h2
  have h3 : GlobalTheory.Member.IsRat V ⟨_, (GlobalTheory.Member.RatElt.bc_mem_HR_iff (AF D.host.F) _ _ γ).2 h1⟩ γ := rfl
  exact ⟨_, ((GlobalTheory.Member.RatElt.rational_elements D V).1 _).2 ⟨_, h3⟩, h3⟩

theorem reduction : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    IsInfFam θ → OrthoSmall D.host.E → DenomBound θ V → ∃ (d : ℕ) (C : ℝ) (M : ℕ), 0 < d ∧ ∀ g : GA D V,
      ∃ γ ∈ GQ V, BddDen V d (γ * g) ∧ normInf θ V γ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ M := by
  intro D θ V hθ hO ⟨C₁, M, hd⟩
  choose d hd0 hdle hdmem using hd
  obtain ⟨-, -, -, -, -, -, -, hG, hdet, -, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨N₀, m, hN₀, hm, hint, hmem⟩ := exists_int_bounds (D.host.AA * D.host.AAbar)
    (mul_ne_zero (Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D))
  obtain ⟨S, C₂, k, hS, hS0, hP⟩ := exists_small_frame D.host.E hO V.rank V.gramᵀ N₀ (m * N₀) hG hdet hN₀ (mul_ne_zero hm hN₀)
  have hP' := fun g : GA D V => hP (Formalism.L2.Pj.latG V g) (d g) (hd0 g)
    (GlobalTheory.Member.latG_lattice_and_completion D V g).1
    (fun x hx y hy => hint _ ((GlobalTheory.Member.LatSelfDual.selfDual V g x).2 hx y hy))
    (fun y hy => (GlobalTheory.Member.LatSelfDual.selfDual V g _).1 fun x hx => by
      rw [GlobalTheory.Member.LatSelfDual.frameForm_smul_left, Int.cast_mul, mul_assoc]
      exact hmem _ (hy x hx)) (hdmem g)
  choose P δ hP1 hP2 hP3 hP4 using hP'
  obtain ⟨T, C₃, hT, hC₃, hγ⟩ := exists_unitary_to_finite D.host.E V.rank V.gramᵀ S (GA D V) P δ (fun g => |C₂| * (d g : ℝ) ^ k) hS hS0 hP2 hP3
    fun g i j => (hP4 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  obtain ⟨e, he, hB⟩ := bddDen_of_frame D V T hT
  refine ⟨e, (∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (2 : ℝ)) * (C₃ * (|C₂| * C₁ ^ k)), M * k,
    he, fun g => ?_⟩
  obtain ⟨γ', Q, hQ, h1, h2, h3⟩ := hγ g
  obtain ⟨γ, hγQ, hr⟩ := isRat_of_unitary V γ' h2
  refine ⟨γ, hγQ, hB g γ γ' Q hQ hr (by rw [h1]; exact hP1 g), (normInf_le hθ hr h3).trans ?_⟩
  have h4 : (d g : ℝ) ^ k ≤ C₁ ^ k * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ (M * k) := by
    rw [pow_mul, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) (hdle g) k
  rw [mul_assoc, mul_assoc, mul_assoc]
  gcongr

end GlobalTheory.SmoothForms.Reduce
