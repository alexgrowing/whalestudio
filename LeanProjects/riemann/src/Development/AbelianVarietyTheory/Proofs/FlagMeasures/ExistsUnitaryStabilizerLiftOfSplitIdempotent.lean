import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.SplitLift

open Formalism.UG

variable {A : Type} [CommRing A] {n : ℕ}

theorem exists_lift_matrix {S k : Type} [CommRing S] [Field k] (r : S →+* k) (ε : S)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (M : GL (Fin n) k) :
    ∃ N N' : Matrix (Fin n) (Fin n) S, N.map r = (M : Matrix (Fin n) (Fin n) k) ∧
      N * N' = ε • (1 : Matrix (Fin n) (Fin n) S) ∧ N' * N = ε • (1 : Matrix (Fin n) (Fin n) S) := by
  choose f hf using hr
  let N : Matrix (Fin n) (Fin n) S := (M : Matrix (Fin n) (Fin n) k).map f
  have hN : N.map r = (M : Matrix (Fin n) (Fin n) k) := by
    ext i j; simp [N, hf]
  have hd : r N.det ≠ 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hN]
    exact (Matrix.isUnits_det_units M).ne_zero
  obtain ⟨t, ht⟩ := hloc _ hd
  refine ⟨N, (t * ε) • N.adjugate, hN, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    congr 1; linear_combination ht
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    congr 1; linear_combination ht

theorem exists_gen (S : Subring A) (Λ : Submodule S (Fin n → A)) {k : Type} [Field k]
    (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S) (hfg : Λ.FG)
    (hε : ε * ε = ε) (hrε : r ε = 1)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (hc : Function.Surjective c)
    (hker : ∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) :
    ∃ μ : Fin n → Λ, (∀ a : Fin n → S, c (∑ i, a i • μ i) = fun i => r (a i)) ∧
      (∀ i, ε • μ i = μ i) ∧ ∀ y : Λ, ∃ a : Fin n → S, ε • y = ∑ i, a i • μ i := by
  choose g hg using hc
  let μ : Fin n → Λ := fun i => ε • g (Pi.single i 1)
  have h1 : ∀ a : Fin n → S, c (∑ i, a i • μ i) = fun i => r (a i) := by
    intro a
    rw [map_sum]
    ext j
    simp [μ, map_smulₛₗ, hg, hrε, Finset.sum_apply, Pi.single_apply]
  have h2 : ∀ i, ε • μ i = μ i := fun i => by simp only [μ, smul_smul, hε]
  refine ⟨μ, h1, h2, ?_⟩
  let N : Submodule S (Fin n → A) := Submodule.span S (Set.range fun i => (μ i : Fin n → A))
  have hle : Λ ≤ N ⊔ RingHom.ker r • Λ := by
    intro y hy
    choose f hf using hr
    let a : Fin n → S := fun i => f (c ⟨y, hy⟩ i)
    have h0 : c (⟨y, hy⟩ - ∑ i, a i • μ i) = 0 := by
      rw [map_sub, h1]; ext j; simp [a, hf]
    have h3 := hker _ h0
    have h4 : ((∑ i, a i • μ i : Λ) : Fin n → A) ∈ N := by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ =>
        N.smul_mem (a i) (Submodule.subset_span ⟨i, rfl⟩)
    have : y = ((∑ i, a i • μ i : Λ) : Fin n → A) +
        ((⟨y, hy⟩ - ∑ i, a i • μ i : Λ) : Fin n → A) := by
      rw [Submodule.coe_sub]; simp
    rw [this]
    exact Submodule.add_mem_sup h4 h3
  obtain ⟨z, hz, hzle⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl hle
  have hz1 : r z ≠ 0 := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hz
    rw [hz]; exact one_ne_zero
  obtain ⟨t, ht⟩ := hloc z hz1
  intro y
  have hy : z • (y : Fin n → A) ∈ N := hzle (Submodule.smul_mem_pointwise_smul _ _ _ y.2)
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hy
  refine ⟨fun i => t * ε * b i, Subtype.ext ?_⟩
  have : ε • (y : Fin n → A) = (t * ε) • z • (y : Fin n → A) := by
    rw [smul_smul]; congr 1; linear_combination -ht
  rw [Submodule.coe_smul, this, ← hb, Finset.smul_sum, Submodule.coe_sum]
  simp only [Submodule.coe_smul, smul_smul]

theorem exists_basis (S : Subring A) (Λ : Submodule S (Fin n → A)) {k : Type} [Field k]
    (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S) (hfg : Λ.FG)
    (hsp : Submodule.span A (Λ : Set (Fin n → A)) = ⊤)
    (hε : ε * ε = ε) (hrε : r ε = 1)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (hc : Function.Surjective c)
    (hker : ∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) :
    ∃ B B' : Matrix (Fin n) (Fin n) A, B * B' = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) ∧
      B' * B = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) ∧ (ε : A) • B = B ∧ (ε : A) • B' = B' ∧
      (∀ y : Λ, ∃ a : Fin n → S, B' *ᵥ (y : Fin n → A) = (fun i => (a i : A)) ∧
        c y = fun i => r (a i)) ∧
      ∀ a : Fin n → S, ∃ y : Λ, B *ᵥ (fun i => (a i : A)) = y ∧ c y = fun i => r (a i) := by
  obtain ⟨μ, h1, h2, h3⟩ := exists_gen S Λ r c ε hfg hε hrε hr hloc hc hker
  have hεA : (ε : A) * ε = ε := by exact_mod_cast congrArg Subtype.val hε
  let B : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => (μ j : Fin n → A) i
  have hB : ∀ a : Fin n → S, B *ᵥ (fun i => (a i : A)) = ((∑ i, a i • μ i : Λ) : Fin n → A) := by
    intro a
    ext i
    rw [Submodule.coe_sum]
    simp [B, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm, Subring.smul_def]
  have hεB : (ε : A) • B = B := by
    ext i j
    have := congrFun (congrArg Subtype.val (h2 j)) i
    simpa [B, Subring.smul_def] using this
  have hall : ∀ v : Fin n → A, ∃ w, B *ᵥ w = (ε : A) • v := by
    intro v
    have hv : v ∈ Submodule.span A (Λ : Set (Fin n → A)) := hsp ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha⟩ := h3 ⟨y, hy⟩
      exact ⟨_, by rw [hB a, ← ha]; rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨w, hw⟩ := hy
      exact ⟨u + w, by rw [Matrix.mulVec_add, hu, hw, smul_add]⟩
    | smul a x _ hx =>
      obtain ⟨u, hu⟩ := hx
      exact ⟨a • u, by rw [Matrix.mulVec_smul, hu, smul_comm]⟩
  choose w hw using hall
  let C : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => w (Pi.single j 1) i
  have hBC : B * C = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    ext i j
    have := congrFun (hw (Pi.single j 1)) i
    simpa [C, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply] using this
  let B' : Matrix (Fin n) (Fin n) A := (ε : A) • C
  have hεB' : (ε : A) • B' = B' := by simp only [B', smul_smul, hεA]
  have hBB' : B * B' = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    simp only [B', Matrix.mul_smul, hBC, smul_smul, hεA]
  have hz : (1 - (ε : A)) • B = 0 := by rw [sub_smul, one_smul, hεB, sub_self]
  have hz' : (1 - (ε : A)) • B' = 0 := by rw [sub_smul, one_smul, hεB', sub_self]
  have hsq : (1 - (ε : A)) * (1 - ε) = 1 - ε := by linear_combination hεA
  have hB'B : B' * B = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    have e1 : (B + (1 - (ε : A)) • (1 : Matrix (Fin n) (Fin n) A)) *
        (B' + (1 - (ε : A)) • (1 : Matrix (Fin n) (Fin n) A)) = 1 := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_one, hz, hz', hBB', smul_add, smul_smul, hsq]
      simp [sub_smul]
    have e2 := mul_eq_one_comm.1 e1
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_one, hz, hz', smul_add, smul_smul, hsq] at e2
    simp only [sub_smul, one_smul, add_zero, zero_add] at e2
    linear_combination (norm := abel_nf) e2
  refine ⟨B, B', hBB', hB'B, hεB, hεB', ?_, fun a => ⟨_, hB a, h1 a⟩⟩
  intro y
  obtain ⟨a, ha⟩ := h3 y
  refine ⟨fun i => ε * a i, ?_, ?_⟩
  · have e : (ε : A) • (y : Fin n → A) = B *ᵥ (fun i => (a i : A)) := by
      rw [hB a, ← ha]; rfl
    rw [← hεB', Matrix.smul_mulVec, ← Matrix.mulVec_smul, e, Matrix.mulVec_mulVec, hB'B,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp
  · have := h1 a
    rw [← ha, map_smulₛₗ, hrε, one_smul] at this
    simp [this, hrε]

noncomputable def adj (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  J⁻¹ * cT s Y * J

theorem cT_add (s : A →+* A) (X Y : Matrix (Fin n) (Fin n) A) :
    cT s (X + Y) = cT s X + cT s Y := by ext i j; simp [cT]

theorem cT_smul (s : A →+* A) (a : A) (X : Matrix (Fin n) (Fin n) A) :
    cT s (a • X) = s a • cT s X := by ext i j; simp [cT]

theorem cT_cT (s : A →+* A) (hs : ∀ a, s (s a) = a) (X : Matrix (Fin n) (Fin n) A) :
    cT s (cT s X) = X := by ext i j; simp [cT, hs]

theorem adj_mul (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (X Y : Matrix (Fin n) (Fin n) A) : adj s J X * adj s J Y = adj s J (Y * X) := by
  simp only [adj, cT_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ]

theorem adj_smul (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (a : A)
    (X : Matrix (Fin n) (Fin n) A) : adj s J (a • X) = s a • adj s J X := by
  simp only [adj, cT_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem adj_one (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) :
    adj s J 1 = 1 := by
  simp only [adj, cT_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hJ]

theorem mul_adj (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (X : Matrix (Fin n) (Fin n) A) : J * adj s J X = cT s X * J := by
  simp only [adj, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ]

theorem cT_adj_mul (s : A →+* A) (hs : ∀ a, s (s a) = a) {J : Matrix (Fin n) (Fin n) A}
    (hH : IsHerm s J) (hJ : IsUnit J.det)
    (X : Matrix (Fin n) (Fin n) A) : cT s (adj s J X) * J = J * X := by
  have hH' : cT s J = J := hH
  have h1 : cT s J⁻¹ * J = 1 := by
    have := congrArg (cT s) (Matrix.mul_nonsing_inv _ hJ)
    rwa [cT_mul, cT_one, hH'] at this
  simp only [adj, cT_mul, cT_cT s hs, hH', Matrix.mul_assoc, h1, Matrix.mul_one]

theorem hform_dot (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_adj (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (X : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    hform s J x (adj s J X *ᵥ y) = hform s J (X *ᵥ x) y := by
  rw [hform_dot, hform_dot, Matrix.mulVec_mulVec, mul_adj s hJ, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 1
  ext i
  simp [cT, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, mul_comm]

noncomputable def glue (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (e : A)
    (X X' : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  (1 - e - s e) • (1 : Matrix (Fin n) (Fin n) A) + X + adj s J X'

theorem glue_mul (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) {e : A}
    (he : e * e = e) (hes : e * s e = 0) {X X' : Matrix (Fin n) (Fin n) A}
    (hX : e • X = X) (hX' : e • X' = X') (h : X * X' = e • (1 : Matrix (Fin n) (Fin n) A)) :
    glue s J e X X' * glue s J e X' X = 1 := by
  have hse : s e * s e = s e := by rw [← map_mul, he]
  have a1 : s e • adj s J X = adj s J X := by rw [← adj_smul, hX]
  have a2 : s e • adj s J X' = adj s J X' := by rw [← adj_smul, hX']
  have u1 : (1 - e - s e) * e = 0 := by linear_combination -he - hes
  have u2 : (1 - e - s e) * s e = 0 := by linear_combination -hse - hes
  have z1 : (1 - e - s e) • X = 0 := by rw [← hX, smul_smul, u1, zero_smul]
  have z2 : (1 - e - s e) • X' = 0 := by rw [← hX', smul_smul, u1, zero_smul]
  have z3 : (1 - e - s e) • adj s J X = 0 := by rw [← a1, smul_smul, u2, zero_smul]
  have z4 : (1 - e - s e) • adj s J X' = 0 := by rw [← a2, smul_smul, u2, zero_smul]
  have z5 : X * adj s J X = 0 := by
    rw [← a1]; nth_rewrite 1 [← hX]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hes, zero_smul]
  have z6 : adj s J X' * X' = 0 := by
    rw [← a2]; nth_rewrite 2 [← hX']
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm, hes, zero_smul]
  have z7 : adj s J X' * adj s J X = s e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [adj_mul s hJ, h, adj_smul, adj_one s hJ]
  have u3 : (1 - e - s e) * (1 - e - s e) = 1 - e - s e := by linear_combination -u1 - u2
  simp only [glue, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, z1, z2, z3, z4, z5, z6, z7, h, u3]
  module

theorem cT_glue (s : A →+* A) (hs : ∀ a, s (s a) = a) {J : Matrix (Fin n) (Fin n) A}
    (hH : IsHerm s J) (hJ : IsUnit J.det) (e : A) (X X' : Matrix (Fin n) (Fin n) A) :
    cT s (glue s J e X X') * J = J * glue s J e X' X := by
  simp only [glue, cT_add, cT_smul, cT_one, Matrix.add_mul, Matrix.mul_add, cT_adj_mul s hs hH hJ,
    mul_adj s hJ, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, map_sub,
    map_one, hs]
  rw [sub_right_comm]
  abel

theorem exists_unitary_lift : ∀ (A : Type) [CommRing A] (s : A →+* A) (S : Subring A) (n : ℕ) (J : Matrix (Fin n) (Fin n) A) (Λ : Submodule S (Fin n → A)) (k : Type) [Field k] (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S), (∀ a, s (s a) = a) → (∀ a ∈ S, s a ∈ S) → Formalism.UG.IsHerm s J → IsUnit J.det → Λ.FG → Submodule.span A (Λ : Set (Fin n → A)) = ⊤ → (∀ y, y ∈ Λ ↔ ∀ y' ∈ Λ, Formalism.UG.hform s J y' y ∈ S) → ε * ε = ε → (ε : A) * s ε = 0 → r ε = 1 → Function.Surjective r → (∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε) → Function.Surjective c → (∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) → ∀ M : GL (Fin n) k, ∃ x : GL (Fin n) A, x ∈ Formalism.UG.UJ s J ∧ x ∈ Formalism.UG.stabGL Λ ∧ (∀ (y : Λ) (h : (x : Matrix (Fin n) (Fin n) A) *ᵥ (y : Fin n → A) ∈ Λ), c ⟨_, h⟩ = (M : Matrix (Fin n) (Fin n) k) *ᵥ c y) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ((x : Matrix (Fin n) (Fin n) A) - 1) *ᵥ y = ((ε : A) + s ε) • z := by
  intro A _ s S n J Λ k _ r c ε hs hS hH hJ hfg hsp hdual hε hes hrε hr hloc hc hker M
  obtain ⟨B, B', hBB', hB'B, hεB, hεB', hB', hB⟩ :=
    exists_basis S Λ r c ε hfg hsp hε hrε hr hloc hc hker
  obtain ⟨N, N', hN, hNN', hN'N⟩ := exists_lift_matrix r ε hr hloc M
  have hεA : (ε : A) * ε = ε := by exact_mod_cast congrArg Subtype.val hε
  let F : Matrix (Fin n) (Fin n) S → Matrix (Fin n) (Fin n) A := fun P => B * P.map S.subtype * B'
  have hFε : ∀ P, (ε : A) • F P = F P := fun P => by
    simp only [F, ← Matrix.mul_smul, hεB']
  have hFmul : ∀ P Q, P * Q = ε • (1 : Matrix (Fin n) (Fin n) S) →
      F P * F Q = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    intro P Q h
    have h' : P.map S.subtype * Q.map S.subtype = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
      rw [← Matrix.map_mul, h]
      ext i j
      by_cases hij : i = j <;> simp [hij]
    calc F P * F Q = B * (P.map S.subtype * (B' * B) * Q.map S.subtype) * B' := by
          simp only [F, Matrix.mul_assoc]
      _ = _ := by
          simp only [hB'B, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h', hBB', smul_smul,
            hεA]
  have hFΛ : ∀ P (y : Λ), ∃ z : Λ, F P *ᵥ (y : Fin n → A) = z ∧ c z = P.map r *ᵥ c y := by
    intro P y
    obtain ⟨a, ha, hca⟩ := hB' y
    obtain ⟨z, hz, hcz⟩ := hB (P *ᵥ a)
    refine ⟨z, ?_, ?_⟩
    · rw [← hz]
      simp only [F, ← Matrix.mulVec_mulVec, ha]
      congr 1
      ext i
      simp [Matrix.mulVec, dotProduct]
    · rw [hcz, hca]
      ext i
      simp [Matrix.mulVec, dotProduct, map_sum]
  have hFmem : ∀ P, ∀ y ∈ Λ, F P *ᵥ y ∈ Λ := fun P y hy => by
    obtain ⟨z, hz, -⟩ := hFΛ P ⟨y, hy⟩
    exact hz ▸ z.2
  have hadj : ∀ P, ∀ y ∈ Λ, adj s J (F P) *ᵥ y ∈ Λ := fun P y hy => by
    rw [hdual]
    intro y' hy'
    rw [hform_adj s hJ]
    exact (hdual y).1 hy _ (hFmem P y' hy')
  let ε' : S := ⟨s ε, hS _ ε.2⟩
  have hrε' : r ε' = 0 := by
    have : ε * ε' = 0 := Subtype.ext hes
    have := congrArg r this
    rwa [map_mul, hrε, one_mul, map_zero] at this
  have hglue : ∀ P Q y, glue s J ε (F P) (F Q) *ᵥ y =
      (1 - ε - ε') • y + F P *ᵥ y + ε' • adj s J (F Q) *ᵥ y := by
    intro P Q y
    have a1 : s ε • adj s J (F Q) = adj s J (F Q) := by rw [← adj_smul, hFε]
    rw [glue, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    nth_rewrite 1 [← a1]
    rw [Matrix.smul_mulVec]
    rfl
  have hgmem : ∀ P Q, ∀ y ∈ Λ, glue s J ε (F P) (F Q) *ᵥ y ∈ Λ := fun P Q y hy => by
    rw [hglue]
    exact Λ.add_mem (Λ.add_mem (Λ.smul_mem _ hy) (hFmem P y hy)) (Λ.smul_mem _ (hadj Q y hy))
  have g1 := glue_mul s hJ hεA hes (hFε N) (hFε N') (hFmul _ _ hNN')
  have g2 := glue_mul s hJ hεA hes (hFε N') (hFε N) (hFmul _ _ hN'N)
  refine ⟨⟨glue s J ε (F N) (F N'), glue s J ε (F N') (F N), g1, g2⟩, ?_, ?_, ?_, ?_⟩
  · change cT s (glue s J ε (F N) (F N')) * J * glue s J ε (F N) (F N') = J
    rw [cT_glue s hs hH hJ, Matrix.mul_assoc, g2, Matrix.mul_one]
  · intro y
    refine ⟨hgmem N N' y, fun hy => ?_⟩
    have := hgmem N' N _ hy
    rwa [Matrix.mulVec_mulVec, g2, Matrix.one_mulVec] at this
  · intro y h
    obtain ⟨z, hz, hcz⟩ := hFΛ N y
    have : (⟨_, h⟩ : Λ) = (1 - ε - ε') • y + z + ε' • ⟨_, hadj N' y y.2⟩ := by
      apply Subtype.ext
      change glue s J ε (F N) (F N') *ᵥ (y : Fin n → A) = _
      rw [hglue, hz]; rfl
    rw [this, map_add, map_add, map_smulₛₗ, map_smulₛₗ, hcz, hN, hrε']
    simp [hrε, hrε']
  · intro y hy
    refine ⟨-y + F N *ᵥ y + adj s J (F N') *ᵥ y,
      Λ.add_mem (Λ.add_mem (Λ.neg_mem hy) (hFmem N y hy)) (hadj N' y hy), ?_⟩
    change (glue s J ε (F N) (F N') - 1) *ᵥ y = _
    have a1 : s ε • adj s J (F N') = adj s J (F N') := by rw [← adj_smul, hFε]
    have b1 : ((ε : A) + s ε) • F N = F N := by
      rw [← hFε N, smul_smul]; congr 1; linear_combination hεA + hes
    have b2 : ((ε : A) + s ε) • adj s J (F N') = adj s J (F N') := by
      have hse : s ε * s ε = s ε := by rw [← map_mul, hεA]
      rw [← a1, smul_smul]; congr 1; linear_combination hse + hes
    rw [smul_add, smul_add, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, b1, b2, glue,
      Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    module

end GlobalTheory.SplitLift
