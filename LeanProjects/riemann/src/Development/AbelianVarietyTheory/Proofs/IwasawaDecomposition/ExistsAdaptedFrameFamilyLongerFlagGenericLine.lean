import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

namespace StepLoc

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K] {O : Subring K} {τ : ι}

abbrev blk (k : ι → ℕ) (τ : ι) (P : Mat m K) : Matrix (Rest m k τ) (Rest m k τ) K :=
  (P τ).submatrix Subtype.val Subtype.val

theorem mul_apply_rest {P : Mat m K} (hP : Par k O P) (g : Mat m K) (a : Fin (m τ)) (j : Rest m k τ) :
    (g * P) τ a j.1 = Matrix.vecMul (fun l : Rest m k τ => g τ a l.1) (blk k τ P) j := by
  rw [Pi.mul_apply, Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun l : Fin (m τ) => k τ ≤ (l : ℕ))]
  have : ∑ l : {l : Fin (m τ) // ¬ k τ ≤ (l : ℕ)}, g τ a l.1 * P τ l.1 j.1 = 0 :=
    Finset.sum_eq_zero fun l _ => by
      have h1 := l.2
      have h2 := j.2
      rw [(hP τ).2.2.2 l.1 j.1 (by omega) (by show (l.1 : ℕ) < j.1; omega), mul_zero]
  rw [this, add_zero]
  rfl

theorem blk_mul_inv {P : Mat m K} (hP : Par k O P) : blk k τ P * blk k τ P⁻¹ = 1 := by
  ext a j
  have := mul_apply_rest hP.inv P a.1 j
  rw [Mat.mul_inv hP.det_ne] at this
  refine this.symm.trans ?_
  show (1 : Matrix _ _ K) a.1 j.1 = _
  simp only [Matrix.one_apply, Subtype.ext_iff]

theorem line_iff {Q : Mat m K} (hQ : Par k O Q) (hk : k τ < m τ) {s : Rest m k τ → K} {b : K}
    (hs : ∀ j : Rest m k τ, s j = b * Q τ ⟨k τ, hk⟩ j.1) (hb : b ≠ 0) (g : Mat m K) :
    (∃ a : K, ∀ j : Rest m k τ, (g * Q) τ ⟨k τ, hk⟩ j.1 = a * s j) ↔
      ∀ j : Fin (m τ), k τ < j → g τ ⟨k τ, hk⟩ j = 0 := by
  have e : ∀ (x : K) (j : Rest m k τ), Matrix.vecMul (Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) x) (blk k τ Q) j
      = x * Q τ ⟨k τ, hk⟩ j.1 := fun x j => by
    rw [Matrix.single_vecMul]
    simp
  constructor
  · rintro ⟨a, ha⟩ j hj
    have h1 : Matrix.vecMul (fun l : Rest m k τ => g τ ⟨k τ, hk⟩ l.1) (blk k τ Q) =
        Matrix.vecMul (Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) (a * b)) (blk k τ Q) := by
      funext l
      rw [← mul_apply_rest hQ, ha, e, hs, mul_assoc]
    have h2 := congrArg (Matrix.vecMul · (blk k τ Q⁻¹)) h1
    simp only [Matrix.vecMul_vecMul, blk_mul_inv hQ, Matrix.vecMul_one] at h2
    have h3 := congrFun h2 ⟨j, hj.le⟩
    rwa [Pi.single_eq_of_ne (fun h => hj.ne' (congrArg (fun x : Rest m k τ => (x.1 : ℕ)) h))] at h3
  · intro h
    refine ⟨g τ ⟨k τ, hk⟩ ⟨k τ, hk⟩ / b, fun j => ?_⟩
    have h1 : (fun l : Rest m k τ => g τ ⟨k τ, hk⟩ l.1) =
        Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) (g τ ⟨k τ, hk⟩ ⟨k τ, hk⟩) := by
      funext l
      by_cases hl : l = ⟨⟨k τ, hk⟩, le_rfl⟩
      · rw [hl, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hl]
        exact h _ (lt_of_le_of_ne l.2 fun h' => hl (Subtype.ext (Fin.ext h'.symm)))
    rw [mul_apply_rest hQ, h1, e, hs, ← mul_assoc, div_mul_cancel₀ _ hb]

theorem par_succ_iff {k' : ι → ℕ} (hk : k τ < m τ) (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (g : Mat m K) :
    Par k' O g ↔ Par k O g ∧ ∀ j : Fin (m τ), k τ < j → g τ ⟨k τ, hk⟩ j = 0 := by
  constructor
  · intro h
    refine ⟨h.mono (fun t => ?_) le_rfl, fun j hj => (h τ).2.2.2 _ j (by rw [h1]; exact Nat.lt_succ_self _) hj⟩
    by_cases ht : t = τ
    · rw [ht, h1]; exact Nat.le_succ _
    · exact (h2 t ht).ge
  · rintro ⟨h, h'⟩ t
    refine ⟨(h t).1, (h t).2.1, (h t).2.2.1, fun i j hi hij => ?_⟩
    by_cases ht : t = τ
    · subst ht
      rw [h1] at hi
      rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi | hi
      · exact (h t).2.2.2 i j hi hij
      · obtain rfl : i = ⟨k t, hk⟩ := Fin.ext hi
        exact h' j hij
    · exact (h t).2.2.2 i j (h2 t ht ▸ hi) hij

theorem exists_completion (hk : k τ < m τ) (c : Rest m k τ → K) (i : Rest m k τ) (hi : c i = 1) :
    ∃ N : Mat m K, (∀ j : Rest m k τ, N τ ⟨k τ, hk⟩ j.1 = c j) ∧
      ∀ O : Subring K, (∀ j, c j ∈ O) → Par k O N := by
  classical
  let v : Fin (m τ) → K := fun j => if h : k τ ≤ (j : ℕ) then c ⟨j, h⟩ else 0
  have hv : ∀ j : Rest m k τ, v j.1 = c j := fun j => dif_pos j.2
  let T : Matrix (Fin (m τ)) (Fin (m τ)) K :=
    ((1 : Matrix _ _ K).updateRow i.1 v).submatrix (Equiv.swap ⟨k τ, hk⟩ i.1) id
  have hd : T.det * T.det = 1 := by
    have e : ((1 : Matrix _ _ K).updateRow i.1 v).det = 1 := by
      rw [← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
      exact (hv i).trans hi
    rw [Matrix.det_permute, e, mul_one, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  refine ⟨Function.update (1 : Mat m K) τ T, fun j => ?_, fun O hO t => ?_⟩
  · rw [Function.update_self]
    show ((1 : Matrix _ _ K).updateRow i.1 v) (Equiv.swap ⟨k τ, hk⟩ i.1 ⟨k τ, hk⟩) j.1 = _
    rw [Equiv.swap_apply_left, Matrix.updateRow_self, hv]
  by_cases ht : t = τ
  · subst ht
    rw [Function.update_self]
    have hm : ∀ a b, T a b ∈ O := fun a b => by
      show ((1 : Matrix _ _ K).updateRow i.1 v) _ b ∈ O
      rw [Matrix.updateRow_apply]
      split_ifs
      · show dite _ _ _ ∈ O
        split_ifs
        exacts [hO _, O.zero_mem]
      · rw [Matrix.one_apply]; split_ifs; exacts [O.one_mem, O.zero_mem]
    refine ⟨hm, left_ne_zero_of_mul_eq_one hd, ?_, fun a b ha hab => ?_⟩
    · rw [← eq_inv_of_mul_eq_one_left hd]; exact det_mem hm
    · have h1 : a ≠ ⟨k t, hk⟩ := fun h => ha.ne (congrArg Fin.val h)
      have h2 : a ≠ i.1 := fun h => (h ▸ ha).not_ge i.2
      show ((1 : Matrix _ _ K).updateRow i.1 v) (Equiv.swap ⟨k t, hk⟩ i.1 a) b = 0
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Matrix.updateRow_ne h2, Matrix.one_apply_ne hab.ne]
  · rw [Function.update_of_ne ht]
    exact Par.one t

end StepLoc

open StepLoc in

theorem exists_fr_stepSet (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι]
    (m k k' : ι → ℕ) (S : Fr M m k) (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ))
    (s : Rest m k τ → Ω') (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (hA₀ : A₀ ∈ S.S (genericPoint M.Z))
    (hE : ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)))
    (hP : ProjPoints M EE M' φ f s) :
    ∃ S' : Fr M' m k', ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z' := by
  refine ⟨⟨stepSet S τ hk A₀ M' φ f s, fun z' => ?_⟩, fun _ => rfl⟩
  obtain ⟨U, A, hz, hA, hU⟩ := S.loc (f z')
  have hAU : ∀ w ∈ U, A ∈ S.S w := fun w hw => (hU w hw A).2 (by rw [Mat.mul_inv hA]; exact Par.one)
  obtain ⟨hd, hE'⟩ := hE _ A (hAU _ hz)
  obtain ⟨i, hi⟩ := hP.cover z' _ hd hE'
  set c := ((dualBlock k τ A₀ A).map φ).mulVec s with hc
  let ψ : Ω →+* Ω' := φ
  obtain ⟨N, hN, hNO⟩ := exists_completion hk (fun j => c j / c i) i (div_self hi.1)
  have hAφ : ∀ t, (A.map ψ t).det ≠ 0 := fun t => by rw [Mat.det_map]; exact (map_ne_zero ψ).2 (hA t)
  have hN0 : Par k ⊤ N := hNO ⊤ fun _ => trivial
  have hP0 : Par k ⊤ ((A * A₀⁻¹).map ψ) :=
    ((Fr.mem_iff hA₀).1 (Fr.mem_genericPoint (hAU _ hz))).map ψ fun _ _ => trivial
  have hs : s = Matrix.vecMul c (blk k τ ((A * A₀⁻¹).map ψ)) := by
    have hP1 := (Fr.mem_iff hA₀).1 (Fr.mem_genericPoint (hAU _ hz))
    have e1 : (blk k τ (A * A₀⁻¹))⁻¹ * blk k τ (A * A₀⁻¹) = 1 :=
      Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse (blk_mul_inv hP1))
    have e2 : c = Matrix.vecMul s ((blk k τ (A * A₀⁻¹))⁻¹.map ψ) := by
      rw [hc, ← Matrix.mulVec_transpose]
      rfl
    have e3 : blk k τ ((A * A₀⁻¹).map ψ) = (blk k τ (A * A₀⁻¹)).map ψ := rfl
    rw [e2, e3, Matrix.vecMul_vecMul, ← Matrix.map_mul, e1, Matrix.map_one _ ψ.map_zero ψ.map_one,
      Matrix.vecMul_one]
  have hQ : ∀ j : Rest m k τ, s j = c i * (N * (A * A₀⁻¹).map ψ) τ ⟨k τ, hk⟩ j.1 := fun j => by
    have e : (fun l : Rest m k τ => N τ ⟨k τ, hk⟩ l.1) = (c i)⁻¹ • c := by
      funext l
      rw [hN, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [mul_apply_rest hP0, e, Matrix.smul_vecMul, ← hs, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hi.1]
  have hA₁ : ∀ t, ((N * A.map ψ) t).det ≠ 0 := fun t => by
    rw [Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hN0.det_ne t) (hAφ t)
  refine ⟨f ⁻¹ᵁ U ⊓ ⟨_, M'.isOpen_setOf_div c i⟩, N * A.map ψ, ⟨hz, hi⟩, hA₁, fun w hw A' => ?_⟩
  have hNw : Par k (M'.O w).toSubring N := hNO _ hw.2.2
  have hAw : A ∈ S.S (f w) := hAU _ hw.1
  rw [par_succ_iff hk h1 h2, ← line_iff (hN0.mul hP0) hk hQ hi.1]
  have e1 : A' * (N * A.map ψ)⁻¹ * (N * (A * A₀⁻¹).map ψ) = A' * (A₀.map ψ)⁻¹ := by
    rw [Mat.map_mul, Mat.map_inv, ← mul_assoc N, mul_assoc A', ← mul_assoc _ (N * A.map ψ), Mat.inv_mul hA₁,
      one_mul]
  rw [e1]
  refine and_congr_left' ⟨fun h => ?_, fun h B hB => ?_⟩
  · have := (h A hAw).mul hNw.inv
    rwa [Mat.mul_inv_rev, ← mul_assoc]
  · have h3 : Par k (M'.O w).toSubring ((A * B⁻¹).map ψ) :=
      ((Fr.mem_iff hB).1 hAw).map ψ fun _ hx => hP.hom.map_mem_O hx
    have := h.mul (hNw.mul h3)
    rw [Mat.map_mul, Mat.map_inv, ← mul_assoc N, mul_assoc A', ← mul_assoc _ (N * A.map ψ), Mat.inv_mul hA₁,
      one_mul] at this
    exact this

end GlobalTheory.FlagBundle
