import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section cpt

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cpt_zero (Bs : B.RealPlaceData k ρ Wp Wq) : KB.CptCoef Bs (fun _ => (0 : Wq →L[ℂ] Wp)) :=
  ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, ⟨0, fun _ _ h => (h rfl).elim⟩, ⟨1, one_pos, fun _ _ h => (h rfl).elim⟩⟩

theorem cpt_add_smul (Bs : B.RealPlaceData k ρ Wp Wq) {F₁ F₂ : B.Mat k ρ → (Wq →L[ℂ] Wp)} (c : ℂ)
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (F₁ + c • F₂) := by
  obtain ⟨s₁, ⟨R₁, hR₁⟩, ⟨ε₁, hε₁, hG₁⟩⟩ := h₁
  obtain ⟨s₂, ⟨R₂, hR₂⟩, ⟨ε₂, hε₂, hG₂⟩⟩ := h₂
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add s₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul c s₂), ⟨max R₁ R₂, fun g hg hne => ?_⟩,
    ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun g hg hne => ?_⟩⟩
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (hR₂ g hg this).trans (le_max_right _ _)
    · exact (hR₁ g hg h0).trans (le_max_left _ _)
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (min_le_right _ _).trans (hG₂ g hg this)
    · exact (min_le_left _ _).trans (hG₁ g hg h0)

theorem cpt_sum (Bs : B.RealPlaceData k ρ Wp Wq) {ι : Type} (S : Finset ι) (c : ι → ℂ) (F : ι → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (hF : ∀ i, KB.CptCoef Bs (F i)) : KB.CptCoef Bs (∑ i ∈ S, c i • F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact cpt_zero Bs
  | insert b t hb ih =>
    rw [Finset.sum_insert hb, add_comm]
    exact cpt_add_smul Bs (c b) ih (hF b)

theorem nice_of_cpt (Bs : B.RealPlaceData k ρ Wp Wq) {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : KB.CptCoef Bs F) :
    ∃ ε, JC.NiceCoef Bs ε F := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, -, hG⟩⟩ := h
  refine ⟨ε, hs, fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k ρ R)
    (fun g hg hgC => ?_) A m, hG⟩
  by_contra h0
  exact hgC (hR g hg h0)

theorem nice_vec_of_cpt {S : Type} [Fintype S] (Bs : B.RealPlaceData k ρ Wp Wq) {x : S → B.Mat k ρ → (Wq →L[ℂ] Wp)}
    (h : ∀ a, KB.CptCoef Bs (x a)) : ∃ ε, ∀ a, JC.NiceCoef Bs ε (x a) := by
  classical
  have hx : ∀ a, KB.CptCoef Bs (x a) := h

  choose εf hεf using fun a => (hx a).2.2
  by_cases hS : Nonempty S
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty εf, fun a => ?_⟩
    obtain ⟨ε', hε'⟩ := nice_of_cpt Bs (hx a)
    refine ⟨hε'.1, hε'.2.1, fun g hg hne => ?_⟩
    exact (Finset.inf'_le _ (Finset.mem_univ a)).trans ((hεf a).2 g hg hne)
  · refine ⟨0, fun a => (hS ⟨a⟩).elim⟩

end cpt

section shift

theorem poly_shift {E : Type} [AddCommGroup E] [Module ℂ E] (d : ℕ) (c : Fin (d + 1) → E) (δ : ℂ) :
    ∃ c' : Fin (d + 1) → E, c' (Fin.last d) = c (Fin.last d) ∧
      ∀ t : ℂ, ∑ l : Fin (d + 1), (t + δ) ^ (l : ℕ) • c l = ∑ m : Fin (d + 1), t ^ (m : ℕ) • c' m := by
  refine ⟨fun m => ∑ l : Fin (d + 1),
    (if (m : ℕ) ≤ l then (((l : ℕ).choose m : ℂ) * δ ^ ((l : ℕ) - m)) else 0) • c l, ?_, fun t => ?_⟩
  · dsimp only
    rw [Finset.sum_eq_single (Fin.last d)]
    · simp
    · intro l _ hl
      have := l.isLt
      have hl' : (l : ℕ) ≠ d := fun e => hl (Fin.ext (by simp [e]))
      rw [if_neg (by simp; omega), zero_smul]
    · simp
  · simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.sum_smul]
    congr 1
    have hl := l.isLt
    rw [Fin.sum_univ_eq_sum_range (fun m => t ^ m * if m ≤ (l : ℕ) then ((l : ℕ).choose m : ℂ) * δ ^ ((l : ℕ) - m) else 0)
      (d + 1)]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (d + 1)) (fun m => m ≤ (l : ℕ))]
    have h1 : (Finset.range (d + 1)).filter (fun m => m ≤ (l : ℕ)) = Finset.range ((l : ℕ) + 1) := by
      ext m; simp; omega
    rw [h1, Finset.sum_eq_zero (s := (Finset.range (d + 1)).filter (fun m => ¬ m ≤ (l : ℕ)))
      (fun m hm => by simp at hm; rw [if_neg (by omega), mul_zero]), add_zero, add_pow]
    apply Finset.sum_congr rfl
    intro m hm
    simp at hm
    rw [if_pos (by omega)]
    ring

end shift

section vand

theorem vand_ident {n : ℕ} (τ : Fin n → ℂ) (hτ : Function.Injective τ) (t : ℂ) (m : Fin n) :
    ∑ i : Fin n, (∑ l : Fin n, t ^ (l : ℕ) * (Matrix.vandermonde τ)⁻¹ l i) * τ i ^ (m : ℕ) = t ^ (m : ℕ) := by
  have hdet : (Matrix.vandermonde τ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hτ
  have hinv : (Matrix.vandermonde τ)⁻¹ * Matrix.vandermonde τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  calc ∑ i : Fin n, (∑ l : Fin n, t ^ (l : ℕ) * (Matrix.vandermonde τ)⁻¹ l i) * τ i ^ (m : ℕ)
      = ∑ l : Fin n, t ^ (l : ℕ) * ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i * Matrix.vandermonde τ i m := by
        simp only [Finset.sum_mul, Finset.mul_sum, Matrix.vandermonde_apply]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro i _; ring
    _ = ∑ l : Fin n, t ^ (l : ℕ) * (1 : Matrix (Fin n) (Fin n) ℂ) l m := by
        apply Finset.sum_congr rfl; intro l _; rw [← Matrix.mul_apply, hinv]
    _ = t ^ (m : ℕ) := by
        simp [Matrix.one_apply]

theorem vand_row {n : ℕ} (τ : Fin n → ℂ) (hτ : Function.Injective τ) (l m : Fin n) :
    ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i * τ i ^ (m : ℕ) = if l = m then 1 else 0 := by
  have hdet : (Matrix.vandermonde τ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hτ
  have hinv : (Matrix.vandermonde τ)⁻¹ * Matrix.vandermonde τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have := congrFun (congrFun hinv l) m
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [Matrix.vandermonde_apply] using this

end vand

section slicepoly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem sliceAt_zero (z z' : Fin (2 * r + k + 1) → ℂ) (p : C.LPt) :
    D.sliceAt k r z z' (fun _ => (0 : Wq →L[ℂ] Wp)) p = fun _ => 0 := by
  funext γ
  unfold D.sliceAt
  split_ifs
  · simp [U.PhiFun, D.castF]
  · rfl

theorem slicePoly_of_pt (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef T.base F)
    (j : ℕ) (hj : j ≤ r) (hj1 : 1 ≤ j) (h : C.LPt) (hh : D.IsLocPt h j) (w' : List C.Letter) (b : Bool) (δ : ℝ)
    (e : Fin 2)
    (hpt : ∀ (a : Wd.Ix (Fin w'.length)), ∀ g ∈ B.GV k r, Dmin k r T.base.z T.base.z' g ⟨j, by omega⟩ ≠ 0 →
      ∃ c : Fin (j + 1) → (Wq →L[ℂ] Wp), c (Fin.last j) = (if e = 0 then D.uwG k r T.base.z T.base.z' F j hj w' a g else 0) ∧
        ∀ t : ℝ, D.uwG k r T.base.z T.base.z' F j hj ((b, t + δ) :: w') (Fin.cons e a) g = ∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • c l) :
    ∃ Cf : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp),
      Cf (Fin.last j) = (if e = 0 then KB.slv T F j hj w' h hh.2 else 0) ∧
      (∀ l, ∃ ε, ∀ a, JC.NiceCoef (T.bs j) ε (Cf l a)) ∧
      ∀ t : ℝ, EqGV (fun a => KB.slv T F j hj ((b, t + δ) :: w') h hh.2 (Fin.cons e a))
        (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • Cf l) := by
  classical
  set τ : Fin (j + 1) → ℂ := fun i => (((i : ℕ) : ℝ) : ℂ) with hτdef
  have hτ : Function.Injective τ := by
    intro a b' hab
    simp only [hτdef, Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  set Vi := (Matrix.vandermonde τ)⁻¹ with hVi
  set Vt : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) :=
    fun i a => KB.slv T F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') h hh.2 (Fin.cons e a) with hVt
  set top : Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) :=
    if e = 0 then KB.slv T F j hj w' h hh.2 else 0 with htop
  refine ⟨fun l => if l = Fin.last j then top else ∑ i, Vi l i • Vt i, if_pos rfl, ?_, ?_⟩
  ·
    have hc : ∀ (i : ℕ) (hi : i ≤ r) (hi1 : 1 ≤ i) (w : List C.Letter) (hp : D.IsLocPt h i) (a : Wd.Ix (Fin w.length)),
        KB.CptCoef (T.bs i) (KB.slv T F i hi w h hp.2 a) := fun i hi hi1 w hp a =>
      Formalism.FourierDecayAlt.P.PBE.slice_pos_cpt k r Wp Wq T F hF i hi hi1 w h (by rw [hp.2]) hp a
    intro l
    by_cases hl : l = Fin.last j
    · by_cases he : e = 0
      · simp only [hl, if_pos rfl, htop, he, if_true]
        exact nice_vec_of_cpt (T.bs j) (fun a => hc j hj hj1 w' hh a)
      · simp only [hl, if_pos rfl, htop, he, if_false]
        exact ⟨0, fun a => Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero⟩
    · simp only [hl, if_false]
      refine nice_vec_of_cpt (T.bs j) (fun a => ?_)
      have e1 : (∑ i, Vi l i • Vt i) a = ∑ i, Vi l i • Vt i a := by simp [Finset.sum_apply]
      rw [e1]
      exact cpt_sum (T.bs j) _ _ _ (fun i => hc j hj hj1 _ hh _)
  ·
    intro t a γ hγ
    have hcast : r - j = r - D.ptSize h := by rw [hh.2]
    have hγ' : D.castM hcast γ ∈ B.GV k (r - D.ptSize h) := Formalism.FourierDecayAlt.P.PBE.castM_GV hcast hγ

    have hL := sliceAt_lincomb k r Wp Wq T F hF j hj hj1 h hh Finset.univ
      (fun i => ∑ l : Fin (j + 1), (t : ℂ) ^ (l : ℕ) * Vi l i) (fun i => (b, ((i : ℕ) : ℝ) + δ) :: w')
      (fun _ => Fin.cons e a) (D.uwG k r T.base.z T.base.z' F j hj ((b, t + δ) :: w') (Fin.cons e a)) (by
        intro g hg hD
        obtain ⟨c, -, hc⟩ := hpt a g hg hD
        rw [hc t]
        simp only [hc]
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m _
        rw [← Finset.sum_smul]
        congr 1
        have := vand_ident τ hτ (t : ℂ) m
        simp only [hτdef] at this
        rw [← this]) (D.castM hcast γ) hγ'

    have hT := sliceAt_lincomb k r Wp Wq T F hF j hj hj1 h hh Finset.univ
      (fun i => Vi (Fin.last j) i) (fun i => (b, ((i : ℕ) : ℝ) + δ) :: w')
      (fun _ => Fin.cons e a) (if e = 0 then D.uwG k r T.base.z T.base.z' F j hj w' a else fun _ => 0) (by
        intro g hg hD
        obtain ⟨c, hcl, hc⟩ := hpt a g hg hD
        simp only [hc]
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have : ∀ m : Fin (j + 1), ∑ i : Fin (j + 1), (Vi (Fin.last j) i * ((((i : ℕ) : ℝ) : ℂ)) ^ (m : ℕ)) • c m =
            (if Fin.last j = m then (1 : ℂ) else 0) • c m := by
          intro m
          rw [← Finset.sum_smul]
          congr 1
          have := vand_row τ hτ (Fin.last j) m
          simp only [hτdef] at this
          rw [← this]
        simp only [this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [hcl]
        split_ifs <;> simp) (D.castM hcast γ) hγ'

    show D.castF _ (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' F j hj ((b, t + δ) :: w') (Fin.cons e a)) h) γ = _
    simp only [D.castF]
    rw [hL]
    simp only [Finset.sum_apply, Pi.smul_apply]
    have hR : ∀ x : Fin (j + 1), (if x = Fin.last j then top else ∑ i, Vi x i • Vt i) a γ =
        ∑ q, Vi x q • D.sliceAt k r T.base.z T.base.z'
          (D.uwG k r T.base.z T.base.z' F j hj ((b, ((q : ℕ) : ℝ) + δ) :: w') (Fin.cons e a)) h (D.castM hcast γ) := by
      intro x
      by_cases hx : x = Fin.last j
      · rw [if_pos hx, hx, ← hT]
        simp only [htop]
        by_cases he : e = 0
        · simp only [he, if_true, KB.slv, D.castF]
        · simp only [he, if_false, sliceAt_zero, Pi.zero_apply]
      · rw [if_neg hx]
        simp only [Finset.sum_apply, Pi.smul_apply, hVt, KB.slv, D.castF]
    simp only [hR, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

end slicepoly

end Formalism.FourierDecayAlt.P.PBG
