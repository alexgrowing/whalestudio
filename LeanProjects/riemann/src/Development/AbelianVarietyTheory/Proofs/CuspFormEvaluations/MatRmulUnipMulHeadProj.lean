import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivVanishesOfTranslationInvariance
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.BetaEqZeroOfCharacter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat

open NumberField Matrix Complex
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (thetaChar omegaStd)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory.LagSplit

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {g : ℕ}

def coper (y : Frame X.Ψ r) (v : Fin r → E) : X.Ψ × Fin r → ℂ := fun p =>
  if (p.2 : ℕ) < X.p0 then X.c p.1 * ((mat y p.1)⁻¹ *ᵥ Data.emb p.1.1 v) p.2
  else -(X.c p.1 * hermC p.1.1 X.Gm (FD.col (mat y p.1) p.2) (Data.emb p.1.1 v))

theorem coper_of_lt (y : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) {a : Fin r} (h : (a : ℕ) < X.p0) :
    coper X y v (τ, a) = X.c τ * ((mat y τ)⁻¹ *ᵥ Data.emb τ.1 v) a := if_pos h

theorem coper_of_le (y : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) {a : Fin r} (h : X.p0 ≤ (a : ℕ)) :
    coper X y v (τ, a) = -(X.c τ * hermC τ.1 X.Gm (FD.col (mat y τ) a) (Data.emb τ.1 v)) :=
  if_neg (not_lt.2 h)

theorem coper_add (y : Frame X.Ψ r) (u v : Fin r → E) :
    coper X y (u + v) = coper X y u + coper X y v := by
  funext p
  have h : Data.emb p.1.1 (u + v) = Data.emb p.1.1 u + Data.emb p.1.1 v := by
    funext a; simp [Data.emb]
  simp only [coper, Pi.add_apply, h]
  split_ifs
  · rw [mulVec_add, Pi.add_apply, mul_add]
  · simp [hermC, mul_add, Finset.sum_add_distrib, add_comm]

theorem coper_smul (y : Frame X.Ψ r) (α : E) (v : Fin r → E) (p : X.Ψ × Fin r) :
    coper X y (α • v) p = conj (rowType X p α) * coper X y v p := by
  have h : Data.emb p.1.1 (α • v) = p.1.1 α • Data.emb p.1.1 v := by
    funext a; simp [Data.emb]
  simp only [coper, rowType, h]
  split_ifs
  · rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, ComplexEmbedding.conjugate_coe_eq, conj_conj]
    ring
  · simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_neg, neg_inj]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def coperHom (y : Frame X.Ψ r) : (Fin r → E) →+ (X.Ψ × Fin r → ℂ) :=
  AddMonoidHom.mk' (coper X y) (coper_add X y)

theorem hermC_eq_sum_col (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.det ≠ 0) (u v : Fin r → ℂ) :
    hermC τ G u v = ∑ a, (A⁻¹ *ᵥ u) a * hermC τ G (FD.col A a) v := by
  have hu : u = A *ᵥ (A⁻¹ *ᵥ u) := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hA.isUnit, one_mulVec]
  generalize A⁻¹ *ᵥ u = w at hu
  simp only [hu, hermC, FD.col, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

variable {X} in

theorem EF_eq_coper {y : Frame X.Ψ r} (hy : ∀ τ, (mat y τ).det ≠ 0) (u v : Fin r → E) :
    ((EF X u v : ℚ) : ℂ) = I / 2 * (coper X y u ⬝ᵥ per X y v - per X y u ⬝ᵥ coper X y v) := by
  have h := congrArg (fun t : ℝ => (t : ℂ)) (EF_eq_sum X u v)
  simp only [ofReal_ratCast, ofReal_sum] at h
  rw [h, dotProduct, dotProduct, ← Finset.sum_sub_distrib, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h1 : ∑ a, (coper X y u (τ, a) * per X y v (τ, a) - per X y u (τ, a) * coper X y v (τ, a)) =
      X.c τ * (hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v) -
        hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 u)) := by
    rw [hermC_eq_sum_col _ _ (hy τ), hermC_eq_sum_col _ _ (hy τ) (Data.emb τ.1 v),
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [coper, per]
    split_ifs <;> ring
  rw [h1, ← hermC_conj τ.1 X.Gm_herm (Data.emb τ.1 u), sub_conj]
  push_cast
  linear_combination
    (X.c τ * ((hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v)).im : ℂ)) * -I_mul_I

section Cx

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

def cxMat (f : (Fin r → E) → X.Ψ × Fin r → ℂ) : Matrix (Fin g) (Fin g ⊕ Fin g) ℂ :=
  Matrix.of fun i s => f (bas (Pi.single s 1)) (idx i)

def actMat (α : 𝓞 E) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ :=
  Matrix.of fun s t => (bas.symm (α • bas (Pi.single t 1)) s : ℂ)

theorem cxMat_mulVec_int (f : (Fin r → E) →+ (X.Ψ × Fin r → ℂ)) (m : Fin g ⊕ Fin g → ℤ) :
    cxMat X bas idx f *ᵥ (fun s => (m s : ℂ)) = f (bas m) ∘ idx := by
  have hm : m = ∑ j, m j • Pi.single j (1 : ℤ) := by
    funext j; simp [Pi.single_apply]
  funext i
  conv_rhs => rw [hm, map_sum, AddSubmonoidClass.coe_finset_sum, map_sum]
  simp only [map_zsmul, AddSubgroupClass.coe_zsmul]
  simp [cxMat, mulVec, dotProduct, mul_comm]

theorem actMat_mulVec_star (α : 𝓞 E) (u : Fin g ⊕ Fin g → ℂ) :
    actMat X bas α *ᵥ star u = star (actMat X bas α *ᵥ u) := by
  funext i; simp [actMat, mulVec, dotProduct]

theorem cxMat_mul_actMat (f : (Fin r → E) →+ (X.Ψ × Fin r → ℂ)) (α : 𝓞 E) (χ : X.Ψ × Fin r → ℂ)
    (hf : ∀ v p, f ((α : E) • v) p = χ p * f v p) :
    cxMat X bas idx f * actMat X bas α = diagonal (fun i => χ (idx i)) * cxMat X bas idx f := by
  ext i t
  have h := congrFun (cxMat_mulVec_int X bas idx f (bas.symm (α • bas (Pi.single t 1)))) i
  rw [LinearEquiv.apply_symm_apply] at h
  rw [diagonal_mul]
  exact h.trans (hf _ _)

def perCx (y : Frame X.Ψ r) : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  (cxMat X bas idx (per X y)).mulVecLin

def coperCx (y : Frame X.Ψ r) : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  (cxMat X bas idx (coper X y)).mulVecLin

def coMat (s : Fin g → Fin g ⊕ Fin g) (y : Frame X.Ψ r) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i k => coper X y (bas (Pi.single (s k) 1)) (idx i)

theorem perCx_int (y : Frame X.Ψ r) (m : Fin g ⊕ Fin g → ℤ) :
    perCx X bas idx y (fun s => (m s : ℂ)) = per X y (bas m) ∘ idx :=
  cxMat_mulVec_int X bas idx (perLin X y).toAddMonoidHom m

theorem coperCx_int (y : Frame X.Ψ r) (m : Fin g ⊕ Fin g → ℤ) :
    coperCx X bas idx y (fun s => (m s : ℂ)) = coper X y (bas m) ∘ idx :=
  cxMat_mulVec_int X bas idx (coperHom X y) m

theorem perCx_apply (y : Frame X.Ψ r) (u : Fin g ⊕ Fin g → ℂ) :
    perCx X bas idx y u = perMat X bas idx Sum.inl y *ᵥ (u ∘ Sum.inl) +
      perMat X bas idx Sum.inr y *ᵥ (u ∘ Sum.inr) := by
  funext i; simp [perCx, cxMat, mulVec, dotProduct]

theorem coperCx_apply (y : Frame X.Ψ r) (u : Fin g ⊕ Fin g → ℂ) :
    coperCx X bas idx y u = coMat X bas idx Sum.inl y *ᵥ (u ∘ Sum.inl) +
      coMat X bas idx Sum.inr y *ᵥ (u ∘ Sum.inr) := by
  funext i; simp [coperCx, cxMat, coMat, mulVec, dotProduct]

theorem perCx_actMat (y : Frame X.Ψ r) (α : 𝓞 E) (u : Fin g ⊕ Fin g → ℂ) :
    perCx X bas idx y (actMat X bas α *ᵥ u) =
      diagonal (fun i => rowType X (idx i) α) *ᵥ perCx X bas idx y u := by
  simp only [perCx, mulVecLin_apply, mulVec_mulVec]
  exact congrArg (· *ᵥ u) (cxMat_mul_actMat X bas idx (perLin X y).toAddMonoidHom α
    (fun p => rowType X p α) (per_smul X y α))

theorem coperCx_actMat (y : Frame X.Ψ r) (α : 𝓞 E) (u : Fin g ⊕ Fin g → ℂ) :
    coperCx X bas idx y (actMat X bas α *ᵥ u) =
      diagonal (fun i => conj (rowType X (idx i) α)) *ᵥ coperCx X bas idx y u := by
  simp only [coperCx, mulVecLin_apply, mulVec_mulVec]
  exact congrArg (· *ᵥ u) (cxMat_mul_actMat X bas idx (coperHom X y) α
    (fun p => conj (rowType X p α)) (coper_smul X y α))

def secN (y : Frame X.Ψ r) : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ) :=
  (I / 2) • (fromRows (coMat X bas idx Sum.inr y)ᵀ (-(coMat X bas idx Sum.inl y)ᵀ)).mulVecLin

def secLin (y : Frame X.Ψ r) : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ) :=
  secL g ∘ₗ (hMat X bas idx y).mulVecLin

def splitMat (y : Frame X.Ψ r) : Matrix (Fin g) (Fin g) ℂ :=
  coMat X bas idx Sum.inl y * hMat X bas idx y

theorem coperCx_secLin (y : Frame X.Ψ r) (w : Fin g → ℂ) :
    coperCx X bas idx y (secLin X bas idx y w) = splitMat X bas idx y *ᵥ w := by
  simp [coperCx_apply, secLin, secL_apply, splitMat]

variable {X bas} (hs : IsSympl X bas)
include hs

theorem omegaCx_eq_coper {y : Frame X.Ψ r} (hy : ∀ τ, (mat y τ).det ≠ 0)
    (u v : Fin g ⊕ Fin g → ℂ) :
    omegaCx g u v = I / 2 * (perCx X bas idx y u ⬝ᵥ coperCx X bas idx y v -
      coperCx X bas idx y u ⬝ᵥ perCx X bas idx y v) := by
  let D : LinearMap.BilinForm ℂ (Fin g → ℂ) := dotProductBilin ℂ ℂ
  have h := eq_omegaCx_of_intCast ((I / 2) • (D.compl₁₂ (perCx X bas idx y) (coperCx X bas idx y) -
    D.compl₁₂ (coperCx X bas idx y) (perCx X bas idx y))) fun a b => by
      have h1 := EF_eq_coper hy (bas a) (bas b)
      rw [hs] at h1
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.compl₁₂_apply, perCx_int,
        coperCx_int, D, dotProductBilin_apply_apply, smul_eq_mul, comp_equiv_dotProduct_comp_equiv]
      push_cast at h1
      linear_combination h1
  rw [← h]; rfl

end Cx

section Balanced

variable (idx : Fin g ≃ X.Ψ × Fin r)

def IsBalanced (M : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∀ i j, M i j ≠ 0 → (idx i).1 = (idx j).1 ∧ (((idx i).2 : ℕ) < X.p0 ↔ X.p0 ≤ ((idx j).2 : ℕ))

theorem eq_and_iff_of_rowType {p q : X.Ψ × Fin r}
    (h : ∀ α : 𝓞 E, rowType X p α = conj (rowType X q α)) :
    p.1 = q.1 ∧ ((p.2 : ℕ) < X.p0 ↔ X.p0 ≤ (q.2 : ℕ)) := by
  have h1 : rowType X p = ComplexEmbedding.conjugate (rowType X q) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)
  have hp := (X.cmType _).1 p.1.2
  have hq := (X.cmType _).1 q.1.2
  have hinv := ComplexEmbedding.involutive_conjugate E
  unfold rowType at h1
  split_ifs at h1 with a b b
  · rw [hinv] at h1
    exact absurd (h1 ▸ q.1.2) hp
  · exact ⟨Subtype.ext (hinv.injective h1), by omega⟩
  · exact ⟨Subtype.ext (h1.trans (hinv _)), by omega⟩
  · exact absurd (h1 ▸ p.1.2) hq

variable {X} {q0 : ℕ} (hr : X.p0 + q0 = r)

theorem sum_letterDir_apply {n : ℕ} (z : Harm.Var X.Ψ q0 X.p0 (Fin n) → ℂ) (t : X.Ψ)
    (ρ : Fin q0 ⊕ Fin X.p0) (k : Fin n) :
    (∑ l, z l • letterDir X hr idx l) k (idx.symm (rowOf X hr (t, ρ))) = z (t, ρ, k) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (t, ρ, k)]
  · simp [letterDir, -rowOf_apply]
  · rintro ⟨t', ρ', k'⟩ _ hne
    by_cases hk : k = k'
    · subst hk
      have : (t, ρ) ≠ (t', ρ') := fun h => hne (by rw [Prod.mk.injEq] at h; rw [h.1, h.2])
      simp [letterDir, -rowOf_apply, -Prod.mk.injEq, this]
    · simp [letterDir, hk]
  · simp

variable {idx}

theorem IsBalanced.dot_mulVec {M : Matrix (Fin g) (Fin g) ℂ} (hM : IsBalanced X idx M)
    (w : Fin g → ℂ) :
    w ⬝ᵥ M *ᵥ w = ∑ t, ∑ a, ∑ b,
      (M (idx.symm (rowOf X hr (t, .inl a))) (idx.symm (rowOf X hr (t, .inr b))) +
        M (idx.symm (rowOf X hr (t, .inr b))) (idx.symm (rowOf X hr (t, .inl a)))) *
      w (idx.symm (rowOf X hr (t, .inl a))) * w (idx.symm (rowOf X hr (t, .inr b))) := by
  let e := (rowOf X hr).trans idx.symm
  have h0 (t t' : X.Ψ) (ρ ρ' : Fin q0 ⊕ Fin X.p0) (h : M (e (t, ρ)) (e (t', ρ')) ≠ 0) :
      t = t' ∧ ((rowIdx hr ρ : ℕ) < X.p0 ↔ X.p0 ≤ (rowIdx hr ρ' : ℕ)) := by
    simpa [e] using hM _ _ h
  have h1 (t a b) : M (e (t, .inl a)) (e (t, .inl b)) = 0 := by
    by_contra h
    have := (h0 _ _ _ _ h).2
    simp only [rowIdx_inl] at this
    omega
  have h2 (t a b) : M (e (t, .inr a)) (e (t, .inr b)) = 0 := by
    by_contra h
    have := (h0 _ _ _ _ h).2
    have ha := a.isLt
    simp only [rowIdx_inr] at this
    omega
  change _ = ∑ t, ∑ a, ∑ b, (M (e (t, .inl a)) (e (t, .inr b)) + M (e (t, .inr b)) (e (t, .inl a))) *
    w (e (t, .inl a)) * w (e (t, .inr b))
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h3 (ρ) : ∑ j, w (e (t, ρ)) * (M (e (t, ρ)) j * w j) =
      ∑ ρ', w (e (t, ρ)) * (M (e (t, ρ)) (e (t, ρ')) * w (e (t, ρ'))) := by
    rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single t]
    · intro t' _ ht
      refine Finset.sum_eq_zero fun ρ' _ => ?_
      rw [not_not.1 (mt (h0 _ _ _ _) fun h => ht h.1.symm), zero_mul, mul_zero]
    · simp
  simp only [h3, Fintype.sum_sum_type, h1, h2, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
    add_zero, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin X.p0))), add_comm]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem IsBalanced.polyDeriv_exp_mul {M : Matrix (Fin g) (Fin g) ℂ} (hM : IsBalanced X idx M)
    {n : ℕ} {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} (hP : Harm.IsHarmonic P) (c : ℂ)
    {G : (Fin n → Fin g → ℂ) → ℂ} (hG : AnalyticAt ℂ G 0) :
    polyDeriv P (letterDir X hr idx) (fun z => cexp (∑ k, c * (z k ⬝ᵥ M *ᵥ z k)) * G z) 0 =
      polyDeriv P (letterDir X hr idx) G 0 := by
  refine GaussGauge.polyDeriv_exp_balanced_mul_dir hP (fun t a b => c *
    (M (idx.symm (rowOf X hr (t, .inl a))) (idx.symm (rowOf X hr (t, .inr b))) +
      M (idx.symm (rowOf X hr (t, .inr b))) (idx.symm (rowOf X hr (t, .inl a)))))
    (letterDir X hr idx) (B := fun z : Fin n → Fin g → ℂ => ∑ k, c * (z k ⬝ᵥ M *ᵥ z k)) (G := G)
    ?_ (fun z => ?_) hG
  · refine SCV.analyticAt_of_differentiableOn (s := Set.univ) ?_ Filter.univ_mem
    simp only [dotProduct, mulVec]
    fun_prop
  · simp only [hM.dot_mulVec hr, sum_letterDir_apply, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

end Balanced

section Split

variable {X} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
  (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
include hs hx

theorem hMat_mulVec_perCx (u : Fin g ⊕ Fin g → ℂ) :
    hMat X bas idx x *ᵥ perCx X bas idx x u = perProj (tauMat X bas idx x) u := by
  rw [perCx_apply, mulVec_add, mulVec_mulVec, mulVec_mulVec, hMat_mul_perMat idx hs hx, one_mulVec,
    perProj_apply, tauMat]

theorem perCx_eq_perProj (u : Fin g ⊕ Fin g → ℂ) :
    perCx X bas idx x u = perMat X bas idx Sum.inl x *ᵥ perProj (tauMat X bas idx x) u := by
  rw [← hMat_mulVec_perCx idx hs hx, mulVec_mulVec, mul_eq_one_comm.1 (hMat_mul_perMat idx hs hx),
    one_mulVec]

theorem secLin_isLagSection :
    IsLagSection (omegaCx g) (perCx X bas idx x) (secLin X bas idx x) := by
  refine ⟨fun z => ?_, fun z w => (secL_isLagSection 0).2 _ _⟩
  rw [perCx_eq_perProj idx hs hx, secLin, LinearMap.comp_apply, (secL_isLagSection _).1,
    mulVecLin_apply, mulVec_mulVec, mul_eq_one_comm.1 (hMat_mul_perMat idx hs hx), one_mulVec]

theorem splitMat_isSymm : (splitMat X bas idx x).IsSymm := by
  have hL := secLin_isLagSection idx hs hx
  ext i j
  have h := omegaCx_eq_coper idx hs (fun τ => (hx τ).1) (secLin X bas idx x (Pi.single i 1))
    (secLin X bas idx x (Pi.single j 1))
  rw [hL.2, hL.1, hL.1, coperCx_secLin, coperCx_secLin] at h
  have h' : splitMat X bas idx x i j = splitMat X bas idx x j i := by simpa [sub_eq_zero] using h.symm
  exact h'.symm

theorem splitMat_mulVec_per (m : Fin g → ℤ) :
    splitMat X bas idx x *ᵥ (per X x (bas (Sum.elim m 0)) ∘ idx) =
      coper X x (bas (Sum.elim m 0)) ∘ idx := by
  rw [← coperCx_secLin, ← coperCx_int, secLin, LinearMap.comp_apply, mulVecLin_apply,
    hMat_mulVec_per_bas idx hs hx, secL_apply]
  congr 1
  funext s
  rcases s with s | s <;> simp [mulVec]

theorem dot_imInv_sub_splitMat (z w : Fin g → ℂ) :
    z ⬝ᵥ ((hMat X bas idx x)ᵀ * imInv X bas idx x * hMat X bas idx x - splitMat X bas idx x) *ᵥ w =
      -(coperCx X bas idx x (secH (tauMat X bas idx x) (hMat X bas idx x *ᵥ z)) ⬝ᵥ w) := by
  have hY := (tauMat_im_posDef idx hs hx).det_pos.ne'.isUnit
  have h1 := beta_secH_secL (tauMat_isSymm idx hs hx) hY (hMat X bas idx x *ᵥ z)
    (hMat X bas idx x *ᵥ w)
  have h2 := omegaCx_eq_coper idx hs (fun τ => (hx τ).1)
    (secH (tauMat X bas idx x) (hMat X bas idx x *ᵥ z)) (secLin X bas idx x w)
  rw [(secLin_isLagSection idx hs hx).1, coperCx_secLin, perCx_eq_perProj idx hs hx, perProj_secH hY,
    mulVec_mulVec, mul_eq_one_comm.1 (hMat_mul_perMat idx hs hx), one_mulVec] at h2
  have h3 := h1.symm.trans h2
  have h4 : -(2 * I)⁻¹ = I / 2 := by rw [mul_inv, inv_I]; ring
  rw [h4] at h3
  have h5 := mul_left_cancel₀ (show I / 2 ≠ 0 by simp) h3
  rw [sub_mulVec, dotProduct_sub, Matrix.mul_assoc, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose, ← mulVec_mulVec, imInv, h5]
  ring

theorem isBalanced_sub_splitMat : IsBalanced X idx
    ((hMat X bas idx x)ᵀ * imInv X bas idx x * hMat X bas idx x - splitMat X bas idx x) := by
  have hY := (tauMat_im_posDef idx hs hx).det_pos.ne'.isUnit
  have hA := mul_eq_one_comm.1 (hMat_mul_perMat idx hs hx)
  intro i j hij
  refine eq_and_iff_of_rowType X fun α => mul_right_cancel₀ hij ?_
  set D : Matrix (Fin g) (Fin g) ℂ := diagonal fun i => rowType X (idx i) α with hD
  have he (z : Fin g → ℂ) := secH_equivariant hY (actMat X bas α *ᵥ ·)
    (fun z => hMat X bas idx x *ᵥ (D *ᵥ (perMat X bas idx Sum.inl x *ᵥ z))) (by simp)
    (actMat_mulVec_star X bas α)
    (fun u => by rw [← perCx_eq_perProj idx hs hx, ← perCx_actMat, hMat_mulVec_perCx idx hs hx])
    (hMat X bas idx x *ᵥ z)
  have h1 := dot_imInv_sub_splitMat idx hs hx (D *ᵥ Pi.single i 1) (Pi.single j 1)
  have h2 := dot_imInv_sub_splitMat idx hs hx (Pi.single i 1) (Pi.single j 1)
  have h3 := he (Pi.single i 1)
  rw [mulVec_mulVec _ _ (hMat X bas idx x), hA, one_mulVec] at h3
  rw [h3, coperCx_actMat, hD, diagonal_mulVec_single] at h1
  simp only [single_dotProduct, dotProduct_single, mul_one, one_mul, mulVec_single_one, col_apply,
    mulVec_diagonal] at h1 h2
  rw [h1, h2, mul_neg]

theorem thFr_eq_splitMat {q0 : ℕ} (hr : X.p0 + q0 = r) (n : ℕ) (a b : Fin n → Fin g → ℝ)
    {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} (hP : Harm.IsHarmonic P) :
    thFr X hr bas idx n a b P x = (hMat X bas idx x).det ^ (n / 2) *
      polyDeriv P (letterDir X hr idx) (fun z => ∏ k,
        cexp (Real.pi / 2 * (z k ⬝ᵥ splitMat X bas idx x *ᵥ z k)) *
          thetaChar (tauMat X bas idx x) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ))
            (hMat X bas idx x *ᵥ z k)) 0 := by
  refine congrArg _ (Eq.trans ?_
    ((isBalanced_sub_splitMat idx hs hx).polyDeriv_exp_mul hr hP (Real.pi / 2) ?_))
  · congr 1
    funext z
    rw [Complex.exp_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [canFn, ← mul_assoc, ← Complex.exp_add, sub_mulVec, dotProduct_sub, Matrix.mul_assoc,
      ← mulVec_mulVec, dotProduct_mulVec (z k) _ᵀ, vecMul_transpose, ← mulVec_mulVec]
    congr 2
    ring
  · refine SCV.analyticAt_of_differentiableOn (s := Set.univ) ?_ Filter.univ_mem
    refine CanTh.differentiableOn_prod_fun _ fun k _ => DifferentiableOn.mul ?_ ?_
    · simp only [dotProduct, mulVec]
      fun_prop
    · refine (CanTh.differentiable_thetaChar (CanTh.mem_thetaDomain (tauMat_im_posDef idx hs hx))
        _ _).comp_differentiableOn (differentiableOn_pi.2 fun i => ?_)
      simp only [dotProduct, mulVec]
      fun_prop

end Split

section Holo

theorem differentiableOn_coper (v : Fin r → E) (p : X.Ψ × Fin r) :
    DifferentiableOn ℂ (fun y => coper X y v p) {y | ∀ τ, (mat y τ).det ≠ 0} := by
  have hent : ∀ τ a c, Differentiable ℂ fun x : Frame X.Ψ r => mat x τ a c := by
    intro τ a c
    show Differentiable ℂ fun x : Frame X.Ψ r => x τ a c
    fun_prop
  simp only [coper]
  split_ifs
  · refine DifferentiableOn.const_mul ?_ _
    simp only [mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun c _ => (RiemannRel.differentiableOn_left_inverse
      (fun y : Frame X.Ψ r => mat y p.1) _ (fun _ _ => (hent _ _ _).differentiableOn)
      (fun y hy => nonsing_inv_mul _ (hy p.1).isUnit) _ _).mul_const _
  · refine (Differentiable.differentiableOn (Differentiable.const_mul ?_ _)).neg
    unfold hermC FD.col
    refine Differentiable.fun_sum fun a _ => Differentiable.fun_sum fun c _ => ?_
    exact ((hent _ _ _).mul_const _).mul_const _

variable {X} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
  (hs : IsSympl X bas)
include hs

theorem differentiableOn_splitMat (i j : Fin g) :
    DifferentiableOn ℂ (fun x => splitMat X bas idx x i j) X.dom := by
  simp only [splitMat, mul_apply]
  exact DifferentiableOn.fun_sum fun l _ =>
    ((differentiableOn_coper X _ _).mono fun x hx τ => (hx τ).1).mul (differentiableOn_hMat idx hs l j)

theorem differentiableOn_thFr {q0 : ℕ} (hr : X.p0 + q0 = r) (n : ℕ) (a b : Fin n → Fin g → ℝ)
    {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} (hP : Harm.IsHarmonic P) :
    DifferentiableOn ℂ (thFr X hr bas idx n a b P) X.dom := by
  refine DifferentiableOn.congr ?_ fun x hx => thFr_eq_splitMat idx hs hx hr n a b hP
  refine ((differentiableOn_det_hMat idx hs).pow _).mul ?_
  have hl {f : Frame X.Ψ r → ℂ} (hf : DifferentiableOn ℂ f X.dom) : DifferentiableOn ℂ
      (fun p : Frame X.Ψ r × (Fin n → Fin g → ℂ) => f p.1) (X.dom ×ˢ Set.univ) :=
    hf.comp differentiableOn_fst fun _ hp => hp.1
  have hz (k i) : DifferentiableOn ℂ
      (fun p : Frame X.Ψ r × (Fin n → Fin g → ℂ) => p.2 k i) (X.dom ×ˢ Set.univ) := by fun_prop
  refine CanTh.differentiableOn_polyDeriv_param (FourierCoefficientDomain.isOpen_dom X)
    (F := fun p : Frame X.Ψ r × (Fin n → Fin g → ℂ) => ∏ k,
      cexp (Real.pi / 2 * (p.2 k ⬝ᵥ splitMat X bas idx p.1 *ᵥ p.2 k)) *
        thetaChar (tauMat X bas idx p.1) (fun i => (a k i : ℂ)) (fun i => (b k i : ℂ))
          (hMat X bas idx p.1 *ᵥ p.2 k)) ?_ P _ 0
  refine CanTh.differentiableOn_prod_fun _ fun k _ => DifferentiableOn.mul ?_ ?_
  · refine DifferentiableOn.cexp (DifferentiableOn.const_mul ?_ _)
    simp only [dotProduct, mulVec]
    exact DifferentiableOn.fun_sum fun i _ => (hz k i).fun_mul (DifferentiableOn.fun_sum fun j _ =>
      (hl (differentiableOn_splitMat idx hs i j)).fun_mul (hz k j))
  · exact CanTh.differentiableOn_thetaChar (fun i j => hl (differentiableOn_tauMat idx hs i j))
      (differentiableOn_pi.2 fun i => DifferentiableOn.fun_sum fun j _ =>
        (hl (differentiableOn_hMat idx hs i j)).mul (hz k j))
      (fun p hp => CanTh.mem_thetaDomain (tauMat_im_posDef idx hs hp.1)) _ _

end Holo

section Compl

def headSpan (x : Frame X.Ψ r) (τ : X.Ψ) : Submodule ℂ (Fin r → ℂ) :=
  Submodule.span ℂ (FD.col (mat x τ) '' {a | (a : ℕ) < X.p0})

def tailSpan (y : Frame X.Ψ r) (τ : X.Ψ) : Submodule ℂ (Fin r → ℂ) :=
  Submodule.span ℂ (FD.col (mat y τ) '' {a | X.p0 ≤ (a : ℕ)})

def headProj : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => if (a : ℕ) < X.p0 then 1 else 0

def mix (x y : Frame X.Ψ r) : Frame X.Ψ r := fun τ i a =>
  if (a : ℕ) < X.p0 then x τ i a else y τ i a

def unip (K : Frame X.Ψ r) : Frame X.Ψ r := fun τ a c =>
  if (a : ℕ) < X.p0 ∧ X.p0 ≤ (c : ℕ) then K τ a c else if a = c then 1 else 0

def shear (x y : Frame X.Ψ r) : Frame X.Ψ r := fun τ a c =>
  -((mat (mix X x y) τ)⁻¹ * mat x τ) a c

def adapt (x y : Frame X.Ψ r) : Frame X.Ψ r := rmul x (unip X (shear X x y))

def betaMat (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
    (x y : Frame X.Ψ r) : Matrix (Fin g) (Fin g) ℂ := splitMat X bas idx (adapt X x y)

def embCx (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (τ : E →+* ℂ) :
    (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
  (Matrix.of fun a s => Data.emb τ (bas (Pi.single s 1) : Fin r → E) a).mulVecLin

theorem headProj_mul_self : headProj X * headProj X = headProj X := by
  rw [headProj, diagonal_mul_diagonal]
  congr 1; funext a; split_ifs <;> simp

theorem mat_unip (K : Frame X.Ψ r) (τ : X.Ψ) :
    mat (unip X K) τ = 1 + headProj X * mat K τ * (1 - headProj X) := by
  ext a c
  simp only [headProj, Matrix.mul_sub, Matrix.mul_one, Matrix.add_apply, Matrix.sub_apply, mul_diagonal,
    diagonal_mul, mat, of_apply, unip, one_apply, Fin.ext_iff]
  split_ifs <;> first | omega | simp

@[simp] theorem mix_self (x : Frame X.Ψ r) : mix X x x = x := by
  funext τ i a; simp [mix]

theorem mat_unip_neg_mul (K : Frame X.Ψ r) (τ : X.Ψ) :
    mat (unip X (-K)) τ * mat (unip X K) τ = 1 := by
  have h : (1 - headProj X) * headProj X = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, headProj_mul_self, sub_self]
  have h1 : headProj X * mat K τ * (1 - headProj X) * (headProj X * mat K τ * (1 - headProj X)) =
      0 := by
    rw [Matrix.mul_assoc (headProj X * _), Matrix.mul_assoc (headProj X) _ (1 - _),
      ← Matrix.mul_assoc (1 - _), h, Matrix.zero_mul, Matrix.mul_zero]
  rw [mat_unip, mat_unip, show mat (-K) τ = -mat K τ from rfl, Matrix.mul_neg, Matrix.neg_mul,
    add_mul, mul_add, mul_add, neg_mul, neg_mul, h1]
  simp

theorem unip_mem_Bor (K : Frame X.Ψ r) : unip X K ∈ Bor X.Ψ r := fun τ =>
  ⟨(isUnit_det_of_left_inverse (mat_unip_neg_mul X K τ)).ne_zero, fun a c h => by
    rw [Fin.lt_def] at h
    rw [unip, if_neg (by omega), if_neg (by rw [Fin.ext_iff]; omega)]⟩

theorem per_rmul_unip (x K : Frame X.Ψ r) : per X (rmul x (unip X K)) = per X x := by
  classical
  have h : borMat X (unip X K) = 1 := by
    ext ⟨τ, a⟩ ⟨σ, c⟩
    by_cases hτ : σ = τ
    · subst hτ
      rcases lt_or_ge (a : ℕ) X.p0 with ha | ha
      · rw [borMat_of_lt X _ _ ha, unip, if_neg (by omega)]
        simp [one_apply, eq_comm]
      · rw [borMat_of_le X _ _ ha, inv_eq_left_inv (mat_unip_neg_mul X K σ), mat, of_apply, unip,
          if_neg (by omega)]
        simp [one_apply]
    · rw [borMat_of_ne X _ hτ, one_apply_ne fun h => hτ (congrArg Prod.fst h).symm]
  funext v
  rw [per_rmul x (unip_mem_Bor X K), h, one_mulVec]

variable {X}

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

section Congr

variable {x x' : Frame X.Ψ r} (h : per X x' = per X x)
include h

theorem hMat_congr : hMat X bas idx x' = hMat X bas idx x := by simp only [hMat, perMat, h]

theorem tauMat_congr : tauMat X bas idx x' = tauMat X bas idx x := by
  simp only [tauMat, hMat, perMat, h]

theorem thFr_congr {q0 : ℕ} (hr : X.p0 + q0 = r) (n : ℕ) (a b : Fin n → Fin g → ℝ)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thFr X hr bas idx n a b P x' = thFr X hr bas idx n a b P x := by
  simp only [thFr, canFn, imInv, hMat_congr bas idx h, tauMat_congr bas idx h]

end Congr

variable {bas} (hs : IsSympl X bas)
include hs

end Compl

example (n : ℕ) :
    DifferentiableOn ℂ (thFr HyperbolicCusp.flagData Gauss.hr Gauss.bas Gauss.idx n 0 0 1)
      HyperbolicCusp.flagData.dom ∧
    thFr HyperbolicCusp.flagData Gauss.hr Gauss.bas Gauss.idx n 0 0 1 Gauss.one ≠ 0 :=
  ⟨differentiableOn_thFr _ Gauss.isSympl_bas _ n 0 0 (Harm.isHarmonic_C 1),
    Gauss.thFr_one_ne_zero n⟩

end

end GlobalTheory.ThFr
