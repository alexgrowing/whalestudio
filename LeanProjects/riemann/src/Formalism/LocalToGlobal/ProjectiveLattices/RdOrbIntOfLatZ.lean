import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate

namespace Formalism.L2.Pj.FJ

section Core

variable {r ρ : ℕ}

def cM {m n : Type} (A : Matrix m n ℂ) : Matrix m n ℂ := A.map (starRingEnd ℂ)

theorem cM_cM {m n : Type} (A : Matrix m n ℂ) : cM (cM A) = A := by
  ext i j
  simp [cM]

theorem cM_mul {m n o : Type} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    cM (A * B) = cM A * cM B := by
  simp only [cM]
  exact Matrix.map_mul

theorem cM_transpose {m n : Type} (A : Matrix m n ℂ) : cM Aᵀ = (cM A)ᵀ := by
  simp only [cM]
  exact Matrix.transpose_map

theorem cM_add {m n : Type} (A B : Matrix m n ℂ) : cM (A + B) = cM A + cM B := by
  ext i j
  simp [cM]

theorem cM_one : cM (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cM]
  · simp [cM, Matrix.one_apply, h]

theorem unitary_core (g : Matrix (Fin r) (Fin r) ℂ) (F : Matrix (Fin r) (Fin ρ) ℂ)
    (β : Matrix (Fin ρ) (Fin ρ) ℂ) (hg : (cM g)ᵀ = g) (hiso : Fᵀ * g * cM F = 0)
    (hsk : cM β = -βᵀ) :
    (1 + F * β * (g * cM F)ᵀ)ᵀ * g * cM (1 + F * β * (g * cM F)ᵀ) = g := by
  have hg' : cM g = gᵀ := by
    have := congrArg Matrix.transpose hg
    simpa using this
  have key : ∀ X : Matrix (Fin ρ) (Fin r) ℂ, Fᵀ * (g * (cM F * X)) = 0 := by
    intro X
    rw [← Matrix.mul_assoc g, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hiso, Matrix.zero_mul]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
    cM_add, cM_one, cM_mul, cM_transpose, cM_cM, hg', hsk]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.mul_neg, Matrix.neg_mul, key, neg_zero, Matrix.mul_zero, add_zero, neg_neg]
  abel

theorem det_ne_core (g : Matrix (Fin r) (Fin r) ℂ) (F : Matrix (Fin r) (Fin ρ) ℂ)
    (β : Matrix (Fin ρ) (Fin ρ) ℂ) (hiso : Fᵀ * g * cM F = 0) :
    (1 + F * β * (g * cM F)ᵀ).det ≠ 0 := by
  have hT : (g * cM F)ᵀ * F = 0 := by
    have := congrArg Matrix.transpose hiso
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  generalize (g * cM F)ᵀ = H at hT ⊢
  have key : ∀ X : Matrix (Fin ρ) (Fin r) ℂ, H * (F * X) = 0 := by
    intro X
    rw [← Matrix.mul_assoc, hT, Matrix.zero_mul]
  have hinv : (1 + F * β * H) * (1 - F * β * H) = 1 := by
    simp only [add_mul, mul_sub, one_mul, mul_one, Matrix.mul_assoc, key, Matrix.mul_zero, sub_zero]
    first | abel | skip
  intro h0
  have := congrArg Matrix.det hinv
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end Core

section FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem emb_cc' (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by unfold cc; exact NumberField.IsCMField.complexEmbedding_complexConj E τ x

def Fm (τ : E →+* ℂ) (e : Fin ρ → Fin r → E) : Matrix (Fin r) (Fin ρ) ℂ :=
  Matrix.of fun k a => τ (e a k)

theorem zMatC_eq (X : Data E r) (e : Fin ρ → Fin r → E) (τ : E →+* ℂ) (β : Matrix (Fin ρ) (Fin ρ) ℂ) :
    zMatC X e τ β = 1 + Fm τ e * β * (X.Gm.map τ * cM (Fm τ e))ᵀ := by
  unfold zMatC
  ext k l
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply, Fm, cM,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem gram_eq (X : Data E r) (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm A = Aᵀ * X.Gm.map τ * cM A := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, cM, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem herm_g (X : Data E r) (τ : E →+* ℂ) : (cM (X.Gm.map τ))ᵀ = X.Gm.map τ := by
  ext i j
  simp only [Matrix.transpose_apply, cM, Matrix.map_apply]
  rw [← emb_cc', X.4 j i]

theorem iso_F (X : Data E r) (cu : CuspFD X ρ) (τ : E →+* ℂ) :
    (Fm τ cu.e)ᵀ * X.Gm.map τ * cM (Fm τ cu.e) = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fm, cM, Matrix.of_apply, Matrix.map_apply,
    Matrix.zero_apply, Finset.sum_mul]
  have h := congrArg τ (cu.3 a b)
  unfold ReciprocityTheory.ChartRestriction.G.FD.herm at h
  simp only [map_sum, map_mul, map_zero, emb_cc'] at h
  rw [Finset.sum_comm]
  exact h

theorem skew_beta (X : Data E r) (cu : CuspFD X ρ) (hb : ∀ k, IsSkew (zBas X cu k)) (τ : E →+* ℂ)
    (t : Fin (nZ X ρ) → ℝ) :
    cM (∑ k, (t k : ℂ) • (zBas X cu k).map τ) = -(∑ k, (t k : ℂ) • (zBas X cu k).map τ)ᵀ := by
  have h' := hb
  unfold IsSkew at h'
  ext a b
  simp only [cM, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal, ← emb_cc', h', map_neg, mul_neg, Finset.sum_neg_distrib]

theorem zBas_skew (X : Data E r) (cu : CuspFD X ρ) (h : ∃ bs, IsZBasis X cu bs) (k : Fin (nZ X ρ)) :
    IsSkew (zBas X cu k) := by
  have hs : LinearIndependent ℤ (zBas X cu) ∧
      ∀ β, β ∈ zGam X cu ↔ β ∈ Submodule.span ℤ (Set.range (zBas X cu)) := Classical.epsilon_spec h
  have hm : zBas X cu k ∈ zGam X cu := (hs.2 _).2 (Submodule.subset_span ⟨k, rfl⟩)
  exact hm.1

theorem zAct_mem_dom (X : Data E r) (cu : CuspFD X ρ) (hb : ∀ k, IsSkew (zBas X cu k))
    (t : Fin (nZ X ρ) → ℝ) (x : Frame X.Ψ r) (hx : x ∈ X.dom) : zAct X cu t x ∈ X.dom := by
  unfold zAct ReciprocityTheory.ChartRestriction.G.FD.Data.dom at *
  unfold GG at *
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  unfold dmin mat at *
  beta_reduce
  set M := zMatC X cu.e (τ : E →+* ℂ) (∑ k, ((t k : ℝ) : ℂ) • (zBas X cu k).map (τ : E →+* ℂ)) with hMdef
  have hU : Mᵀ * X.Gm.map (τ : E →+* ℂ) * cM M = X.Gm.map (τ : E →+* ℂ) := by
    rw [hMdef, zMatC_eq]
    exact unitary_core _ _ _ (herm_g X _) (iso_F X cu _) (skew_beta X cu hb _ t)
  have hD : M.det ≠ 0 := by
    rw [hMdef, zMatC_eq]
    exact det_ne_core _ _ _ (iso_F X cu _)
  have hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ,
      Mᵀ * (X.Gm.map (τ : E →+* ℂ) * (cM M * Y)) = X.Gm.map (τ : E →+* ℂ) * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  have hG : ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (M * of (x τ)) =
      ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (of (x τ)) := by
    simp only [gram_eq, Matrix.transpose_mul, cM_mul, Matrix.mul_assoc, hU']
  refine ⟨?_, fun i => ?_⟩
  · show (M * of (x τ)).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hD hdet
  · have := hpos i
    rw [← hG] at this
    exact this

theorem orbDom_of_latZ {Comp : Type} (X : Comp → Data E r) (h : LatZ X ρ) : OrbDom X ρ := by
  intro cu t x hx
  exact zAct_mem_dom (X cu.1) cu.2 (fun k => zBas_skew _ _ (h cu) k) t x hx

theorem rdOrbInt_of_latZ {Comp K : Type} [Field K] (σ : K →+* ℂ) {C : Type} [AddCommGroup C]
    [Module K C] (X : Comp → Data E r) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ))
    (hc : ∀ f c, ContinuousOn (rd f c) (X c).dom) (h : LatZ X ρ) : RdOrbInt σ X ρ rd :=
  rdOrbInt_of σ X rd hc (orbDom_of_latZ X h)

end FD

end Formalism.L2.Pj.FJ
