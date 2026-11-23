import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsWittFrameExtend
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section
namespace GlobalTheory.PlaneFrameCons
open Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gram_entry {n r s : ℕ} (σ : E →ₐ[F] E) (M : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin r) E)
    (B : Matrix (Fin n) (Fin s) E) (i : Fin r) (j : Fin s) :
    (cT (σ : E →+* E) A * M * B) i j = hE σ M (fun k => A k i) (fun k => B k j) := by
  simp only [hE, Formalism.UG.hform, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    RingHom.coe_coe]
  rw [Finset.sum_comm]

theorem gram_mulVec_entry {n r : ℕ} (σ : E →ₐ[F] E) (M : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin r) E)
    (z : Fin n → E) (i : Fin r) :
    ((cT (σ : E →+* E) A * M) *ᵥ z) i = hE σ M (fun k => A k i) z := by
  simp only [hE, Formalism.UG.hform, cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, RingHom.coe_coe]
  rw [Finset.sum_comm]

variable [NumberField F] [NumberField E]

theorem hE_eq {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E)
    (u v : Fin n → E) : hE σ (c • J.map σ) u v = c * σ (form σ J u v) := by
  have := GlobalTheory.TwoPlaneWitt.hE_smul_map hσ J c 1 1 u v
  simpa using this

theorem exists_isWittFrame_cons : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J → ∀ c₀ : E, c₀ ≠ 0 →
      IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
        ∃ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' ∧
          (∀ k, X' k 0 = H.x k) ∧ (∀ k, Y' k 0 = c₀⁻¹ * H.y k) ∧
          ∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i := by
  intro F E _ _ _ _ _ σ hcm n n₁ W W₁ H hskew hn hxx hyy hxy horth hg c₀ hc hND₁ hND r Xf Yf hW
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  set M := c₀ • W.J.map σ with hM
  set M₁ := c₀ • W₁.J.map σ with hM₁

  have hι : ∀ u v, hE σ M (H.ι *ᵥ u) (H.ι *ᵥ v) = hE σ M₁ u v := fun u v => by
    rw [hM, hM₁, hE_eq hσ, hE_eq hσ, GlobalTheory.TwoPlaneWitt.form_mulVec, hg]
  have hcol : ∀ (A : Matrix (Fin n₁) (Fin r) E) (i : Fin r), (fun k => (H.ι * A) k i) = H.ι *ᵥ fun k => A k i :=
    fun A i => funext fun k => by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hyx : form σ W.J H.y H.x = -1 := by rw [GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ, hxy, map_one]
  have hxι : ∀ u, form σ W.J H.x (H.ι *ᵥ u) = 0 := fun u => by
    rw [GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ, (horth u).1, map_zero, neg_zero]
  have hyι : ∀ u, form σ W.J H.y (H.ι *ᵥ u) = 0 := fun u => by
    rw [GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ, (horth u).2, map_zero, neg_zero]
  let X' : Matrix (Fin n) (Fin (r + 1)) E := Matrix.of fun k => Fin.cons (H.x k) (fun i => (H.ι * Xf) k i)
  let Y' : Matrix (Fin n) (Fin (r + 1)) E := Matrix.of fun k => Fin.cons (c₀⁻¹ * H.y k) (fun i => (H.ι * Yf) k i)
  have cX0 : (fun k => X' k 0) = H.x := funext fun k => by simp [X']
  have cY0 : (fun k => Y' k 0) = c₀⁻¹ • H.y := funext fun k => by simp [Y']
  have cXs : ∀ i : Fin r, (fun k => X' k i.succ) = H.ι *ᵥ fun k => Xf k i := fun i => by
    rw [← hcol]; funext k; simp [X']
  have cYs : ∀ i : Fin r, (fun k => Y' k i.succ) = H.ι *ᵥ fun k => Yf k i := fun i => by
    rw [← hcol]; funext k; simp [Y']
  have gXX : ∀ i j, hE σ M₁ (fun k => Xf k i) (fun k => Xf k j) = 0 := fun i j => by
    rw [← gram_entry, hW.xx]; rfl
  have gYY : ∀ i j, hE σ M₁ (fun k => Yf k i) (fun k => Yf k j) = 0 := fun i j => by
    rw [← gram_entry, hW.yy]; rfl
  have gXY : ∀ i j, hE σ M₁ (fun k => Xf k i) (fun k => Yf k j) = (1 : Matrix (Fin r) (Fin r) E) i j := fun i j => by
    rw [← gram_entry, hW.xy]
  have sX : ∀ (s t : E) (a b : Fin n → E), hE σ M (s • a) (t • b) = σ s * t * c₀ * σ (form σ W.J a b) :=
    fun s t a b => GlobalTheory.TwoPlaneWitt.hE_smul_map hσ W.J c₀ s t a b
  refine ⟨X', Y', ⟨?_, ?_, ?_, ?_⟩, fun k => by simp [X'], fun k => by simp [Y'], fun k i => ⟨by simp [X'], by simp [Y']⟩⟩
  · ext i j
    rw [gram_entry]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [cX0, ← one_smul E H.x, sX]; simp [hxx]
    · rw [cX0, cXs, ← one_smul E H.x, ← one_smul E (H.ι *ᵥ _), sX]; simp [hxι]
    · rw [cX0, cXs, ← one_smul E H.x, ← one_smul E (H.ι *ᵥ _), sX]; simp [(horth _).1]
    · rw [cXs, cXs, hι, gXX]; rfl
  · ext i j
    rw [gram_entry]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [cY0, sX]; simp [hyy]
    · rw [cY0, cYs, ← one_smul E (H.ι *ᵥ _), sX]; simp [hyι]
    · rw [cY0, cYs, ← one_smul E (H.ι *ᵥ _), sX]; simp [(horth _).2]
    · rw [cYs, cYs, hι, gYY]; rfl
  · ext i j
    rw [gram_entry]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [cX0, cY0, ← one_smul E H.x, sX]; simp [hxy, hc]
    · rw [Matrix.one_apply_ne (Fin.succ_ne_zero j).symm, cX0, cYs, ← one_smul E H.x, ← one_smul E (H.ι *ᵥ _), sX]; simp [hxι]
    · rw [Matrix.one_apply_ne (Fin.succ_ne_zero i), cY0, cXs, ← one_smul E (H.ι *ᵥ _), sX]; simp [(horth _).2]
    · rw [cXs, cYs, hι, gXY]; simp [Matrix.one_apply]
  · intro z h1 h2 h3
    have σinj : ∀ a : E, σ a = 0 → a = 0 := fun a ha => by rw [← hσ a, ha, map_zero]
    have fxz : form σ W.J H.x z = 0 := by
      have e := congrFun h1 0
      rw [gram_mulVec_entry, cX0, hM, hE_eq hσ] at e
      exact σinj _ ((mul_eq_zero.1 e).resolve_left hc)
    have fyz : form σ W.J H.y z = 0 := by
      have e := congrFun h2 0
      rw [gram_mulVec_entry, cY0, ← one_smul E z, sX, Pi.zero_apply, mul_one] at e
      have hs : σ c₀⁻¹ ≠ 0 := fun h => inv_ne_zero hc (σinj _ h)
      rcases mul_eq_zero.1 e with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hs
        · exact absurd h hc
      · exact σinj _ h
    have hdet : W₁.J.det ≠ 0 := fun h => hND₁.2 (by
      rw [hM₁, Matrix.det_smul, show (W₁.J.map σ).det = σ W₁.J.det by exact (RingHom.map_det (σ : E →+* E) W₁.J).symm, h, map_zero, mul_zero])
    obtain ⟨α, β, z₁, rfl⟩ := GlobalTheory.UnipCocptForm.decomp σ W.J W₁.J H.x H.y H.ι hskew hσ hn hxx hyy hxy horth hg hdet z
    have fzx : form σ W.J (α • H.x + β • H.y + H.ι *ᵥ z₁) H.x = -β := by
      rw [GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_smul,
        GlobalTheory.UnipCocptForm.form_smul, hxx, hyx, (horth z₁).1]; ring
    have fzy : form σ W.J (α • H.x + β • H.y + H.ι *ᵥ z₁) H.y = α := by
      rw [GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_smul,
        GlobalTheory.UnipCocptForm.form_smul, hxy, hyy, (horth z₁).2]; ring
    have hβ : β = 0 := by
      have := GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ (α • H.x + β • H.y + H.ι *ᵥ z₁) H.x
      rw [fzx, fxz, map_zero, neg_zero] at this
      exact neg_eq_zero.1 this
    have hα : α = 0 := by
      have := GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ (α • H.x + β • H.y + H.ι *ᵥ z₁) H.y
      rwa [fzy, fyz, map_zero, neg_zero] at this
    subst hα hβ
    simp only [zero_smul, zero_add] at h1 h2 h3 ⊢
    have k1 : (cT (σ : E →+* E) Xf * M₁) *ᵥ z₁ = 0 := funext fun i => by
      have e := congrFun h1 i.succ
      rw [gram_mulVec_entry, cXs, hι] at e
      rw [gram_mulVec_entry, e]; rfl
    have k2 : (cT (σ : E →+* E) Yf * M₁) *ᵥ z₁ = 0 := funext fun i => by
      have e := congrFun h2 i.succ
      rw [gram_mulVec_entry, cYs, hι] at e
      rw [gram_mulVec_entry, e]; rfl
    rw [hW.aniso z₁ k1 k2 ((hι z₁ z₁).symm.trans h3), Matrix.mulVec_zero]
end GlobalTheory.PlaneFrameCons
end
