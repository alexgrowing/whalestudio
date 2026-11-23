import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change

theorem sgI_mul_self (j j' : ℕ) : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply, ← fromBlocks_one]

theorem unitary_of_blocks {j j' : ℕ} (u : Matrix (Sg j j') (Sg j j') ℂ) (hu : uᴴ * sgI j j' * u = sgI j j')
    (h21 : u.toBlocks₂₁ = 0) (h12 : u.toBlocks₁₂ = 0) : uᴴ * u = 1 := by
  have hb : u = fromBlocks u.toBlocks₁₁ 0 0 u.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks u, h21, h12]
  generalize u.toBlocks₁₁ = a at hb
  generalize u.toBlocks₂₂ = d at hb
  subst hb
  have h := hu
  simp only [sgI, fromBlocks_conjTranspose, fromBlocks_multiply] at h
  obtain ⟨h1, -, -, h2⟩ := fromBlocks_inj.1 h
  have h1' : aᴴ * a = 1 := by
    simpa using h1
  have h2' : dᴴ * d = 1 := by
    simpa using h2
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, h1', h2', ← fromBlocks_one]

theorem blocks_of_unitary {j j' : ℕ} (u : Matrix (Sg j j') (Sg j j') ℂ) (hu : uᴴ * sgI j j' * u = sgI j j')
    (h : uᴴ * u = 1) : u.toBlocks₂₁ = 0 ∧ u.toBlocks₁₂ = 0 := by
  have h' : u * uᴴ = 1 := mul_eq_one_comm.1 h
  have hcomm : sgI j j' * u = u * sgI j j' := by
    calc sgI j j' * u = (u * uᴴ) * sgI j j' * u := by rw [h', one_mul]
      _ = u * (uᴴ * sgI j j' * u) := by simp only [Matrix.mul_assoc]
      _ = u * sgI j j' := by rw [hu]
  rw [← fromBlocks_toBlocks u] at hcomm
  simp only [sgI, fromBlocks_multiply] at hcomm
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul] at hcomm
  obtain ⟨-, h12, h21, -⟩ := fromBlocks_inj.1 hcomm
  constructor
  · ext a b
    have := congrFun (congrFun h21 a) b
    simp only [Matrix.neg_apply, Matrix.zero_apply] at this ⊢
    exact neg_eq_self.1 this
  · ext a b
    have := congrFun (congrFun h12 a) b
    simp only [Matrix.neg_apply, Matrix.zero_apply] at this ⊢
    exact self_eq_neg.1 this

def imLin {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun w := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [star_add, mulVec_add, dotProduct_add]
  map_smul' r a := by
    have : star (r • a) = (r : ℂ) • star a := by
      ext i; simp
    simp [this, mulVec_smul, dotProduct_smul]

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)

theorem perExt_injective : Function.Injective (C.perExt R) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hcoord : ∀ l, C.bas.equivFun y l = 0 := by
    intro l
    obtain ⟨x, hx⟩ := R.unimod.2 (C.lam.coord l)
    have key : imLin R.Hm (R.P x) (C.perExt R y) = C.bas.equivFun y l := by
      rw [LatEmb.perExt, Module.Basis.constr_apply_fintype, map_sum]
      have hk : ∀ k, imLin R.Hm (R.P x) (R.P (C.lam k)) = if k = l then 1 else 0 := by
        intro k
        have h1 : imLin R.Hm (R.P x) (R.P (C.lam k)) = (R.form x (C.lam k) : ℝ) := R.im x _
        rw [h1, hx]
        simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
      simp [hk]
    rw [← key, hy, map_zero]
  have : C.bas.equivFun y = 0 := funext hcoord
  simpa using this

open Classical in
theorem pPart_add (τ : Ψ) (y y' : Fin (j + j') → ℂ) :
    C.pPart R τ (y + y') = C.pPart R τ y + C.pPart R τ y' := by
  simp only [LatEmb.pPart, smul_add, Pi.single_add, map_add]
  module

open Classical in
theorem pBar_add (τ : Ψ) (y y' : Fin (j + j') → ℂ) :
    C.pBar R τ (y + y') = C.pBar R τ y + C.pBar R τ y' := by
  simp only [LatEmb.pBar, smul_add, Pi.single_add, map_add]
  module

open Classical in
theorem pPart_add_pBar (τ : Ψ) (y : Fin (j + j') → ℂ) :
    C.pPart R τ y + C.pBar R τ y = C.perExt R (Pi.single τ y) := by
  simp only [LatEmb.pPart, LatEmb.pBar]
  module

theorem eq_zero_of_parts (τ : Ψ) (y : Fin (j + j') → ℂ) (h : C.pPart R τ y = 0) (h' : C.pBar R τ y = 0) : y = 0 := by
  classical
  have h0 : C.perExt R (Pi.single τ y) = 0 := by
    rw [← pPart_add_pBar, h, h', add_zero]
  have h1 : (Pi.single τ y : Ψ → Fin (j + j') → ℂ) = 0 := (injective_iff_map_eq_zero _).1 (perExt_injective C R) _ h0
  simpa using congrFun h1 τ

variable {C}

theorem cinv_mul {A : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (h : Aᴴ * C.sgr τ * A = sgI j j') :
    C.cinv A τ * A = 1 := by
  calc C.cinv A τ * A = sgI j j' * (Aᴴ * C.sgr τ * A) := by
        simp only [LatEmb.cinv, Matrix.mul_assoc]
    _ = 1 := by rw [h, sgI_mul_self]

theorem mul_cinv {A : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (h : Aᴴ * C.sgr τ * A = sgI j j') :
    A * C.cinv A τ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (cinv_mul h)

theorem sgr_eq {A : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (h : Aᴴ * C.sgr τ * A = sgI j j') :
    C.sgr τ = (C.cinv A τ)ᴴ * sgI j j' * C.cinv A τ := by
  have h1 : (C.cinv A τ)ᴴ * Aᴴ = 1 := by
    rw [← conjTranspose_mul, mul_cinv h, conjTranspose_one]
  calc C.sgr τ = ((C.cinv A τ)ᴴ * Aᴴ) * C.sgr τ * (A * C.cinv A τ) := by rw [h1, mul_cinv h, one_mul, mul_one]
    _ = (C.cinv A τ)ᴴ * (Aᴴ * C.sgr τ * A) * C.cinv A τ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h]

theorem change_isSgU {A A' : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (h : Aᴴ * C.sgr τ * A = sgI j j')
    (h' : A'ᴴ * C.sgr τ * A' = sgI j j') :
    (C.cinv A τ * A')ᴴ * sgI j j' * (C.cinv A τ * A') = sgI j j' := by
  calc (C.cinv A τ * A')ᴴ * sgI j j' * (C.cinv A τ * A')
      = A'ᴴ * ((C.cinv A τ)ᴴ * sgI j j' * C.cinv A τ) * A' := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = sgI j j' := by rw [← sgr_eq h, h']

theorem mulVec_eq_zero {A : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (h : Aᴴ * C.sgr τ * A = sgI j j')
    {w : Sg j j' → ℂ} (hw : A *ᵥ w = 0) : w = 0 := by
  have : (C.cinv A τ * A) *ᵥ w = 0 := by
    rw [← mulVec_mulVec, hw, mulVec_zero]
  simpa [cinv_mul h] using this

theorem split_vec (w : Sg j j' → ℂ) : w = Sum.elim (w ∘ Sum.inl) (0 : Fin j' → ℂ) + Sum.elim (0 : Fin j → ℂ) (w ∘ Sum.inr) := by
  ext (i | i) <;> simp

theorem inr_eq_zero {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A) (τ : Ψ)
    (w : Sg j j' → ℂ) (hw : C.pPart R τ (A τ *ᵥ w) = 0) (i : Fin j') : w (Sum.inr i) = 0 := by
  have h1 : C.pPart R τ (A τ *ᵥ Sum.elim (0 : Fin j → ℂ) (w ∘ Sum.inr)) = 0 := by
    rw [split_vec w, mulVec_add, pPart_add, hA.ker, zero_add] at hw
    simpa using hw
  have h2 := eq_zero_of_parts C R τ _ h1 (hA.kerBar τ _)
  have h3 := mulVec_eq_zero (hA.unit τ) h2
  simpa using congrFun h3 (Sum.inr i)

theorem inl_eq_zero {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A) (τ : Ψ)
    (w : Sg j j' → ℂ) (hw : C.pBar R τ (A τ *ᵥ w) = 0) (i : Fin j) : w (Sum.inl i) = 0 := by
  have h1 : C.pBar R τ (A τ *ᵥ Sum.elim (w ∘ Sum.inl) (0 : Fin j' → ℂ)) = 0 := by
    rw [split_vec w, mulVec_add, pBar_add, hA.kerBar, add_zero] at hw
    simpa using hw
  have h2 := eq_zero_of_parts C R τ _ (hA.ker τ _) h1
  have h3 := mulVec_eq_zero (hA.unit τ) h2
  simpa using congrFun h3 (Sum.inl i)

theorem mulVec_inl (u : Matrix (Sg j j') (Sg j j') ℂ) (k : Fin j) (x : Sg j j') :
    (u *ᵥ Sum.elim (Pi.single k 1) (0 : Fin j' → ℂ)) x = u x (Sum.inl k) := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Pi.single_apply]

theorem mulVec_inr (u : Matrix (Sg j j') (Sg j j') ℂ) (k : Fin j') (x : Sg j j') :
    (u *ᵥ Sum.elim (0 : Fin j → ℂ) (Pi.single k 1)) x = u x (Sum.inr k) := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Pi.single_apply]

theorem mulVec_diag_inl (u : Matrix (Sg j j') (Sg j j') ℂ) (h : u.toBlocks₂₁ = 0) (v : Fin j → ℂ) :
    u *ᵥ Sum.elim v (0 : Fin j' → ℂ) = Sum.elim (u.toBlocks₁₁ *ᵥ v) (0 : Fin j' → ℂ) := by
  ext (i | i)
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₁₁]
  · have : ∀ k, u (Sum.inr i) (Sum.inl k) = 0 := fun k => congrFun (congrFun h i) k
    simp [mulVec, dotProduct, Fintype.sum_sum_type, this]

theorem mulVec_diag_inr (u : Matrix (Sg j j') (Sg j j') ℂ) (h : u.toBlocks₁₂ = 0) (v : Fin j' → ℂ) :
    u *ᵥ Sum.elim (0 : Fin j → ℂ) v = Sum.elim (0 : Fin j → ℂ) (u.toBlocks₂₂ *ᵥ v) := by
  ext (i | i)
  · have : ∀ k, u (Sum.inl i) (Sum.inr k) = 0 := fun k => congrFun (congrFun h i) k
    simp [mulVec, dotProduct, Fintype.sum_sum_type, this]
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₂₂]

end Arch

theorem isAdapted_iff_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A A' : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), R.form = F.form → C.IsAdapted R A → (∀ τ, (A' τ)ᴴ * C.sgr τ * A' τ = sgI j j') → (C.IsAdapted R A' ↔ ∀ τ, (C.cinv (A τ) τ * A' τ)ᴴ * (C.cinv (A τ) τ * A' τ) = 1) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R A A' _ hA hA'
  have hmul : ∀ τ, A τ * (C.cinv (A τ) τ * A' τ) = A' τ := fun τ => by
    rw [← Matrix.mul_assoc, mul_cinv (hA.unit τ), Matrix.one_mul]
  constructor
  · intro hAd τ
    have h21 : (C.cinv (A τ) τ * A' τ).toBlocks₂₁ = 0 := by
      ext i k
      have hw : C.pPart R τ (A τ *ᵥ ((C.cinv (A τ) τ * A' τ) *ᵥ Sum.elim (Pi.single k 1) (0 : Fin j' → ℂ))) = 0 := by
        rw [mulVec_mulVec, hmul]
        exact hAd.ker τ _
      have := inr_eq_zero R hA τ _ hw i
      rwa [mulVec_inl] at this
    have h12 : (C.cinv (A τ) τ * A' τ).toBlocks₁₂ = 0 := by
      ext i k
      have hw : C.pBar R τ (A τ *ᵥ ((C.cinv (A τ) τ * A' τ) *ᵥ Sum.elim (0 : Fin j → ℂ) (Pi.single k 1))) = 0 := by
        rw [mulVec_mulVec, hmul]
        exact hAd.kerBar τ _
      have := inl_eq_zero R hA τ _ hw i
      rwa [mulVec_inr] at this
    exact unitary_of_blocks _ (change_isSgU (hA.unit τ) (hA' τ)) h21 h12
  · intro hu
    have hb := fun τ => blocks_of_unitary _ (change_isSgU (hA.unit τ) (hA' τ)) (hu τ)
    refine ⟨hA', fun τ v => ?_, fun τ v => ?_⟩
    · rw [← hmul τ, ← mulVec_mulVec, mulVec_diag_inl _ (hb τ).1]
      exact hA.ker τ _
    · rw [← hmul τ, ← mulVec_mulVec, mulVec_diag_inr _ (hb τ).2]
      exact hA.kerBar τ _

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change
