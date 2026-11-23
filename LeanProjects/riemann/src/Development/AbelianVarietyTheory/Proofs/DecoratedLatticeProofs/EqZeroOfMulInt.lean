import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.TopFrames

theorem exists_frame {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (hc : Fintype.card Y = N) (M : Matrix (Fin N) Y k) (hM : ∀ y, M *ᵥ y = 0 → y = 0) :
    ∃ F : GlobalTheory.LocMod.Frame k N Y, F.β = M := by
  classical
  let e : Y ≃ Fin N := Fintype.equivFinOfCardEq hc
  have hinj : Function.Injective (M.submatrix id e.symm).mulVec := by
    intro y y' h
    have h0 : (M.submatrix id e.symm) *ᵥ (y - y') = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
    rw [Matrix.submatrix_mulVec_equiv] at h0
    have h1 := hM _ (by simpa using h0)
    funext i
    have := congrFun h1 (e.symm i)
    simpa [sub_eq_zero] using this
  obtain ⟨U, hU⟩ := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hM' : M = (U.val).submatrix id e := by
    rw [hU]; ext i j; simp
  refine ⟨⟨M, (U⁻¹).val.submatrix e id, ?_, ?_⟩, rfl⟩
  · rw [hM', Matrix.submatrix_mul_equiv, Units.mul_inv]; rfl
  · rw [hM']
    have := Matrix.submatrix_mul_equiv (U⁻¹).val U.val e (Equiv.refl _) e
    simp only [Equiv.coe_refl] at this
    rw [this, Units.inv_mul, Matrix.submatrix_one_equiv]

theorem eq_zero_of_mul_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : k) (h : ∀ c : k, c * a ∈ 𝒪[k]) : a = 0 := by
  by_contra ha
  obtain ⟨x, hx⟩ := Valuation.IsNontrivial.exists_one_lt (v := valuation k)
  have := h (x / a)
  rw [div_mul_cancel₀ _ ha, Valuation.mem_integer_iff] at this
  exact absurd hx (not_lt.mpr this)

theorem top_frames : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (s : ℕ) (hs : s + 1 + 1 = D.R.m), d.Lz.rank = 1 → Fintype.card (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2)) = D.sp.X'.rank → ∀ (a : k) (z₀ : Fin d.Lz.rank → k), valuation k a = 1 → (∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * a)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i)) → (∀ B : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) (AE D), B.map (toEAf D) = d.top.β.val → ∀ (y : Fin D.sp.X'.rank → k) (b : k), (fun i => q.sec (((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr *ᵥ (B.map (ofSplit q).π *ᵥ y) + b • ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀)) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v) ↔ (∀ i, y i ∈ 𝒪[k]) ∧ b ∈ 𝒪[k]) → ∃ (FT : GlobalTheory.LocMod.Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))) (FM : GlobalTheory.LocMod.Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)) (c : k), valuation k c = 1 ∧ FM.β = fromCols ((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β) (Matrix.of fun r _ => ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r) ∧ (∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * c)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i)) ∧ (∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v)) ∧ ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 d.top.β (FT.β.submatrix id e.symm) := by
  intro D u d τ k _ _ _ _ q s hs hr hc a z₀ ha hτ hsp
  obtain ⟨e, he⟩ := PinModel.exists_ord _ _ _ _ _ hc
  choose f hf using PinModel.toEAf_surj D
  have hB : (d.top.β.val.map f).map (toEAf D) = d.top.β.val := by
    ext i j; exact hf _
  have H := hsp _ hB
  set P := (d.top.β.val.map f).map (ofSplit q).π with hP
  set A := (d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr with hA
  set w := (d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀ with hw
  have H0 : ∀ (y : Fin D.sp.X'.rank → k) (b : k), A *ᵥ (P *ᵥ y) + b • w = 0 → y = 0 ∧ b = 0 := by
    intro y b h
    have key : ∀ c : k, (∀ i, c * y i ∈ 𝒪[k]) ∧ c * b ∈ 𝒪[k] := by
      intro c
      refine (H (c • y) (c * b)).mp ?_
      have : A *ᵥ (P *ᵥ (c • y)) + (c * b) • w = 0 := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, mul_smul, ← smul_add, h, smul_zero]
      rw [this]
      simp only [Pi.zero_apply, map_zero]
      exact zero_mem _
    exact ⟨funext fun i => eq_zero_of_mul_int _ fun c => (key c).1 i,
      eq_zero_of_mul_int _ fun c => (key c).2⟩
  have hsub : ∀ y, P.submatrix id e *ᵥ y = P *ᵥ (y ∘ e.symm) := by
    intro y; rw [Matrix.submatrix_mulVec_equiv]; rfl
  obtain ⟨FT, hFT⟩ := exists_frame hc (P.submatrix id e) (by
    intro y hy
    rw [hsub] at hy
    have := (H0 (y ∘ e.symm) 0 (by rw [hy]; simp)).1
    funext i
    simpa using congrFun this (e i))
  have hmul : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k,
      fromCols (A * FT.β) (Matrix.of fun r (_ : Unit) => w r) *ᵥ y
        = A *ᵥ (P *ᵥ ((y ∘ Sum.inl) ∘ e.symm)) + y (Sum.inr ()) • w := by
    intro y
    rw [Matrix.fromCols_mulVec, ← Matrix.mulVec_mulVec, hFT, hsub]
    congr 1
    funext r
    simp [Matrix.mulVec, dotProduct, mul_comm]
  obtain ⟨FM, hFM⟩ := exists_frame (N := (D.sp.X (s + 1 + 1)).rank)
    (Y := Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
    (by rw [Fintype.card_sum, hc, ← (d.oT (s + 1 + 1) hs).rank_add, hr]; simp)
    (fromCols (A * FT.β) (Matrix.of fun r (_ : Unit) => w r)) (by
      intro y hy
      rw [hmul] at hy
      obtain ⟨h1, h2⟩ := H0 _ _ hy
      funext i
      rcases i with i | i
      · simpa using congrFun h1 (e i)
      · exact h2)
  refine ⟨FT, FM, a, ha, hFM, hτ, ?_, e, he, ?_⟩
  · intro y
    rw [hFM, hmul, H]
    constructor
    · intro h; exact ⟨fun i => h _, h _⟩
    · rintro ⟨h1, h2⟩ (i | i)
      · simpa using h1 (e i)
      · exact h2
  · intro b hb
    have h1 : Formalism.L2.Theta.mt D.sp.X' 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [h1, Matrix.one_mul, hFT]
    ext i j
    simp only [hP, Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.apply_symm_apply]
    apply PinModel.pi_congr
    rw [hf]
    exact congrFun (congrFun hb i) j

end GlobalTheory.LocMod.TopFrames
