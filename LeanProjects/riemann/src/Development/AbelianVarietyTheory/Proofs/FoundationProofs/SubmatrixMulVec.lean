import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames
open scoped Matrix

namespace GlobalTheory.FlatChange

theorem exists_blockMat {J : Type} [Fintype J] {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ, Fin (m τ))
    (K : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) ℂ) :
    ∃ V : Matrix (Fin g) (Fin g) ℂ, ∀ (z : Fin g → ℂ) τ i,
      (V *ᵥ z) (e.symm ⟨τ, i⟩) = (K τ *ᵥ fun j => z (e.symm ⟨τ, j⟩)) i := by
  classical
  refine ⟨(Matrix.blockDiagonal' K).submatrix e e, fun z τ i => ?_⟩
  rw [Matrix.mulVec, dotProduct, ← e.symm.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single τ]
  · simp [Matrix.mulVec, dotProduct]
  · intro τ' _ h
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ h.symm]
  · simp

theorem det_mul_eq_one {n r : ℕ} (h : n = r) (B : Matrix (Fin r) (Fin r) ℂ) (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, B.submatrix (Fin.cast h) (Fin.cast h) *ᵥ C i = Pi.single i 1) : B.det * C.det = 1 := by
  subst h
  have : B * Cᵀ = 1 := by
    ext a i
    have := congrFun (hC i) a
    rw [Pi.single_apply] at this
    rw [Matrix.one_apply, ← this]
    rfl
  rw [← Matrix.det_transpose C, ← Matrix.det_mul, this, Matrix.det_one]

theorem submatrix_mulVec {n r : ℕ} (h : n = r) (B : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) (i : Fin n) :
    (B.submatrix (Fin.cast h) (Fin.cast h) *ᵥ fun j => v (Fin.cast h j)) i = (B *ᵥ v) (Fin.cast h i) := by
  subst h
  rfl

theorem perFr_of_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ} (h : n = r) (X : Data E r)
    (h0 : X.p0 = 0) (x : Frame X.Ψ r) (v : Fin r → E) {ρ : E →+* ℂ} (hρ : ρ ∈ X.Ψ) (i : Fin n) :
    perFr X x v ρ i = ((mat x ⟨ρ, hρ⟩)⁻¹ *ᵥ Data.emb ρ v) (Fin.cast h i) := by
  have hi : X.p0 + (i : ℕ) < r := by have := i.2; omega
  unfold perFr
  rw [dif_pos hρ, dif_pos hi]
  congr 1
  ext
  simp [h0]

set_option maxHeartbeats 1000000 in

theorem det_frChg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), Dw.q = 0 → GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x x' : (U.X k).dom) (τ : Psi H) (hτ : relab c σ τ.1 ∈ (U.X k).Ψ) (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) (CAt σ))) (a : CAt σ), FrChg g a (U.un k x) (U.un k x') → (mat x'.1 ⟨_, hτ⟩).det = toC (g τ.1).det * (mat x.1 ⟨_, hτ⟩).det := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hq hσ hU k x x' τ hτ cf a hchg
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hpt⟩ := hU
  obtain ⟨-, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hΨ⟩ := hty k
  obtain ⟨P, hPe, p, hx, hd, -⟩ := hpt k x
  obtain ⟨P', hPe', p', -, hd', -⟩ := hpt k x'
  have hm : ∀ ρ, relab c σ ρ ∈ (U.X k).Ψ → Dw.mult ρ = r := fun ρ h => by
    unfold Datum.mult
    rw [if_pos ((hrt ρ).1 ((hΨ _).1 h))]; omega
  have hm' : ∀ ρ, Fin (Dw.mult ρ) → relab c σ ρ ∈ (U.X k).Ψ := fun ρ i => by
    by_contra h
    have h1 : Dw.mult ρ = 0 := by
      unfold Datum.mult
      rw [if_neg (fun h' => h ((hΨ _).2 ((hrt ρ).2 h'))), hq]
    have := i.2
    omega
  let B : (U.X k).Ψ → Matrix (Fin r) (Fin r) ℂ := fun ρ => (mat x'.1 ρ)⁻¹ * mat x.1 ρ
  let K : ∀ ρ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) ℂ := fun ρ =>
    if h : relab c σ ρ ∈ (U.X k).Ψ then (B ⟨_, h⟩).submatrix (Fin.cast (hm ρ h)) (Fin.cast (hm ρ h)) else 0
  have hK : ∀ ρ (h : relab c σ ρ ∈ (U.X k).Ψ),
      K ρ = (B ⟨_, h⟩).submatrix (Fin.cast (hm ρ h)) (Fin.cast (hm ρ h)) := fun ρ h => dif_pos h
  obtain ⟨V, hV⟩ := exists_blockMat e K
  have hPV : ∀ b, P' b = V *ᵥ P b := by
    intro b
    funext j
    obtain ⟨⟨ρ, i⟩, rfl⟩ := e.symm.surjective j
    have h := hm' ρ i
    have h1 : ∀ (y : Frame (U.X k).Ψ r) (i : Fin (Dw.mult ρ)),
        perFr (U.X k) y (φ k b : Fin r → E) (relab c σ (e (e.symm ⟨ρ, i⟩)).1) (e (e.symm ⟨ρ, i⟩)).2 =
          ((mat y ⟨_, h⟩)⁻¹ *ᵥ Data.emb (relab c σ ρ) (φ k b : Fin r → E)) (Fin.cast (hm ρ h) i) := fun y i => by
      rw [Equiv.apply_symm_apply]
      exact perFr_of_zero (hm ρ h) _ (hp0.trans hq) y _ h i
    rw [hV, hPe', h1, hK ρ h]
    simp only [hPe, h1]
    rw [submatrix_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 (x.2 _).1)]
  obtain ⟨-, -, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F (ik k) P P'
    (LinearEquiv.refl _ _) V p p' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hPV
  have hcol : ∀ i, V *ᵥ (∑ j, (show ℂ from cf τ.1 i j) • (Pi.single (e.symm ⟨τ.1, j⟩) 1 : Fin g → ℂ)) =
      Pi.single (e.symm ⟨τ.1, i⟩) 1 := by
    intro i
    have hc : IsCombAt (F.u (ik k) P) ((U.un k x).u τ.1) (show Fin (Dw.mult τ.1) → ℂ from cf τ.1 i)
        ((U.un k x').u τ.1 i) := by
      rw [← hx]; exact hchg.2.1 τ.1 i
    have d1 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F (ik k) P p _ ((U.un k x).u τ.1) _
      (hd τ.1) (cf τ.1 i) _).1 hc
    have d2 := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F (ik k) P p (ik k) P' (Matrix.mulVecLin V) p'
      hex _ _).1 d1
    have tn := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F (ik k) P' p'
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 (hd' τ.1 i)
  have hs : ∀ (i j : Fin (Dw.mult τ.1)),
      (Pi.single (e.symm ⟨τ.1, i⟩) 1 : Fin g → ℂ) (e.symm ⟨τ.1, j⟩) = (Pi.single i 1 : _ → ℂ) j := by
    intro i j
    simp [Pi.single_apply]
  have hdet := det_mul_eq_one (hm _ hτ) (B ⟨_, hτ⟩) (show Matrix _ _ ℂ from cf τ.1) fun i => by
    funext j
    rw [← hs, ← hcol, hV, hK _ hτ]
    congr 2
    funext j'
    refine (?_ : ∀ w : Fin (Dw.mult τ.1) → ℂ,
      w j' = (∑ j, w j • (Pi.single (e.symm ⟨τ.1, j⟩) 1 : Fin g → ℂ)) (e.symm ⟨τ.1, j'⟩)) (cf τ.1 i)
    intro w
    simp only [Finset.sum_apply, Pi.smul_apply, hs, smul_eq_mul]
    simp [Pi.single_apply]
  have hx' := (x'.2 ⟨_, hτ⟩).1
  simp only [B, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hdet
  change _ = Matrix.det (show Matrix _ _ ℂ from cf τ.1) * _
  field_simp at hdet
  linear_combination -hdet

end GlobalTheory.FlatChange
