import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.CoreSelfDual

variable {D : D7}

theorem form_eq (S : HSp D) (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem wittHyperbolicRankZero_proj_mul_emb (y : Fin S₀.rank → D.host.E) : d.q0 *ᵥ (d.i₀ *ᵥ y) = y := by
  have hq : d.q0 * d.i₀ = 1 := by
    calc d.q0 * d.i₀ = S₀.gram⁻¹ * (d.i₀ᴴ * S.gram * d.i₀) := by
          simp only [HypDec.q0, Matrix.mul_assoc]
      _ = 1 := by rw [d.iso]; exact Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det S₀)
  rw [Matrix.mulVec_mulVec, hq, Matrix.one_mulVec]

theorem wittCoreProjection_adjoint_coreEmbedding (x : Fin S.rank → D.host.E) (y : Fin S₀.rank → D.host.E) :
    star (d.q0 *ᵥ x) ⬝ᵥ S₀.gram *ᵥ y = star x ⬝ᵥ S.gram *ᵥ (d.i₀ *ᵥ y) := by
  have hM : d.q0ᴴ * S₀.gram = S.gram * d.i₀ := by
    simp only [HypDec.q0, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      GlobalTheory.MixModel.gram_conjTranspose, GlobalTheory.MixModel.gramInv_conjTranspose, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det S₀), Matrix.mul_one]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, hM]

theorem isSelfDualC_comap {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hΛ : IsSelfDualC S Λ)
    (hP : ∀ x ∈ Λ, d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ Λ) :
    IsSelfDualC S₀ (Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))) := by
  unfold IsSelfDualC at hΛ ⊢
  obtain ⟨hlat, hdual⟩ := hΛ
  have hq : ∀ y, d.q0 *ᵥ (d.i₀ *ᵥ y) = y := GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb d
  have hmem : ∀ y, y ∈ Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ↔ d.i₀ *ᵥ y ∈ Λ :=
    fun y => Iff.rfl
  have heq : Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) =
      Λ.map ((Matrix.mulVecLin d.q0).restrictScalars (𝓞 D.host.E)) := by
    ext y
    rw [hmem, Submodule.mem_map]
    constructor
    · intro hy
      exact ⟨_, hy, hq y⟩
    · rintro ⟨x, hx, rfl⟩
      exact hP x hx
  refine ⟨?_, fun y => ?_⟩
  · rw [heq]
    refine ⟨hlat.fg.map _, ?_⟩
    rw [Submodule.map_coe]
    change Submodule.span D.host.E ((Matrix.mulVecLin d.q0) '' (Λ : Set (Fin S.rank → D.host.E))) = ⊤
    rw [Submodule.span_image, hlat.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact fun y => ⟨d.i₀ *ᵥ y, hq y⟩
  · rw [hmem]
    constructor
    · intro hy x hx
      rw [hmem] at hx
      obtain ⟨b, hb⟩ := (hdual (d.i₀ *ᵥ y)).1 hy (d.i₀ *ᵥ x) hx
      refine ⟨b, ?_⟩
      rw [hb, GlobalTheory.AscFin.CoreSelfDual.form_eq, GlobalTheory.AscFin.CoreSelfDual.form_eq, ← d.iso,
        Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · intro hy
      refine (hdual (d.i₀ *ᵥ y)).2 fun w hw => ?_
      obtain ⟨b, hb⟩ := hy (d.q0 *ᵥ w) (hP w hw)
      refine ⟨b, ?_⟩
      rw [hb, GlobalTheory.AscFin.CoreSelfDual.form_eq, GlobalTheory.AscFin.CoreSelfDual.form_eq,
        GlobalTheory.AscFin.CoreSelfDual.wittCoreProjection_adjoint_coreEmbedding]

theorem mulVec_col_eq_zero {n k c r : ℕ} {q : Matrix (Fin k) (Fin n) D.host.E} {a : Matrix (Fin n) (Fin c) D.host.E}
    {f : Fin r → Fin c} {s : Fin r → D.host.E} (h : q * colsOf a f s = 0) {p : Fin r} (hs : s p ≠ 0) :
    q *ᵥ (fun i => a i (f p)) = 0 := by
  funext i
  have h1 := congrFun (congrFun h i) p
  simp only [Matrix.mul_apply, colsOf, Matrix.zero_apply] at h1
  have h2 : s p * (q *ᵥ (fun i => a i (f p))) i = 0 := by
    rw [← h1]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  exact (mul_eq_zero.mp h2).resolve_left hs

theorem wittCoreProjection_kills_offMiddle_auxiliaryVectors {A : HSp D} {c : ℕ} (a : HermitianOrthogonalExtensionData A S c (-1)) (h : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ + 1) (p : Fin c) (hp : p.1 ≠ ρ) :
    d.q0 *ᵥ (fun i => a.a i p) = 0 := by
  subst hc
  obtain ⟨h2, he, s, he'⟩ := h
  have hqe : d.q0 * d.e = 0 := by
    simp only [HypDec.q0, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc d.i₀ᴴ, d.i₀e, Matrix.mul_zero]
  have hqe' : d.q0 * d.e' = 0 := by
    simp only [HypDec.q0, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc d.i₀ᴴ, d.i₀e', Matrix.mul_zero]
  rw [he] at hqe
  rw [he'] at hqe'
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · have := GlobalTheory.AscFin.CoreSelfDual.mulVec_col_eq_zero hqe (p := ⟨p.1, hlt⟩) (pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero))
    rw [show p = Fin.castLE (by omega) (⟨p.1, hlt⟩ : Fin ρ) from Fin.ext rfl]
    exact this
  · have hk : 2 * ρ - p.1 < ρ := by omega
    have hsk : s ⟨2 * ρ - p.1, hk⟩ ≠ 0 := by
      intro h0
      have h1 := congrFun (congrFun d.e'e ⟨2 * ρ - p.1, hk⟩) ⟨2 * ρ - p.1, hk⟩
      rw [he'] at h1
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, colsOf, h0] at h1
    have := GlobalTheory.AscFin.CoreSelfDual.mulVec_col_eq_zero hqe' hsk
    rw [show p = (Fin.castLE (by omega) (⟨2 * ρ - p.1, hk⟩ : Fin ρ) : Fin (2 * ρ + 1)).rev from
      Fin.ext (by simp only [Fin.val_rev, Fin.coe_castLE]; omega)]
    exact this

private theorem mulVec_eq_sum_smul_col {R : Type} [CommRing R] {n c : ℕ} (M : Matrix (Fin n) (Fin c) R) (u : Fin c → R) :
    M *ᵥ u = ∑ p, u p • (fun i => M i p) := by
  funext i
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem proj_mem {A : HSp D} {c : ℕ} (a : HermitianOrthogonalExtensionData A S c (-1)) (h : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ + 1)
    {N : Matrix (Fin S₀.rank) (Fin A.rank) D.host.E} (hN : d.i₀ * N = frameMat S A a.ι) {z : Fin S₀.rank → D.host.E}
    (hz : d.i₀ *ᵥ z = fun i => a.a i ⟨ρ, by omega⟩) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : Fin S.rank → D.host.E} (hx : x ∈ a.lat Λ 𝔟) :
    d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ a.lat Λ 𝔟 := by
  obtain ⟨y, hy, u, hu, rfl⟩ := hx
  have hcol : ∀ p : Fin c, d.q0 *ᵥ (fun i => a.a i p) =
      if p = (⟨ρ, by omega⟩ : Fin c) then z else 0 := by
    intro p
    split_ifs with hp
    · have hpz : (fun i => a.a i p) = d.i₀ *ᵥ z := by rw [hz, hp]
      rw [hpz, GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb]
    · exact GlobalTheory.AscFin.CoreSelfDual.wittCoreProjection_kills_offMiddle_auxiliaryVectors d a h hc p (fun e => hp (Fin.ext e))
  have h1 : d.i₀ *ᵥ (d.q0 *ᵥ (frameMat S A a.ι *ᵥ y)) = frameMat S A a.ι *ᵥ y := by
    rw [← hN, ← Matrix.mulVec_mulVec, GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb]
  have h2 : d.q0 *ᵥ (a.a *ᵥ u) = u ⟨ρ, by omega⟩ • z := by
    rw [mulVec_eq_sum_smul_col a.a u, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hcol, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  show ∃ y' ∈ Λ, ∃ u' : Fin c → D.host.E, (∀ p, u' p ∈ 𝔟 p) ∧
    d.i₀ *ᵥ (d.q0 *ᵥ (frameMat S A a.ι *ᵥ y + a.a *ᵥ u)) = frameMat S A a.ι *ᵥ y' + a.a *ᵥ u'
  refine ⟨y, hy, fun p => if p = (⟨ρ, by omega⟩ : Fin c) then u p else 0, fun p => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hu p
    · exact (𝔟 p).zero_mem
  · rw [Matrix.mulVec_add, Matrix.mulVec_add, h1, h2, Matrix.mulVec_smul, hz, mulVec_eq_sum_smul_col a.a]
    congr 1
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.AscFin.CoreSelfDual

namespace GlobalTheory.AscFin

theorem isSelfDualC_lat0 {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G) (hF : Std F)
    (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := by
  have h1 : 1 ≤ 2 * ρ + 2 := by omega
  have e : G.Λ (.grid (2 * ρ + 2) 0) =
      (G.colDec (2 * ρ + 2) h1 h).lat (G.Λ (.core (2 * ρ + 2))) (stairId _ _ _) :=
    G.sp.colLat (2 * ρ + 2) h1 h
  have hc : 2 * ρ + 2 - 1 = 2 * ρ + 1 := by omega
  show IsSelfDualC (F.V₀ ρ) ((G.Λ (.grid (2 * ρ + 2) 0)).comap
    ((Matrix.mulVecLin (F.dB ρ h).i₀).restrictScalars (𝓞 D.host.E)))
  refine CoreSelfDual.isSelfDualC_comap (F.dB ρ h) (G.sp.V_is (2 * ρ + 2) 0 h1 h (Nat.zero_le _)).sd ?_
  intro x hx
  rw [e] at hx ⊢
  refine CoreSelfDual.proj_mem (F.dB ρ h) _ (hF.hB ρ h) hc (N := (F.oB ρ h).iA) (hF.aB ρ h)
    (z := (F.oB ρ h).iB *ᵥ F.ζ 0) ?_ hx
  rw [Matrix.mulVec_mulVec]
  exact hF.zB' ρ h

end GlobalTheory.AscFin

end
