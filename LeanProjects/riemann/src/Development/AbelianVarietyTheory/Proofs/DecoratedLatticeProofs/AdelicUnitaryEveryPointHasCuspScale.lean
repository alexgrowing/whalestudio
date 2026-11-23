import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictioStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointNearCuspScaleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasBrg
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CuspGeo

open Formalism.IndefR.Eqv

theorem norm_mul_mul_apply_le {n : ℕ} (P A Q : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hA : ∀ k l, ‖A k l‖ ≤ c)
    (i j : Fin n) : ‖(P * A * Q) i j‖ ≤ (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
  simp only [Matrix.mul_apply]
  calc ‖∑ l, (∑ k, P i k * A k l) * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * c * ‖Q l j‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul, ← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hA k l) (norm_nonneg _)
    _ = (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
        rw [Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem norm_uMat_inv_apply {n : ℕ} {ε : Fin n → Bool} (y : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖uMat y⁻¹ i j‖ = ‖uMat y j i‖ := by
  have hy : (uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y = Formalism.REAL.Jm ε := y.2
  have h1 : uMat y⁻¹ = Formalism.REAL.Jm ε * (uMat y)ᴴ * Formalism.REAL.Jm ε := by
    show (((y : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
    refine Units.inv_eq_of_mul_eq_one_left ?_
    calc Formalism.REAL.Jm ε * (uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y
        = Formalism.REAL.Jm ε * ((uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]
  rw [h1]
  by_cases hi : ε i <;> by_cases hj : ε j <;>
    simp [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hi, hj]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

def frameBound (fr : UI.Frames D V) (τ : D.what₂.Tau) (i j : Fin V.rank) : ℝ :=
  ∑ k, ∑ l, ‖fr.P (Formalism.L2.Host.tauPl D τ) i k‖ * ‖(fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ l j‖

theorem frameBound_nonneg (fr : UI.Frames D V) (τ : D.what₂.Tau) (i j : Fin V.rank) : 0 ≤ frameBound fr τ i j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

def brgFin (fr : UI.Frames D V) : (UI.instV fr).Gf →* GA D V :=
  (UI.brg fr : (UI.instV fr).GA →* GA D V).comp (MonoidHom.inr _ _)

theorem brgFin_apply (fr : UI.Frames D V) (k : (UI.instV fr).Gf) : brgFin fr k = UI.brg fr (1, k) := rfl

theorem continuous_brgFin (fr : UI.Frames D V) : Continuous (brgFin fr) :=
  (UI.brg fr).continuous.comp (continuous_const.prodMk continuous_id)

theorem brg_entry_bounds (fr : UI.Frames D V)
    (h2 : ∀ (x : (UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (UI.brg fr x) =
        fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (y : (UI.instV fr).Ginf) (c : ℝ),
      ((∀ v i j, ‖uMat (y v) i j‖ ≤ c) → normInf θ V (UI.brg fr (y, 1)) ≤ S * c) ∧
      ((∀ v i j, ‖(uMat (y v) - 1) i j‖ ≤ c) →
        ∀ τ i j, ‖(infMat D.sp.cm.sig V.gram (θ τ) (UI.brg fr (y, 1)) - 1) i j‖ ≤ S * c) := by
  have hle : ∀ τ i j, frameBound fr τ i j ≤ ∑ τ, ∑ i, ∑ j, 2 * frameBound fr τ i j := fun τ i j => by
    have h0 := frameBound_nonneg fr
    calc frameBound fr τ i j ≤ 2 * frameBound fr τ i j := by linarith [h0 τ i j]
      _ ≤ ∑ j', 2 * frameBound fr τ i j' :=
          Finset.single_le_sum (f := fun j' => 2 * frameBound fr τ i j') (fun j' _ => by linarith [h0 τ i j'])
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', 2 * frameBound fr τ i' j' :=
          Finset.single_le_sum (f := fun i' => ∑ j', 2 * frameBound fr τ i' j')
            (fun i' _ => Finset.sum_nonneg fun j' _ => by linarith [h0 τ i' j']) (Finset.mem_univ i)
      _ ≤ _ :=
          Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', 2 * frameBound fr τ' i' j')
            (fun τ' _ => Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => by linarith [h0 τ' i' j'])
            (Finset.mem_univ τ)
  refine ⟨∑ τ, ∑ i, ∑ j, 2 * frameBound fr τ i j,
    Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg zero_le_two (frameBound_nonneg fr τ i j), fun y c => ⟨fun hc => ?_, fun hc τ i j => ?_⟩⟩
  · unfold normInf
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have e1 := norm_mul_mul_apply_le (fr.P (Formalism.L2.Host.tauPl D τ))
      (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ c (fun k l => hc (Formalism.L2.Host.tauPl D τ) k l) i j
    have e2 := norm_mul_mul_apply_le (fr.P (Formalism.L2.Host.tauPl D τ))
      (uMat ((y (Formalism.L2.Host.tauPl D τ))⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ c
      (fun k l => (norm_uMat_inv_apply _ k l).trans_le (hc _ l k)) i j
    rw [← map_inv, h2 _ τ (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl,
      h2 _ τ (uMat ((y (Formalism.L2.Host.tauPl D τ))⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl]
    unfold frameBound
    linarith
  · have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc (Formalism.L2.Host.tauPl D τ) i j)
    have hdet : IsUnit (fr.P (Formalism.L2.Host.tauPl D τ)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit (Formalism.L2.Host.tauPl D τ))
    rw [h2 _ τ (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl]
    have e : fr.P (Formalism.L2.Host.tauPl D τ) * (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) *
        (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ - 1 = fr.P (Formalism.L2.Host.tauPl D τ) *
        ((uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) - 1) *
        (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hdet]
    rw [e]
    exact (norm_mul_mul_apply_le _ _ _ c (hc _) i j).trans (mul_le_mul_of_nonneg_right (hle τ i j) hc0)

theorem near (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) :
    Near θ V := by
  intro U hU
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.unitaryGroup_twoModels_rationalReal_unipotent_dictionary D θ hθ V (UI.framesV D V)
  obtain ⟨S, hS0, hS⟩ := brg_entry_bounds (θ := θ) (UI.framesV D V) h2
  obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow (θ := θ) V hθ
  have hKp : IsOpen ((U.comap (brgFin (UI.framesV D V)) : Subgroup _) : Set (UI.instV (UI.framesV D V)).Gf) :=
    hU.preimage (continuous_brgFin _)
  obtain ⟨b, C, δ₀, K, hδ₀, hK, hx⟩ := GlobalTheory.T.adelicPoint_nearCusp_scale (UI.instV (UI.framesV D V)) _ hKp
  obtain ⟨Ck, hCk⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V (hK.image (continuous_brgFin (UI.framesV D V)))
  refine ⟨b * d, max (Ck * (S * C) ^ d) (S * C), δ₀, hδ₀, fun g => ?_⟩
  set fr := UI.framesV D V with hfr
  set x := (UI.brg fr).symm g with hxdef
  have hgx : UI.brg fr x = g := (UI.brg fr).apply_symm_apply g
  obtain ⟨δ, hδ, hδ1, ⟨γ, hγ, hγK, hγb⟩, halt⟩ := hx x
  refine ⟨δ, hδ, hδ1, ?_, ?_⟩
  · have hsplit : γ * x = ((γ * x).1, 1) * (1, (γ * x).2) := Prod.ext (by simp) (by simp)
    have e : UI.brg fr γ * g = UI.brg fr ((γ * x).1, 1) * brgFin fr (γ * x).2 := by
      calc UI.brg fr γ * g = UI.brg fr (γ * x) := by rw [map_mul, hgx]
        _ = UI.brg fr (((γ * x).1, 1) * (1, (γ * x).2)) := congrArg _ hsplit
        _ = _ := map_mul _ _ _
    have hkb := hCk _ ⟨_, hγK, rfl⟩
    have hq : GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * Ck := by
      have := GlobalTheory.Grow.quotHeight_le V g ((h1 γ).2 hγ)
      rw [e] at this
      exact this.trans ((GlobalTheory.Grow.height_mul_le V _ _).trans
        (mul_le_mul_of_nonneg_left hkb (GlobalTheory.Grow.height_pos V _).le))
    have hy : ∀ v i j, ‖uMat ((γ * x).1 v) i j‖ ≤ C / δ ^ b := fun v i j =>
      (le_div_iff₀ (pow_pos hδ b)).2 (hγb v i j)
    have hN := (hS (γ * x).1 (C / δ ^ b)).1 hy
    have hN0 : 0 ≤ normInf θ V (UI.brg fr ((γ * x).1, 1)) := by unfold normInf; positivity
    have hNb : normInf θ V (UI.brg fr ((γ * x).1, 1)) * δ ^ b ≤ S * C := by
      calc _ ≤ S * (C / δ ^ b) * δ ^ b := mul_le_mul_of_nonneg_right hN (pow_pos hδ b).le
        _ = S * C := by rw [mul_assoc, div_mul_cancel₀ _ (pow_pos hδ b).ne']
    have hH := hd _ ((brg_mem_GinfC fr ((γ * x).1, 1)).2 rfl)
    have hHb : GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * δ ^ (b * d) ≤ (S * C) ^ d := by
      rw [pow_mul]
      calc _ ≤ normInf θ V (UI.brg fr ((γ * x).1, 1)) ^ d * (δ ^ b) ^ d :=
            mul_le_mul_of_nonneg_right hH (by positivity)
        _ = (normInf θ V (UI.brg fr ((γ * x).1, 1)) * δ ^ b) ^ d := (mul_pow _ _ _).symm
        _ ≤ (S * C) ^ d := pow_le_pow_left₀ (by positivity) hNb d
    have hCk0 : 0 ≤ Ck := zero_le_one.trans ((GlobalTheory.Grow.one_le_height V _).trans hkb)
    calc GlobalTheory.Grow.quotHeight V g * δ ^ (b * d)
        ≤ GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * Ck * δ ^ (b * d) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = Ck * (GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * δ ^ (b * d)) := by ring
      _ ≤ Ck * (S * C) ^ d := mul_le_mul_of_nonneg_left hHb hCk0
      _ ≤ _ := le_max_left _ _
  · rcases halt with h | ⟨W, hW, hWm⟩
    · exact Or.inl h
    · obtain ⟨r, C₀, hC₀, hNI⟩ := h3 W hW
      refine Or.inr ⟨r, C₀, hC₀, fun m hm => ?_⟩
      have hm' : (UI.brg fr).symm m ∈ (UI.instV fr).NA W :=
        hNI _ (by rwa [(UI.brg fr).apply_symm_apply])
      obtain ⟨γ', hγ', u, k, hk, he, hu⟩ := hWm _ hm'
      refine ⟨UI.brg fr γ', (h1 γ').2 hγ', UI.brg fr (u, 1), brgFin fr k,
        ⟨(brg_mem_GinfC fr (u, 1)).2 rfl, fun τ i j => ?_⟩, hk, (brg_mem_GfC fr (1, k)).2 rfl, ?_⟩
      · calc _ ≤ S * (C * δ) := (hS u (C * δ)).2 hu τ i j
          _ ≤ max (Ck * (S * C) ^ d) (S * C) * δ := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le
      · calc m * g = UI.brg fr ((UI.brg fr).symm m * x) := by rw [map_mul, (UI.brg fr).apply_symm_apply, hgx]
          _ = UI.brg fr (γ' * x * ((u, 1) * (1, k))) := by
            rw [he]; exact congrArg (fun z => UI.brg fr (γ' * x * z)) (Prod.ext (by simp) (by simp))
          _ = UI.brg fr γ' * g * UI.brg fr (u, 1) * brgFin fr k := by
            rw [map_mul, map_mul, map_mul, hgx, ← mul_assoc]; rfl

end GlobalTheory.CuspGeo
