import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iA {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem coreMat_iB {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = midCol d h := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem besselDecomposition_vector_eq {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (a : D.host.E) :
    (besDec d h).i₀ *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => a) =
      a • (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z := by
  show coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, coreMat_iB]
  show midCol d h *ᵥ (fun _ : Fin 1 => a) = _
  funext k
  simp [midCol, Matrix.mulVec, dotProduct, HermitianOrthogonalExtensionData.besDat, mul_comm]

theorem ratV_smul' {n : ℕ} (a : D.host.E) (v : Fin n → D.host.E) : ratV (a • v) = incA D a • ratV v := by
  funext i
  simp [ratV]

section Diag

variable {S S₀ : HSp D} {σ : ℕ} (d1 : HypDec S S₀ σ) (l : Fin σ → D.host.E)

theorem diagI_mul (hl : ∀ a, l a ≠ 0) :
    (diagonal fun a => incA D (l a)) ⬝ (diagonal fun a => incA D (l a)⁻¹) = (1 : Mx D σ σ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a
  rw [← map_mul, mul_inv_cancel₀ (hl a), map_one]

theorem diagI_mul' (hl : ∀ a, l a ≠ 0) :
    (diagonal fun a => incA D (l a)⁻¹) ⬝ (diagonal fun a => incA D (l a)) = (1 : Mx D σ σ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a
  rw [← map_mul, inv_mul_cancel₀ (hl a), map_one]

variable (hl : ∀ a, l a ≠ 0)

theorem jX_diag : (diagDec d1 l hl).jX = d1.jX ⬝ diagonal fun a => incA D (l a) := by
  show rat (d1.e * diagonal l) = _
  rw [rat_mul]; congr 1; exact diagonal_map (map_zero _)

theorem pX_diag_jX : (diagDec d1 l hl).pX ⬝ d1.jX = diagonal fun a => incA D (l a)⁻¹ := by
  have e := (diagDec d1 l hl).pX_jX
  rw [jX_diag, ← Matrix.mul_assoc] at e
  calc (diagDec d1 l hl).pX ⬝ d1.jX
        = (diagDec d1 l hl).pX ⬝ d1.jX ⬝ (diagonal fun a => incA D (l a)) ⬝ (diagonal fun a => incA D (l a)⁻¹) := by
          rw [Matrix.mul_assoc ((diagDec d1 l hl).pX ⬝ d1.jX), diagI_mul l hl, Matrix.mul_one]
    _ = _ := by rw [e, Matrix.one_mul]

theorem blockX_diag (n : GA D S) (T : Mx D σ σ) (e1 : mt S n ⬝ d1.jX = d1.jX + d1.jX ⬝ T) :
    blockX (diagDec d1 l hl) n =
      1 + (diagonal fun a => incA D (l a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (l a)) := by
  rw [blockX, jX_diag, ← Matrix.mul_assoc (mt S n), e1, Matrix.add_mul, Matrix.mul_add]
  simp only [← Matrix.mul_assoc]
  rw [pX_diag_jX, diagI_mul' l hl]

theorem coefX_diag (n : GA D S) (z z₀ : Fin S₀.rank → D.host.E) (w : Fin S.rank → D.host.E) (a : D.host.E)
    (b : Fin σ → AE D) (hw : d1.i₀ *ᵥ z₀ = w) (hz : d1.i₀ *ᵥ z = a • w)
    (e2 : mt S n *ᵥ ratV w = ratV w + d1.jX *ᵥ b) :
    coefX (diagDec d1 l hl) z n = incA D a • ((diagonal fun a => incA D (l a)⁻¹) *ᵥ b) := by
  have hzs : (diagDec d1 l hl).j0 *ᵥ ratV z = incA D a • ratV w := by
    rw [HypDec.j0, ← ratV_mulVec]
    show ratV (d1.i₀ *ᵥ z) = _
    rw [hz, ratV_smul']
  have hw' : ratV w = (diagDec d1 l hl).j0 *ᵥ ratV z₀ := by
    rw [HypDec.j0, ← ratV_mulVec]
    show ratV w = ratV (d1.i₀ *ᵥ z₀)
    rw [hw]
  rw [coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzs, Matrix.mulVec_smul, e2, Matrix.mulVec_smul,
    Matrix.mulVec_add, hw', Matrix.mulVec_mulVec, (diagDec d1 l hl).pX_j0, Matrix.zero_mulVec, zero_add,
    Matrix.mulVec_mulVec, pX_diag_jX]

end Diag

theorem incA_inv_mul_pow (i : ℕ) :
    incA D (D.host.xi0 ^ i)⁻¹ * incA D (D.host.xi0 ^ (i + 1)) = incA D D.host.xi0 := by
  rw [← map_mul, pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)), one_mul]

theorem up_sum {σ : ℕ} (T : Mx D σ σ) :
    upSum ((diagonal fun a => incA D (lam σ a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (lam σ a))) =
      ∑ i : Fin σ, ∑ j : Fin σ, if j.1 = i.1 + 1 then incA D D.host.xi0 * T i j else 0 := by
  simp only [upSum, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · have e := incA_inv_mul_pow (D := D) i
    rw [show lam (D := D) σ j = D.host.xi0 ^ ((i : ℕ) + 1) by rw [lam, hij],
      show lam (D := D) σ i = D.host.xi0 ^ (i : ℕ) from rfl]
    linear_combination T i j * e
  · rfl

theorem ell_sum {σ : ℕ} (b : Fin σ → AE D) :
    ell D σ ⬝ᵥ (incA D (D.host.xi0 ^ σ) • ((diagonal fun a => incA D (lam σ a)⁻¹) *ᵥ b)) =
      ∑ i : Fin σ, if i.1 + 1 = σ then incA D D.host.xi0 * b i else 0 := by
  simp only [ell, dotProduct, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have e := incA_inv_mul_pow (D := D) i
    rw [hi] at e
    calc (1 : AE D) * (incA D (D.host.xi0 ^ σ) * (incA D (lam σ i)⁻¹ * b i))
        = (incA D (D.host.xi0 ^ (i : ℕ))⁻¹ * incA D (D.host.xi0 ^ σ)) * b i := by
          rw [one_mul, ← mul_assoc, mul_comm (incA D (D.host.xi0 ^ σ))]; rfl
      _ = incA D D.host.xi0 * b i := by rw [e]
  · exact zero_mul _

theorem simpleSum_lam {σ : ℕ} (T : Mx D σ σ) (b : Fin σ → AE D) :
    upSum (1 + (diagonal fun a => incA D (lam σ a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (lam σ a))) +
        ell D σ ⬝ᵥ (incA D (D.host.xi0 ^ σ) • ((diagonal fun a => incA D (lam σ a)⁻¹) *ᵥ b)) =
      GlobalTheory.BesselChar.superSum (fun _ => incA D D.host.xi0) T b := by
  rw [upSum_add, upSum_one, zero_add, up_sum, ell_sum]
  rfl

theorem psiBes_diag (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1)
    (n : GA D B) (hn : n ∈ NFlag B ((besDec d h).e * diagonal (lam σ))) :
    psiBes ψ (diagDec (besDec d h) (lam σ) (lam_ne σ)) 1
      (vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ) n =
      besChar ψ (d.besDat (neg_ne_zero.2 one_ne_zero) σ h) n := by
  have hn' : n ∈ NFlag B (besDec d h).e := (nFlag_diag _ (lam σ) (lam_ne σ)) ▸ hn
  obtain ⟨T, b, -, h1, h2⟩ : ∃ (T : Mx D σ σ) (b : Fin σ → AE D), GlobalTheory.BesselChar.StrictUp T ∧
      mt B n ⬝ (besDec d h).jX = (besDec d h).jX + (besDec d h).jX ⬝ T ∧
      mt B n *ᵥ ratV (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z =
        ratV (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z + (besDec d h).jX *ᵥ b :=
    GlobalTheory.BesselChar.exists_coords (d.besDat (neg_ne_zero.2 one_ne_zero) σ h) n hn'
  rw [GlobalTheory.BesselChar.besChar_eq ψ _ n T b h1 h2]
  rw [psiBes, simpleSum, blockX_diag _ _ _ n T h1,
    coefX_diag _ _ _ n _ _ _ _ b (by rw [besselDecomposition_vector_eq d h 1, one_smul]) (besselDecomposition_vector_eq d h _) h2,
    simpleSum_lam, map_one, one_mul, psiE]
  rfl

theorem integral_tr {S : HSp D} {N N' : Subgroup (GA D S)} (hN : N = N') (ν : Measure N) (𝓝 : Set N)
    (f : GA D S → ℂ) : ∫ n in trSet hN 𝓝, f n.1 ∂(trMeas hN ν) = ∫ n in 𝓝, f n.1 ∂ν := by
  subst hN
  rfl

end GlobalTheory.RowChain.TopPer

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem embA_top (G : GridData L sc) (h : GA D (G.V (.top 0))) :
    GlobalTheory.MixPer.embA (besDecAt G 0 ((D.R.m - 2) / 2) top_idx) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) h = embTop G h :=
  (embRel_iff _ h _).1 (GlobalTheory.CharLaws.embRel_embA _ _ _ (coreMat_iA _ _).symm h)

end GlobalTheory.RowChain.TopPer

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem embA_topLev (G : GridData L sc) {t : T} {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (h : GA D (G.V (.top 0))) :
    GlobalTheory.MixPer.embA (topLev G hM).d (topLev G hM).o h = embTop G h :=
  embA_top G h

theorem psiBes_topLev (G : GridData L sc) {t : T} {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (ψ : AddChar (AF D.host.F) ℂ)
    (n : GA D (G.V (.grid D.R.m 0))) (hn : n ∈ flagN (topLev G hM).d) :
    psiBes ψ (topLev G hM).d 1 (vecB (topLev G hM).o (topLev G hM).ζ) n = besChar ψ G.besTop n :=
  psiBes_diag ψ (G.rowDec 0 (by have := D.R.two_le_m; omega)) (by have := top_idx (D := D); omega) n hn

theorem bplus_eq_topLev_per : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    (M : GlobalTheory.FunObj.Vol G) (hM : M.Is t) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)),
    Bplus Wl M φ F = (GlobalTheory.RowChain.topLev G hM).per Wl.ψ φ F := by
  intro D T L sc G Wl t M hM φ F
  have hN : NFlag (G.V (.grid D.R.m 0)) G.besTop.e = flagN (topLev G hM).d :=
    (nFlag_diag (rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2)
      (by have := top_idx (D := D); omega)).e (lam _) (lam_ne _)).symm
  have hper : (topLev G hM).per Wl.ψ φ F = ∫ h in M.fd (.top 0), ∫ n in trSet hN M.fdN,
      GlobalTheory.MixPer.besFun Wl.ψ 1 (topLev G hM).d (topLev G hM).o (topLev G hM).ζ φ F h n ∂(trMeas hN M.νN) ∂M.ν (.top 0) :=
    rfl
  rw [hper]
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  refine (integral_tr hN M.νN M.fdN fun g => φ h * F (g * embTop G h) * star (besChar Wl.ψ G.besTop g)).symm.trans ?_
  refine integral_congr_ae (ae_of_all _ fun n => ?_)
  show φ h * F (n.1 * embTop G h) * star (besChar Wl.ψ G.besTop n.1) =
    φ h * F ((show GA D (topLev G hM).V from n.1) * GlobalTheory.MixPer.embA (topLev G hM).d (topLev G hM).o h) *
      star (psiBes Wl.ψ (topLev G hM).d 1 (vecB (topLev G hM).o (topLev G hM).ζ) n.1)
  rw [embA_topLev G hM h, psiBes_topLev G hM Wl.ψ n.1 n.2]
  rfl

end GlobalTheory.RowChain.TopPer
