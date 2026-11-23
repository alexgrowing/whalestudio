import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesPerHaarScale

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.EndsPf.Chr

open GlobalTheory.RowChain

variable {D : D7}

theorem ratV_smul' {n : ℕ} (a : D.host.E) (v : Fin n → D.host.E) : ratV (a • v) = incA D a • ratV v := by
  funext i
  simp [ratV]

section Diag

variable {σ : ℕ} (l : Fin σ → D.host.E)

theorem diagI_mul (hl : ∀ a, l a ≠ 0) :
    (diagonal fun a => incA D (l a)) ⬝ (diagonal fun a => incA D (l a)⁻¹) = (1 : Mx D σ σ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a
  rw [← map_mul, mul_inv_cancel₀ (hl a), map_one]

theorem diagI_mul' (hl : ∀ a, l a ≠ 0) :
    (diagonal fun a => incA D (l a)⁻¹) ⬝ (diagonal fun a => incA D (l a)) = (1 : Mx D σ σ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a
  rw [← map_mul, inv_mul_cancel₀ (hl a), map_one]

end Diag

section Gen

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (J : Mx D S.rank ρ) (l : Fin ρ → D.host.E)

theorem pX_J (hl : ∀ a, l a ≠ 0) (hJ : d.jX = J ⬝ diagonal fun a => incA D (l a)) :
    d.pX ⬝ J = diagonal fun a => incA D (l a)⁻¹ := by
  have e := d.pX_jX
  rw [hJ, ← Matrix.mul_assoc] at e
  calc d.pX ⬝ J = d.pX ⬝ J ⬝ (diagonal fun a => incA D (l a)) ⬝ (diagonal fun a => incA D (l a)⁻¹) := by
        rw [Matrix.mul_assoc (d.pX ⬝ J), diagI_mul l hl, Matrix.mul_one]
    _ = _ := by rw [e, Matrix.one_mul]

theorem blockX_J (hl : ∀ a, l a ≠ 0) (hJ : d.jX = J ⬝ diagonal fun a => incA D (l a)) (n : GA D S) (T : Mx D ρ ρ)
    (e1 : mt S n ⬝ J = J + J ⬝ T) :
    blockX d n = 1 + (diagonal fun a => incA D (l a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (l a)) := by
  rw [blockX, hJ, ← Matrix.mul_assoc (mt S n), e1, Matrix.add_mul, Matrix.mul_add]
  simp only [← Matrix.mul_assoc]
  rw [pX_J d J l hl hJ, diagI_mul' l hl]

theorem coefX_J (hl : ∀ a, l a ≠ 0) (hJ : d.jX = J ⬝ diagonal fun a => incA D (l a)) (n : GA D S)
    (z : Fin S₀.rank → D.host.E) (w : Fin S.rank → D.host.E) (t : D.host.E) (b : Fin ρ → AE D)
    (hz : d.i₀ *ᵥ z = t • w) (e2 : mt S n *ᵥ ratV w = ratV w + J *ᵥ b) :
    coefX d z n = incA D t • ((diagonal fun a => incA D (l a)⁻¹) *ᵥ b) := by
  have hzs : d.j0 *ᵥ ratV z = incA D t • ratV w := by
    rw [HypDec.j0, ← ratV_mulVec, hz, ratV_smul']
  rw [coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzs, Matrix.mulVec_smul, e2, smul_add, ← hzs,
    Matrix.mulVec_add, Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec, zero_add, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, pX_J d J l hl hJ]

end Gen

theorem neg_hermitianTraceZeroElement_ne_zero : -D.host.xi0 ≠ 0 := neg_ne_zero.2 (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)

theorem neg_pow_ratio (i : ℕ) :
    incA D ((-D.host.xi0) ^ (i + 1))⁻¹ * incA D ((-D.host.xi0) ^ (i + 1 + 1)) = incA D (-D.host.xi0) := by
  rw [← map_mul, pow_succ (-D.host.xi0) (i + 1), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ neg_hermitianTraceZeroElement_ne_zero), one_mul]

theorem upSum_scaled {ρ : ℕ} (T : Mx D ρ ρ) :
    upSum ((diagonal fun a : Fin ρ => incA D ((-D.host.xi0) ^ (a.1 + 1))⁻¹) ⬝ T ⬝
        (diagonal fun a : Fin ρ => incA D ((-D.host.xi0) ^ (a.1 + 1)))) = incA D (-D.host.xi0) * upSum T := by
  simp only [upSum, Matrix.diagonal_mul, Matrix.mul_diagonal, Finset.mul_sum, mul_ite, mul_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [hij]
    have e := neg_pow_ratio (D := D) i.1
    linear_combination T i j * e
  · rfl

theorem ell_scaled {ρ : ℕ} (b : Fin ρ → AE D) :
    ell D ρ ⬝ᵥ (incA D ((-D.host.xi0) ^ (ρ + 1)) • ((diagonal fun a : Fin ρ => incA D ((-D.host.xi0) ^ (a.1 + 1))⁻¹) *ᵥ b)) =
      incA D (-D.host.xi0) * (ell D ρ ⬝ᵥ b) := by
  simp only [ell, dotProduct, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have e := neg_pow_ratio (D := D) i.1
    have hp : (-D.host.xi0) ^ (ρ + 1) = (-D.host.xi0) ^ (i.1 + 1 + 1) := congrArg (fun k => (-D.host.xi0) ^ (k + 1)) hi.symm
    rw [hp]
    linear_combination b i * e
  · ring

theorem star_psi_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) : ψ (-x) = star (ψ x) := by
  have h1 : ‖ψ x‖ = 1 := hψ.1.2.1 x
  have h2 : ψ x * star (ψ x) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ x ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h3.trans h2.symm)

theorem psiE_neg_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : AE D) :
    psiE ψ (-x) = star (psiE ψ x) := by
  unfold psiE
  rewrite [map_neg]
  exact star_psi_neg hψ _

theorem simpleSum_scaled {ρ : ℕ} (T : Mx D ρ ρ) (b : Fin ρ → AE D) :
    upSum (1 + (diagonal fun a : Fin ρ => incA D ((-D.host.xi0) ^ (a.1 + 1))⁻¹) ⬝ T ⬝
        (diagonal fun a : Fin ρ => incA D ((-D.host.xi0) ^ (a.1 + 1)))) +
      ell D ρ ⬝ᵥ (incA D ((-D.host.xi0) ^ (ρ + 1)) •
        ((diagonal fun a : Fin ρ => incA D ((-D.host.xi0) ^ (a.1 + 1))⁻¹) *ᵥ b)) =
      -GlobalTheory.BesselChar.superSum (fun _ => incA D D.host.xi0) T b := by
  rewrite [upSum_add, upSum_one, zero_add, upSum_scaled, ell_scaled, superSum_const, map_neg]
  generalize upSum T = u
  generalize ell D ρ ⬝ᵥ b = v
  generalize incA D D.host.xi0 = s
  ring

theorem psiBes_eq_star_besChar : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {A B S₀ A' Lz : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (hc : c = 2 * ρ + 1) (d : HypDec B S₀ ρ) (o : OrthDec S₀ A' Lz) (ζ : Fin Lz.rank → D.host.E), IsAuxiliaryVectorWittDec a d → (d.i₀ * o.iB) *ᵥ ζ = (-D.host.xi0) ^ (ρ + 1) • (fun k => a.a k ⟨ρ, by omega⟩) → ∀ n ∈ flagN d, psiBes ψ d 1 (vecB o ζ) n = star (besChar ψ (a.besDat (neg_ne_zero.2 one_ne_zero) ρ hc) n) := by
  intro D ψ hψ A B S₀ A' Lz c ρ a hc d o ζ hA hz n hn
  have hl : ∀ p : Fin ρ, (-D.host.xi0) ^ (p.1 + 1) ≠ 0 := fun p => pow_ne_zero _ neg_hermitianTraceZeroElement_ne_zero
  have hde : d.e = a.iso ρ (by omega) * diagonal (fun p : Fin ρ => (-D.host.xi0) ^ (p.1 + 1)) := by
    obtain ⟨hh, he, -⟩ := hA
    rw [he]
    ext i p
    simp only [colsOf, Matrix.mul_diagonal, HermitianOrthogonalExtensionData.iso, Matrix.submatrix_apply, id]
    exact mul_comm _ _
  have hn' : n ∈ NFlag B (a.besDat (neg_ne_zero.2 one_ne_zero) ρ hc).e := by
    have h0 : n ∈ NFlag B d.e := hn
    rw [hde, nFlag_diag _ _ hl] at h0
    exact h0
  obtain ⟨T, b, -, h1, h2⟩ : ∃ (T : Mx D ρ ρ) (b : Fin ρ → AE D), GlobalTheory.BesselChar.StrictUp T ∧
      mt B n ⬝ rat (a.iso ρ (by omega)) = rat (a.iso ρ (by omega)) + rat (a.iso ρ (by omega)) ⬝ T ∧
      mt B n *ᵥ ratV (a.besDat (neg_ne_zero.2 one_ne_zero) ρ hc).z =
        ratV (a.besDat (neg_ne_zero.2 one_ne_zero) ρ hc).z + rat (a.iso ρ (by omega)) *ᵥ b :=
    GlobalTheory.BesselChar.exists_coords (a.besDat (neg_ne_zero.2 one_ne_zero) ρ hc) n hn'
  have hJ : d.jX = rat (a.iso ρ (by omega)) ⬝
      diagonal fun p : Fin ρ => incA D ((-D.host.xi0) ^ (p.1 + 1)) := by
    show rat d.e = _
    rw [hde, rat_mul]; congr 1; exact diagonal_map (map_zero _)
  have hz' : d.i₀ *ᵥ vecB o ζ = (-D.host.xi0) ^ (ρ + 1) • (a.besDat (neg_ne_zero.2 one_ne_zero) ρ hc).z := by
    rw [vecB, Matrix.mulVec_mulVec]; exact hz
  rw [GlobalTheory.BesselChar.besChar_eq ψ _ n T b h1 h2]
  rw [psiBes, simpleSum, blockX_J d _ _ hl hJ n T h1, coefX_J d _ _ hl hJ n _ _ _ b hz' h2,
    simpleSum_scaled, map_one, one_mul, psiE_neg_star hψ, psiE]
  rfl

end GlobalTheory.AscFin.EndsPf.Chr

namespace GlobalTheory.AscFin.EndsPf

theorem integral_tr' {D : D7} {S : HSp D} {N N' : Subgroup (GA D S)} (hN : N = N') (ν : Measure N) (𝓝 : Set N)
    (f : GA D S → ℂ) : ∫ n in GlobalTheory.RowChain.trSet hN 𝓝, f n.1 ∂(GlobalTheory.RowChain.trMeas hN ν) = ∫ n in 𝓝, f n.1 ∂ν := by
  subst hN
  rfl

theorem psi_frame {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {A B S₀ A' Lz : HSp D} {c ρ : ℕ}
    (a : HermitianOrthogonalExtensionData A B c (-1)) (hc : c = 2 * ρ + 1) (d : HypDec B S₀ ρ) (o : OrthDec S₀ A' Lz) (ζ : Fin Lz.rank → D.host.E)
    (hd : IsAuxiliaryVectorWittDec a d) (hz : (d.i₀ * o.iB) *ᵥ ζ = (-D.host.xi0) ^ (ρ + 1) • fun k => a.a k ⟨ρ, by omega⟩) :
    ∀ n ∈ flagN d, psiBes ψ d 1 (vecB o ζ) n = star (besChar ψ (a.besDat (neg_ne_zero.2 one_ne_zero) ρ hc) n) :=
  GlobalTheory.AscFin.EndsPf.Chr.psiBes_eq_star_besChar ψ hψ a hc d o ζ hd hz

theorem per_scale {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {A B : HSp D} {c : ℕ} {ε : D.host.E}
    (a : HermitianOrthogonalExtensionData A B c ε) (dd : BesDat A B a.ι) (hA : GlobalTheory.Unf.CoCpt A) (μ μ' : Measure (GA D A)) (𝓕 𝓕' : Set (GA D A))
    (ν ν' : Measure (NFlag B dd.e)) (𝓝 𝓝' : Set (NFlag B dd.e)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 μ)
    (hμ' : μ'.IsHaarMeasure) (h𝓕' : IsFundamentalDomain (GQ A) 𝓕' μ') (hν : GlobalTheory.Per.IsUnitN B dd.e ν 𝓝)
    (hν' : GlobalTheory.Per.IsUnitN B dd.e ν' 𝓝') (φ : GA D A → ℂ) (F : GA D B → ℂ) (hφ : ∀ γ ∈ GQ A, ∀ g, φ (γ * g) = φ g)
    (hF : ∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) :
    ∃ r : ℝ, 0 < r ∧ GlobalTheory.Per.besPer ψ dd μ 𝓕 ν 𝓝 (stabilizerEmbedding a) φ F = r * GlobalTheory.Per.besPer ψ dd μ' 𝓕' ν' 𝓝' (stabilizerEmbedding a) φ F :=
  GlobalTheory.Per.besPer_haar_scale ψ hψ a dd hA μ μ' 𝓕 𝓕' ν ν' 𝓝 𝓝' hμ h𝓕 hμ' h𝓕' hν hν' φ F hφ hF

section Parts
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem flag_eq (h1 : 1 ≤ D.R.m) (h2 : D.R.m ≤ D.R.m) {V₀ : HSp D} (d : HypDec (G.V (.grid D.R.m 0)) V₀ ((D.R.m - 2) / 2))
    (hd : IsAuxiliaryVectorWittDec (G.colDec D.R.m h1 h2) d) : flagN d = NFlag (G.V (.grid D.R.m 0)) G.besTop.e := by
  obtain ⟨hle, he, -⟩ := hd
  show NFlag _ d.e = NFlag _ ((G.colDec D.R.m h1 h2).iso ((D.R.m - 2) / 2) (by omega))
  rw [he, ← GlobalTheory.RowChain.nFlag_diag ((G.colDec D.R.m h1 h2).iso ((D.R.m - 2) / 2) (by omega))
    (fun p : Fin ((D.R.m - 2) / 2) => (-D.host.xi0) ^ (p.1 + 1))
    (fun _ => pow_ne_zero _ (neg_ne_zero.2 (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)))]
  congr 1
  ext k p
  simp [colsOf, HermitianOrthogonalExtensionData.iso, Matrix.mul_diagonal, mul_comm]

theorem emb_eq (h1 : 1 ≤ D.R.m) (h2 : D.R.m ≤ D.R.m) {V₀ Lz : HSp D} {ρ : ℕ} (d : HypDec (G.V (.grid D.R.m 0)) V₀ ρ)
    (o : OrthDec V₀ (G.V (.core D.R.m)) Lz) (ha : d.i₀ * o.iA = frameMat _ _ (G.colDec D.R.m h1 h2).ι)
    (h : GA D (G.V (.core D.R.m))) : embA d o h = embTop G h :=
  (embRel_iff (G.rowDec 0 (by omega)) h _).1 (GlobalTheory.CharLaws.embRel_embA d o _ ha.symm h)

theorem psi_eq (W : G.Weil) (h1 : 1 ≤ D.R.m) (h2 : D.R.m ≤ D.R.m) {V₀ Lz : HSp D}
    (d : HypDec (G.V (.grid D.R.m 0)) V₀ ((D.R.m - 2) / 2)) (o : OrthDec V₀ (G.V (.core D.R.m)) Lz) (ζ : Fin Lz.rank → D.host.E)
    (hd : IsAuxiliaryVectorWittDec (G.colDec D.R.m h1 h2) d)
    (hz : (d.i₀ * o.iB) *ᵥ ζ = (-D.host.xi0) ^ ((D.R.m - 2) / 2 + 1) • fun k => (G.colDec D.R.m h1 h2).a k ⟨(D.R.m - 2) / 2, by have := D.R.two_le_m; omega⟩) :
    ∀ n ∈ flagN d, psiBes W.ψ d 1 (vecB o ζ) n = star (besChar W.ψ G.besTop n) :=
  psi_frame W.ψ W.ψ_std (G.colDec D.R.m h1 h2) (by have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; omega) d o ζ hd hz

end Parts

section Key
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem per_conj (W : G.Weil) {V₀ Lz : HSp D} {ρ : ℕ} (d : HypDec (G.V (.grid D.R.m 0)) V₀ ρ)
    (o : OrthDec V₀ (G.V (.core D.R.m)) Lz) (ζ : Fin Lz.rank → D.host.E) (hN : flagN d = NFlag (G.V (.grid D.R.m 0)) G.besTop.e)
    (hE : ∀ h, embA d o h = embTop G h)
    (hψ : ∀ n ∈ flagN d, psiBes W.ψ d 1 (vecB o ζ) n = star (besChar W.ψ G.besTop n))
    (μ : Measure (GA D (G.V (.core D.R.m)))) (𝓕 : Set (GA D (G.V (.core D.R.m)))) (ν : Measure (flagN d)) (𝓝 : Set (flagN d))
    (φ : Fn G (.core D.R.m)) (F : Fn G (.grid D.R.m 0)) :
    besPer W.ψ 1 d o ζ μ 𝓕 ν 𝓝 (star φ) (star F) =
      starRingEnd ℂ (GlobalTheory.Per.besPer W.ψ G.besTop μ 𝓕 (GlobalTheory.RowChain.trMeas hN ν) (GlobalTheory.RowChain.trSet hN 𝓝) (embTop G) (star φ) F) := by
  have hy : (G.besTop.y : GA D (G.V (.grid D.R.m 0))) = 1 := rfl
  unfold besPer GlobalTheory.Per.besPer
  rw [← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  dsimp only
  rw [← integral_conj]
  have e2 := integral_tr' hN ν 𝓝 (fun g => starRingEnd ℂ
      (star (star (φ h)) * F (g * embTop G h) * star (besChar W.ψ G.besTop g)))
  refine Eq.trans ?_ (e2.symm.trans ?_)
  · refine integral_congr_ae (ae_of_all _ fun n => ?_)
    show star (φ h) * star (F (n.1 * embA d o h)) * star (psiBes W.ψ d 1 (vecB o ζ) n.1) = _
    rw [hE, hψ n.1 n.2]
    simp only [star_star, map_mul, Complex.star_def, Complex.conj_conj]
  · refine integral_congr_ae (ae_of_all _ fun n => ?_)
    show _ = starRingEnd ℂ (star (star (φ h)) * F (n.1 * embTop G h * (G.besTop.y : GA D (G.V (.grid D.R.m 0)))) *
      star (besChar W.ψ G.besTop n.1))
    rw [hy, mul_one]

end Key

section ToTop
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def toTop (vA : GlobalTheory.Unf.Vol (G.V (.core D.R.m))) : GlobalTheory.Unf.Vol (G.V (.top 0)) := vA
end ToTop

section Scale
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem scale_top (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (hM : M.IsRow) (vA : GlobalTheory.Unf.Vol (G.V (.core D.R.m)))
    (ν : Measure (NFlag (G.V (.grid D.R.m 0)) G.besTop.e)) (𝓝 : Set (NFlag (G.V (.grid D.R.m 0)) G.besTop.e))
    (hν : GlobalTheory.Per.IsUnitN _ G.besTop.e ν 𝓝) (φ : Fn G (.core D.R.m)) (F : Fn G (.grid D.R.m 0))
    (hφ : RapidDec _ φ) (hF : RapidDec _ F) :
    ∃ r : ℝ, 0 < r ∧ GlobalTheory.Per.besPer W.ψ G.besTop (toTop vA).μ (toTop vA).𝓕 ν 𝓝 (embTop G) (star φ) F =
      r * GlobalTheory.Per.besPer W.ψ G.besTop (M.ν (.top 0)) (M.fd (.top 0)) M.νN M.fdN (embTop G) (star φ) F :=
  per_scale W.ψ W.ψ_std (G.rowDec 0 (by have := D.R.two_le_m; omega)) G.besTop (GlobalTheory.RowUnf.cocpt_top G (Nat.zero_le _))
    (toTop vA).μ (M.ν (.top 0)) (toTop vA).𝓕 (M.fd (.top 0)) ν M.νN 𝓝 M.fdN
    (toTop vA).haar (toTop vA).fund hM.top.haar_fund.1 hM.top.haar_fund.2 hν hM.unip
    (star φ) F (fun γ hγ g => congrArg star (hφ.1 γ hγ g)) hF.1
end Scale

theorem top_gen {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G)
    (hM : M.IsRow) (i ρ : ℕ) (hi : i = D.R.m) (hρ : 2 * ρ + 2 = i) (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) {V₀ Lz : HSp D}
    (d : HypDec (G.V (.grid i 0)) V₀ ρ) (o : OrthDec V₀ (G.V (.core i)) Lz) (ζ : Fin Lz.rank → D.host.E)
    (hd : IsAuxiliaryVectorWittDec (G.colDec i h1 h2) d)
    (ha : d.i₀ * o.iA = frameMat _ _ (G.colDec i h1 h2).ι)
    (hz : (d.i₀ * o.iB) *ᵥ ζ = (-D.host.xi0) ^ (ρ + 1) • fun k => (G.colDec i h1 h2).a k ⟨ρ, by omega⟩)
    (vA : GlobalTheory.Unf.Vol (G.V (.core i))) (vN : VolN d) (φ : ∀ i, Fn G (.core i)) (f : ∀ i, Fn G (.grid i 0))
    (hφ : RapidDec _ (φ D.R.m)) (hf : RapidDec _ (f D.R.m))
    (hne : besPer W.ψ 1 d o ζ vA.μ vA.𝓕 vN.ν vN.𝓝 (star (φ i)) (star (f i)) ≠ 0) :
    Bplus W M (φ D.R.m) (f D.R.m) ≠ 0 := by
  subst hi
  obtain rfl : ρ = (D.R.m - 2) / 2 := by omega
  have hN := flag_eq h1 h2 d hd
  have hE := emb_eq h1 h2 d o ha
  have hψ := psi_eq W h1 h2 d o ζ hd hz
  obtain ⟨r, hr, hrr⟩ := scale_top W M hM vA (GlobalTheory.RowChain.trMeas hN vN.ν) (GlobalTheory.RowChain.trSet hN vN.𝓝)
    (GlobalTheory.RowChain.isUnit_trans hN _ _ vN.unit) (φ D.R.m) (f D.R.m) hφ hf
  intro hB
  apply hne
  have hb : GlobalTheory.Per.besPer W.ψ G.besTop (M.ν (.top 0)) (M.fd (.top 0)) M.νN M.fdN (embTop G)
      (star (φ D.R.m)) (f D.R.m) = 0 :=
    (Bplus_eq W M (φ D.R.m) (f D.R.m)).symm.trans hB
  have hrr' : GlobalTheory.Per.besPer W.ψ G.besTop (toTop vA).μ (toTop vA).𝓕 (GlobalTheory.RowChain.trMeas hN vN.ν) (GlobalTheory.RowChain.trSet hN vN.𝓝)
      (embTop G) (star (φ D.R.m)) (f D.R.m) = 0 := by
    rw [hrr, hb, mul_zero]
  rw [per_conj W d o ζ hN hE hψ vA.μ vA.𝓕 vN.ν vN.𝓝 (φ D.R.m) (f D.R.m)]
  exact (congrArg (starRingEnd ℂ) hrr').trans (map_zero _)

theorem ends : All fun {_} _ _ _ {G} W M => ∀ (v : CoreVol G) (F : Frames G), Std F → F.Ends v W M := by
  intro D _ T L μ0 _ sc G W M hM v F hF
  refine ⟨fun h => (embRel_iff _ h _).1 (F.oz.embRel_left _ hF.zA.symm h), fun ρ h he φ f hφ hf hne => ?_⟩
  refine top_gen W M hM (2 * ρ + 2) ρ he rfl (by omega) h (F.dB ρ h) (F.oB ρ h) (F.ζ (ρ + 1))
    (hF.hB ρ h) (hF.aB ρ h) ?_ (v (2 * ρ + 2)) (F.nB ρ h) φ f hφ hf hne
  rw [hF.ζ (ρ + 1), mulVec_smul, hF.zB' ρ h]

end GlobalTheory.AscFin.EndsPf

end
