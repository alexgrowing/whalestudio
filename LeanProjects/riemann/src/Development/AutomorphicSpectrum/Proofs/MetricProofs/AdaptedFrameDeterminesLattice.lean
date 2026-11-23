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

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ}

namespace LatEmb

variable (C : LatEmb F)

theorem perExt_eq_sum (R : RiemLat E g Λ) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R y = ∑ k, C.bas.repr y k • R.P (C.lam k) := by
  simp [perExt, Module.Basis.constr_apply_fintype]

omit [IsCMField E] in

theorem form_antisymm {M : Type} [AddCommGroup M] (f : M →ₗ[ℤ] M →ₗ[ℤ] ℤ) (hf : ∀ x, f x x = 0) (x y : M) :
    f x y = - f y x := by
  have h := hf (x + y)
  simp only [map_add, LinearMap.add_apply, hf] at h
  linarith

theorem exists_dual (R : RiemLat E g Λ) (i : Fin (2 * g)) :
    ∃ z : Λ, ∀ k, R.form (C.lam k) z = if k = i then 1 else 0 := by
  obtain ⟨x, hx⟩ := R.unimod.2 (C.lam.coord i)
  refine ⟨-x, fun k => ?_⟩
  rw [map_neg, form_antisymm R.form R.alt, neg_neg, hx]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

theorem perExt_injective (R : RiemLat E g Λ) : Function.Injective (C.perExt R) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hc : ∀ i, C.bas.repr y i = 0 := by
    intro i
    obtain ⟨z, hz⟩ := C.exists_dual R i
    have h0 : ((C.perExt R y) ⬝ᵥ R.Hm *ᵥ star (R.P z)).im = 0 := by simp [hy]
    have hk : ∀ k, ((C.bas.repr y k • R.P (C.lam k)) ⬝ᵥ R.Hm *ᵥ star (R.P z)).im =
        C.bas.repr y k * (R.form (C.lam k) z : ℝ) := by
      intro k
      rw [smul_dotProduct, Complex.smul_im, R.im]
      simp
    rw [C.perExt_eq_sum, sum_dotProduct, Complex.im_sum] at h0
    simp only [hk, hz] at h0
    simpa using h0
  apply C.bas.repr.injective
  ext i
  simpa using hc i

theorem perExt_bijective (R : RiemLat E g Λ) : Function.Bijective (C.perExt R) := by
  have hd : Module.finrank ℝ (Ψ → Fin (j + j') → ℂ) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_eq_card_basis C.bas]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  exact ⟨C.perExt_injective R, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 (C.perExt_injective R)⟩

def latPt (x : Λ) : Ψ → Fin (j + j') → ℂ := ∑ k, ((C.lam.repr x k : ℤ) : ℝ) • C.bas k

theorem perExt_latPt (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.latPt x) = R.P x := by
  have hb : ∀ k, C.perExt R (C.bas k) = R.P (C.lam k) := fun k => by
    simp [perExt, Module.Basis.constr_basis]
  conv_rhs => rw [← C.lam.sum_repr x, map_sum]
  unfold latPt
  rw [map_sum]
  simp only [map_smul, hb, Int.cast_smul_eq_zsmul, map_zsmul]

omit [NumberField E] in

theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply]

theorem cinv_mul {M : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (hu : Mᴴ * C.sgr τ * M = sgI j j') :
    C.cinv M τ * M = 1 := by
  unfold cinv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hu, sgI_mul_self]

theorem mul_cinv {M : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (hu : Mᴴ * C.sgr τ * M = sgI j j') :
    M * C.cinv M τ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (C.cinv_mul hu)

def aPart (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) : Fin (j + j') → ℂ :=
  A τ *ᵥ Sum.elim (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inl i)) 0

def bPart (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) : Fin (j + j') → ℂ :=
  A τ *ᵥ Sum.elim 0 (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inr i))

theorem aPart_add_bPart {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ}
    (hu : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j') (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) :
    C.aPart A y τ + C.bPart A y τ = y τ := by
  unfold aPart bPart
  rw [← mulVec_add]
  have h : (Sum.elim (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inl i)) (0 : Fin j' → ℂ) +
      Sum.elim (0 : Fin j → ℂ) (fun i => (C.cinv (A τ) τ *ᵥ y τ) (Sum.inr i)) : Sg j j' → ℂ) =
      C.cinv (A τ) τ *ᵥ y τ := by
    ext (i | i) <;> simp
  rw [h, mulVec_mulVec, C.mul_cinv (hu τ), one_mulVec]

def cxStr (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) : Fin (j + j') → ℂ :=
  (-Complex.I) • C.aPart A y τ + Complex.I • C.bPart A y τ

open Classical in

theorem perExt_single_I_of_pPart (R : RiemLat E g Λ) (τ : Ψ) (w : Fin (j + j') → ℂ) (h : C.pPart R τ w = 0) :
    C.perExt R (Pi.single τ (Complex.I • w)) = (-Complex.I) • C.perExt R (Pi.single τ w) := by
  have h2 := (smul_eq_zero.1 h).resolve_left (by norm_num)
  rw [sub_eq_zero.1 h2, smul_smul]
  simp

open Classical in

theorem perExt_single_I_of_pBar (R : RiemLat E g Λ) (τ : Ψ) (w : Fin (j + j') → ℂ) (h : C.pBar R τ w = 0) :
    C.perExt R (Pi.single τ (Complex.I • w)) = Complex.I • C.perExt R (Pi.single τ w) := by
  have h2 := (smul_eq_zero.1 h).resolve_left (by norm_num)
  rw [eq_neg_of_add_eq_zero_left h2, smul_neg, smul_smul]
  simp

open Classical in

theorem perExt_single_cxStr {R : RiemLat E g Λ} {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A)
    (y : Ψ → Fin (j + j') → ℂ) (τ : Ψ) :
    C.perExt R (Pi.single τ (C.cxStr A y τ)) = Complex.I • C.perExt R (Pi.single τ (y τ)) := by
  have ha := C.perExt_single_I_of_pPart R τ (C.aPart A y τ) (hA.ker τ _)
  have hb := C.perExt_single_I_of_pBar R τ (C.bPart A y τ) (hA.kerBar τ _)
  have hy : C.perExt R (Pi.single τ (y τ)) =
      C.perExt R (Pi.single τ (C.aPart A y τ)) + C.perExt R (Pi.single τ (C.bPart A y τ)) := by
    rw [← map_add, ← Pi.single_add, C.aPart_add_bPart hA.unit]
  unfold cxStr
  rw [neg_smul, Pi.single_add, map_add, Pi.single_neg, map_neg, ha, hb, hy, smul_add]
  simp

open Classical in

theorem perExt_eq_sum_single (R : RiemLat E g Λ) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R y = ∑ τ, C.perExt R (Pi.single τ (y τ)) := by
  rw [← map_sum, Finset.univ_sum_single]

theorem perExt_cxStr {R : RiemLat E g Λ} {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A)
    (y : Ψ → Fin (j + j') → ℂ) : C.perExt R (C.cxStr A y) = Complex.I • C.perExt R y := by
  classical
  rw [C.perExt_eq_sum_single R (C.cxStr A y), C.perExt_eq_sum_single R y, Finset.smul_sum]
  exact Finset.sum_congr rfl fun τ _ => C.perExt_single_cxStr hA y τ

theorem eqvBy_of_adapted (R R' : RiemLat E g Λ) {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ}
    (hA : C.IsAdapted R A) (hA' : C.IsAdapted R' A) : R.EqvBy R' 1 := by
  let eL := LinearEquiv.ofBijective (C.perExt R) (C.perExt_bijective R)
  let eL' := LinearEquiv.ofBijective (C.perExt R') (C.perExt_bijective R')
  let φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := eL.symm.trans eL'
  have hφL : ∀ y, φ (C.perExt R y) = C.perExt R' y := by
    intro y
    have h : eL.symm (C.perExt R y) = y := eL.symm_apply_apply y
    show eL' (eL.symm (C.perExt R y)) = _
    rw [h]
    rfl
  have hI : ∀ z, φ (Complex.I • z) = Complex.I • φ z := by
    intro z
    obtain ⟨y, rfl⟩ := (C.perExt_bijective R).2 z
    rw [← C.perExt_cxStr hA, hφL, hφL, C.perExt_cxStr hA']
  have hz : ∀ (c : ℂ) (w : Fin g → ℂ), c • w = c.re • w + c.im • (Complex.I • w) := by
    intro c w
    ext k
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hs : ∀ (c : ℂ) z, φ (c • z) = c • φ z := by
    intro c z
    rw [hz c z, map_add, map_smul, map_smul, hI, ← hz]
  refine ⟨{ toFun := φ, invFun := φ.symm, left_inv := φ.left_inv, right_inv := φ.right_inv,
            map_add' := φ.map_add, map_smul' := hs }, fun x => ?_⟩
  show R'.P x = φ (R.P x)
  rw [← C.perExt_latPt R x, hφL, C.perExt_latPt]

end LatEmb

theorem adapted_eqvBy (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ)
    (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ)
    (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (_ : R.form = F.form) (_ : R'.form = F.form)
    (hA : C.IsAdapted R A) (hA' : C.IsAdapted R' A) : R.EqvBy R' 1 :=
  C.eqvBy_of_adapted R R' hA hA'

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
