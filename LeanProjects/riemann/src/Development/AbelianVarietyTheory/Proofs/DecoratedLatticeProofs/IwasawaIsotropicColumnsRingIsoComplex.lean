import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

open Matrix Formalism.UG

namespace GlobalTheory.Core.Rk.IwArch

section IsoCol

variable {A : Type} [CommRing A]

theorem map_cT_rect (σ : A →+* A) (f : A →+* ℂ) (hσ : ∀ x, f (σ x) = star (f x)) {m p : Type}
    (M : Matrix m p A) : (cT σ M).map f = (M.map f)ᴴ := by
  ext i j
  simp [cT, conjTranspose_apply, hσ]

theorem exists_compact_keep_cols {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ) (hf : Function.Bijective f)
    (hσ : ∀ x, f (σ x) = star (f x)) {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool)
    (hb : cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1))
    (X : Matrix (Fin n) (Fin r) A) (hX : cT σ X * J * X = 0) (g : GL (Fin n) A) (hg : g ∈ UJ σ J) :
    ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧
      ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β := by
  set F := RingEquiv.ofBijective f hf
  have hfF : ∀ z : ℂ, f (F.symm z) = z := fun z => F.apply_symm_apply z
  have hfinj : ∀ {p q : Type} (M N : Matrix p q A), M.map f = N.map f → M = N := fun M N h =>
    Matrix.ext fun i j => hf.1 (congrFun (congrFun h i) j)
  set D : Matrix (Fin n) (Fin n) A := Matrix.diagonal fun i => if ε i then 1 else -1 with hD
  have hJm : D.map f = Formalism.REAL.Jm ε := by
    ext i j
    by_cases h : i = j
    · subst h; by_cases he : ε i <;> simp [D, Formalism.REAL.Jm, he]
    · simp [D, Formalism.REAL.Jm, h]

  set h0 := b⁻¹ * g * b with hh0def
  have hh0 : h0 ∈ UJ σ D := hb ▸ conj_mem_UJ σ b hg
  have hh0' : Formalism.REAL.inUJ ε (h0.1.map f) := by
    have e : cT σ h0.1 * D * h0.1 = D := hh0
    have := congrArg (fun M => M.map f) e
    simp only [Matrix.map_mul, map_cT_rect σ f hσ, hJm] at this
    exact this
  let g' : Formalism.REAL.UJ ε := ⟨bc f h0, hh0'⟩

  set Y := (b⁻¹).1 * X with hYdef
  set X' := Y.map f with hX'def
  have hY : cT σ Y * D * Y = 0 := by
    rw [← hb, hYdef, cT_mul]
    calc cT σ X * cT σ (b⁻¹).1 * (cT σ b.1 * J * b.1) * ((b⁻¹).1 * X)
        = cT σ X * (cT σ (b⁻¹).1 * (cT σ b.1 * J * b.1) * (b⁻¹).1) * X := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [cT_inv_cancel, hX]
  have hiso0 : X'ᴴ * Formalism.REAL.Jm ε * X' = 0 := by
    have := congrArg (fun M => M.map f) hY
    simp only [Matrix.map_mul, map_cT_rect σ f hσ, hJm, Matrix.map_zero _ (map_zero f)] at this
    exact this
  set W := LinearMap.range X'.mulVecLin with hWdef
  let Wf : Fin 2 → Submodule ℂ (Fin n → ℂ) := ![⊥, W]
  have hflag : GlobalTheory.FlagMeas.IsIsoFlag ε (a := 1) (fun _ => Module.finrank ℂ W) Wf := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Wf]
    · intro i
      fin_cases i
      show Module.finrank ℂ W = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + Module.finrank ℂ W
      rw [finrank_bot, zero_add]
    · intro x hx y hy
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      simp only [Matrix.mulVecLin_apply]
      rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        ← Matrix.mul_assoc, hiso0, Matrix.vecMul_zero, zero_dotProduct]
  obtain ⟨k0, hk0, hk0W⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hflag g'
  have hkeep : ∀ y ∈ W, Formalism.MainNotions.S.uMat (g' * k0⁻¹) *ᵥ y ∈ W := fun y hy => hk0W 1 y hy

  let k1 : GL (Fin n) A := bc (F.symm : ℂ →+* A) (k0 : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hbc : ∀ u : (Matrix (Fin n) (Fin n) ℂ)ˣ, (bc (F.symm : ℂ →+* A) u).1.map f = u.1 := by
    intro u; ext i j; simp [bc, hfF]
  have hk1f : k1.1.map f = Formalism.MainNotions.S.uMat k0 := hbc _
  have hk1if : (k1⁻¹).1.map f = Formalism.MainNotions.S.uMat k0⁻¹ := by
    have : k1⁻¹ = bc (F.symm : ℂ →+* A) ((k0⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
      simp [k1, map_inv]
    rw [this]; exact hbc _
  have hk1D : k1 ∈ UJ σ D := by
    show cT σ k1.1 * D * k1.1 = D
    apply hfinj
    rw [Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, hJm]
    exact k0.2
  have hk1one : k1 ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) := by
    show cT σ k1.1 * 1 * k1.1 = 1
    apply hfinj
    rw [Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.mul_one]
    exact hk0
  refine ⟨b * k1 * b⁻¹, ?_, ?_, ?_⟩
  · have hk1' : k1 ∈ UJ σ (cT σ b.1 * J * b.1) := by rw [hb]; exact hk1D
    have := conj_mem_UJ σ b⁻¹ hk1'
    rw [cT_inv_cancel, inv_inv] at this
    exact this
  · convert hk1one using 1
    group

  set H := (h0 * k1⁻¹).1 with hHdef
  have hHf : H.map f = Formalism.MainNotions.S.uMat (g' * k0⁻¹) := by
    rw [hHdef, Units.val_mul, Matrix.map_mul, hk1if]
    rfl
  have hcol : ∀ c : Fin r, ∃ w : Fin r → ℂ, X' *ᵥ w = H.map f *ᵥ (X' *ᵥ Pi.single c 1) := by
    intro c
    have hm := hkeep _ (LinearMap.mem_range_self X'.mulVecLin (Pi.single c 1))
    rw [← hHf] at hm
    obtain ⟨w, hw⟩ := hm
    exact ⟨w, hw⟩
  choose w hw using hcol
  let β' : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i c => w c i
  have hHX : H.map f * X' = X' * β' := by
    ext i c
    have h1 := congrFun (hw c) i
    have e1 : (H.map f * X') i c = (H.map f *ᵥ (X' *ᵥ Pi.single c 1)) i := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl
    have e2 : (X' * β') i c = (X' *ᵥ w c) i := by
      rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]; rfl
    rw [e1, e2, h1]
  refine ⟨β'.map F.symm, ?_⟩
  have hβf : (β'.map F.symm).map f = β' := by ext i j; simp [hfF]
  have hHY : H * Y = Y * β'.map F.symm := by
    have e1 : (H * Y).map f = H.map f * X' := Matrix.map_mul
    have e2 : (Y * β'.map F.symm).map f = X' * β' := by rw [Matrix.map_mul, hβf]
    apply hfinj
    rw [e1, e2]
    exact hHX
  have hgk : g * (b * k1 * b⁻¹)⁻¹ = b * (h0 * k1⁻¹) * b⁻¹ := by
    rw [hh0def]; group
  rw [hgk, Units.val_mul, Units.val_mul]
  calc b.1 * H * (b⁻¹).1 * X = b.1 * (H * Y) := by rw [hYdef]; simp only [Matrix.mul_assoc]
    _ = b.1 * ((b⁻¹).1 * X * β'.map F.symm) := by rw [hHY]
    _ = X * β'.map F.symm := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem iw_iso_cols : ∀ {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ), Function.Bijective f → (∀ x, f (σ x) = star (f x)) → ∀ {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool), Formalism.UG.cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1) → ∀ (X : Matrix (Fin n) (Fin r) A), Formalism.UG.cT σ X * J * X = 0 → ∀ g : GL (Fin n) A, g ∈ UJ σ J → ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧ ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β  := by
  intro A _ n r σ f hf hσ J b ε hb X hX g hg
  exact exists_compact_keep_cols σ f hf hσ b ε hb X hX g hg

end IsoCol

end GlobalTheory.Core.Rk.IwArch
