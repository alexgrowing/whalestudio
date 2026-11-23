import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvMid

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec (S : HSp D) {n : ℕ} (y : VA S) (M : Mx D S.rank n) (c : Fin n → AE D) :
    form S y (M *ᵥ c) = (fun k => cA D (c k)) ⬝ᵥ ((adj M ⬝ gA S) *ᵥ y) := by
  have h : (fun i => cA D ((M *ᵥ c) i)) = M.map (cA D) *ᵥ fun k => cA D (c k) := by
    funext i; exact RingHom.map_mulVec (cA D) M c i
  rw [form, h, ← Matrix.mulVec_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec, adj, Matrix.vecMul_transpose]

theorem mul_apply_col {m n k : ℕ} (g : Mx D m n) (M : Mx D n k) (r : Fin m) (c : Fin k) :
    (g ⬝ M) r c = (g *ᵥ (M *ᵥ Pi.single c 1)) r := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl

theorem col_apply {m n : ℕ} (M : Mx D m n) (c : Fin n) (r : Fin m) : (M *ᵥ Pi.single c 1) r = M r c := by
  rw [Matrix.mulVec_single_one]; rfl

theorem submatrix_col {m n : ℕ} (M : Mx D m n) (i : Fin n) (c : Fin 1) :
    (M.submatrix id fun _ : Fin 1 => i) *ᵥ Pi.single c 1 = M *ᵥ Pi.single i 1 := by
  funext r; rw [col_apply, col_apply]; rfl

theorem smul_vecMulVec_single {ρ : ℕ} (s : AE D) (x : Fin ρ → AE D) (J k : Fin ρ) :
    (s • vecMulVec x (Pi.single J 1)) *ᵥ Pi.single k 1 = (s * (Pi.single k 1 : Fin ρ → AE D) J) • x := by
  funext l
  rw [col_apply]
  by_cases hk : k = J
  · subst hk; simp [Matrix.vecMulVec_apply]
  · simp [Matrix.vecMulVec_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne' hk]

theorem upSum_smul_vecMulVec {ρ : ℕ} (s : AE D) (x : Fin ρ → AE D) (j J : Fin ρ) (hJ : J.1 = j.1 + 1) :
    GlobalTheory.MixPer.upSum (s • vecMulVec x (Pi.single J 1)) = s * x j := by
  have hTe : ∀ i k : Fin ρ, (if k.1 = i.1 + 1 then (s • vecMulVec x (Pi.single J 1)) i k else 0) =
      if i = j then (if k = J then s * x j else 0) else 0 := by
    intro i k
    by_cases hk : k = J
    · subst hk
      by_cases hi : i = j
      · subst hi
        simp [hJ, Matrix.vecMulVec_apply, mul_comm]
      · have : ¬ (k.1 = i.1 + 1) := fun h => hi (Fin.ext (by omega))
        simp [hi, this]
    · simp [hk, Matrix.vecMulVec_apply]
  rw [GlobalTheory.MixPer.upSum]
  simp only [hTe]
  simp

section Mid

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem form_jY_single (y : VA V) (J : Fin ρ) (s : AE D) :
    form V y (d.jY *ᵥ Pi.single J (cA D s)) = s * (d.pX *ᵥ y) J := by
  have h : (fun k => cA D ((Pi.single J (cA D s) : Fin ρ → AE D) k)) = (Pi.single J s : Fin ρ → AE D) := by
    funext k
    by_cases hk : k = J
    · subst hk; simp [cA_cA]
    · simp [Pi.single_apply, hk]
  rw [form_mulVec, h, ← d.pX_eq, single_dotProduct]

theorem form_jX (y : VA V) (b : Fin ρ → AE D) :
    form V y (d.jX *ᵥ b) = (fun k => cA D (b k)) ⬝ᵥ (d.pY *ᵥ y) := by
  rw [form_mulVec, ← d.pY_eq]

theorem transv_fix {w v : VA V} {u : GA D V} (hu : IsTransv V w v u) {y : VA V} (hv : form V y v = 0)
    (hw : form V y w = 0) : mt V u *ᵥ y = y := by
  have := hu y
  rw [act, transv, hv, hw] at this
  rw [this]; simp

theorem pX_jX_single (k : Fin ρ) : d.pX *ᵥ (d.jX *ᵥ Pi.single k 1) = Pi.single k 1 := by
  rw [Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec]

theorem pY_jX_vec (x : Fin ρ → AE D) : d.pY *ᵥ (d.jX *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pY_jX, Matrix.zero_mulVec]

theorem isotropicProjection_anisotropic_vec_eq_zero (x : Fin V₀.rank → AE D) : d.pX *ᵥ (d.j0 *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]

theorem dualProjection_anisotropic_vec_eq_zero (x : Fin V₀.rank → AE D) : d.pY *ᵥ (d.j0 *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]

theorem transv_apply {w v : VA V} {u : GA D V} (hu : IsTransv V w v u) (y : VA V) :
    mt V u *ᵥ y = transv V w v y := hu y

variable {w v : VA V} {u : GA D V} {J : Fin ρ} {s : AE D} {c : Fin ρ → AE D}

theorem mem_fixer_of_ne (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) {i : Fin ρ} (hiJ : i ≠ J) :
    u ∈ GlobalTheory.MixPer.fixer V (d.jX.submatrix id fun _ : Fin 1 => i) := by
  rw [GlobalTheory.MixPer.mem_fixer]
  ext r k
  rw [mul_apply_col, submatrix_col, transv_fix hu, col_apply]
  · rfl
  · rw [fv, pX_jX_single d, Pi.single_eq_of_ne' hiJ, mul_zero]
  · rw [fw, pY_jX_vec d, dotProduct_zero]

theorem transv_jX (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) {x : Fin ρ → AE D} (hw : w = d.jX *ᵥ x) :
    mt V u ⬝ d.jX = d.jX + d.jX ⬝ (s • vecMulVec x (Pi.single J 1)) := by
  ext r k
  rw [mul_apply_col, transv_apply hu, transv, fv, fw, pX_jX_single d, pY_jX_vec d]
  simp only [dotProduct_zero, mul_zero, zero_smul, sub_zero]
  rw [Matrix.add_apply, mul_apply_col, smul_vecMulVec_single, Matrix.mulVec_smul, ← hw]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, col_apply]

theorem unitaryTransvection_on_anisotropic_part (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) : mt V u ⬝ d.j0 = d.j0 + d.jX ⬝ (0 : Mx D ρ V₀.rank) := by
  rw [Matrix.mul_zero, add_zero]
  ext r k
  rw [mul_apply_col, transv_fix hu, col_apply]
  · rw [fv, isotropicProjection_anisotropic_vec_eq_zero d, Pi.zero_apply, mul_zero]
  · rw [fw, dualProjection_anisotropic_vec_eq_zero d, dotProduct_zero]

end Mid

end GlobalTheory.TransvMid

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction in

theorem GlobalTheory.TransvMid.exists_mid : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E) (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 < ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  intro D V V₀ ρ d z j a haj hai hj s
  set J : Fin ρ := ⟨j.1 + 1, hj⟩ with hJ
  have hjJ : j < J := by rw [Fin.lt_def]; simp [hJ]
  have haJ : ratVec a J = 0 := by simp [ratVec, hai J hjJ]
  have hw : vecX d (ratVec a) = d.jX *ᵥ ratVec a := rfl
  refine ⟨d.jY *ᵥ Pi.single J (cA D s), ?_, ?_, ?_⟩
  · rw [GlobalTheory.TransvMid.form_jY_single, hw, Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec, haJ, mul_zero]
  · intro i k hki
    rw [GlobalTheory.TransvMid.form_jY_single, vecX, Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec]
    by_cases hk : k = J
    · subst hk
      have : ratVec a i = 0 := by simp [ratVec, hai i (lt_of_lt_of_le hjJ hki)]
      rw [this, mul_zero]
    · rw [Pi.single_eq_of_ne' hk, mul_zero, zero_mul]
  · intro u hu
    have fv : ∀ y : VA V, form V y (d.jY *ᵥ Pi.single J (cA D s)) = s * (d.pX *ᵥ y) J :=
      fun y => GlobalTheory.TransvMid.form_jY_single d y J s
    have fw : ∀ y : VA V, form V y (vecX d (ratVec a)) = (fun k => cA D (ratVec a k)) ⬝ᵥ (d.pY *ᵥ y) :=
      fun y => GlobalTheory.TransvMid.form_jX d y _
    generalize d.jY *ᵥ Pi.single J (cA D s) = v at hu fv
    generalize hwv : vecX d (ratVec a) = w at hu fw
    rw [vecX] at hwv
    refine ⟨fun i => GlobalTheory.TransvMid.mem_fixer_of_ne d hu fv fw (ne_of_lt (lt_of_le_of_lt i.2 hjJ)), ?_⟩
    rw [GlobalTheory.MixPer.simpleSum_eq d z (GlobalTheory.TransvMid.transv_jX d hu fv fw hwv.symm)
      (GlobalTheory.TransvMid.unitaryTransvection_on_anisotropic_part d hu fv fw), GlobalTheory.MixPer.superSum_const]
    simp only [Matrix.zero_mulVec, dotProduct_zero, add_zero, one_mul]
    rw [GlobalTheory.TransvMid.upSum_smul_vecMulVec s _ j J rfl]
    simp [ratVec, haj]
