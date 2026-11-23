import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatVacSign

variable {D : D7} {S T : HSp D}

theorem cA_incA' (w : D.host.E) : cA D (incA D w) = incA D (star w) := rfl

theorem hO_smul_smul (c c' : AE D) (x y : WO S T) :
    hO S T (c • x) (c' • y) = c * cA D c' * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symplO_smul_smul (w w' : D.host.E) (x y : WO S T) :
    symplO S T (incA D w • x) (incA D w' • y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D (D.host.xi0 * (w * star w')) * hO S T x y) := by
  rw [symplO, hO_smul_smul, cA_incA', map_mul (incA D), map_mul (incA D)]
  congr 1
  ring

theorem symplOH_smul_norm {w : D.host.E} {n : ℤ} (hw : w * star w = 2 * n) (x y : WO S T) :
    symplOH S T (incA D w • x) (incA D w • y) = (n : AF D.host.F) * symplO S T x y := by
  have e : incA D (D.host.xi0 * (w * star w)) * hO S T x y =
      ((2 * n : ℤ) : AE D) * (incA D D.host.xi0 * hO S T x y) := by
    rw [hw]
    simp only [map_mul, map_intCast, map_ofNat]
    push_cast
    ring
  rw [symplOH, symplO_smul_smul, e, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, ← symplO]
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  push_cast
  linear_combination ((n : AF D.host.F) * symplO S T x y) * h2

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem char_symplOH_smul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {w : D.host.E} {n : ℤ} (hw : w * star w = 2 * n) {x y : WO S T}
    (hx : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (hy : y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    ψ (symplOH S T (incA D w • x) (incA D w • y)) = 1 := by
  rw [symplOH_smul_norm hw, ← zsmul_eq_mul, AddChar.map_zsmul_eq_zpow,
    GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hx hy, _root_.one_zpow]

theorem incA_smul_finTens {m k : ℕ} (w : D.host.E) (α : Af D.host.F) (M : Matrix (Fin m) (Fin k) D.host.E) :
    incA D w • GlobalTheory.LatVac.finTens α M = GlobalTheory.LatVac.finTens α (w • M) := by
  ext i j
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] w : AE D) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j) =
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (w * M i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_mem_latO' {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (w : 𝓞 D.host.E)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    incA D (w : D.host.E) • u ∈ latO S T LS LT fun _ => True := by
  refine GlobalTheory.LatVac.latO_induction (p := fun u => incA D (w : D.host.E) • u ∈ latO S T LS LT fun _ => True)
    ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    rw [incA_smul_finTens]
    exact GlobalTheory.LatVac.finTens_mem_latO hα (GlobalTheory.LatVac.smul_mem_latRat w hM)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

def fixGroup (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (c : AE D)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplOH S T (c • x) (c • y)) = 1) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ Λ ∧ ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T (c • u) f = f}
  zero_mem' := ⟨zero_mem _, fun f _ => by rw [smul_zero, GlobalTheory.LatVac.heisO_zero]⟩
  add_mem' := by
    rintro a b ⟨ha, fa⟩ ⟨hb, fb⟩
    refine ⟨add_mem ha hb, fun f hf => ?_⟩
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ (c • a) (c • b) f
    rw [fb f hf, fa f hf, hΛ a ha b hb, one_smul, ← smul_add] at h1
    exact h1.symm
  neg_mem' := by
    rintro a ⟨ha, fa⟩
    refine ⟨neg_mem ha, fun f hf => ?_⟩
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ (c • -a) (c • a) f
    rw [fa f hf, hΛ (-a) (neg_mem ha) a ha, one_smul, ← smul_add, neg_add_cancel,
      smul_zero, GlobalTheory.LatVac.heisO_zero] at h1
    exact h1

theorem mem_fixGroup {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {c : AE D}
    {hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplOH S T (c • x) (c • y)) = 1} {u : WO S T} :
    u ∈ fixGroup ψ Λ c hΛ ↔ u ∈ Λ ∧ ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T (c • u) f = f := Iff.rfl

theorem heisO_smul_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (w : 𝓞 D.host.E) {n : ℤ} (hw : (w : D.host.E) * star (w : D.host.E) = 2 * n)
    {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (f : WO S T → ℂ)
    (hf : IsLatVac (heisO ψ S T)
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    heisO ψ S T (incA D (w : D.host.E) • u) f = f := by
  have hΛ : ∀ x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ψ (symplOH S T (incA D (w : D.host.E) • x) (incA D (w : D.host.E) • y)) = 1 :=
    fun x hx y hy => char_symplOH_smul hψ hS hT hw hx hy
  have h2 : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      2 • u ∈ fixGroup ψ _ _ hΛ := by
    intro u hu
    refine mem_fixGroup.2 ⟨nsmul_mem hu 2, fun f hf => ?_⟩
    have e : incA D (w : D.host.E) • (2 • u) = 2 • (incA D (w : D.host.E) • u) := by
      rw [two_nsmul, two_nsmul, smul_add]
    rw [e]
    exact hf.1 _ (smul_mem_latO' w hu)
  have hh : ∀ e, IsSplitIdem D e →
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u → u ∈ fixGroup ψ _ _ hΛ := by
    intro e he u hu hh
    refine mem_fixGroup.2 ⟨hu, fun f hf => hf.2 e he _ (smul_mem_latO' w hu) fun i j => ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hh i j]
  exact (mem_fixGroup.1 (GlobalTheory.LatVac.le_of_two_of_half _ h2 hh hu)).2 f hf

theorem hRat_smul_smul (a b : D.host.E) (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (a • M) (b • N) = a * star b * GlobalTheory.LatVac.hRat S T M N := by
  simp only [GlobalTheory.LatVac.hRat, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, star_mul']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem finRat_eq (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.VacUnique.finRat S T M = GlobalTheory.LatVac.finTens 1 M := by
  ext i j; rfl

theorem algebraMap_mul_pair (c : D.host.F) (β : Af D.host.F) :
    algebraMap D.host.F (AF D.host.F) c * pairA D.host.F 0 β =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) c * β) :=
  Prod.ext (mul_zero _) rfl

end GlobalTheory.LatVacSign

open GlobalTheory.LatVacSign in

theorem GlobalTheory.LatVacSign.heisO_finRat_sign : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T v v) ∧ heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) f = ((-1 : ℂ) ^ k) • f := by
  intro D ψ S T ΛS ΛT hψ hS hT f hf v hv
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have hst : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have := D.host.isCMField_hostE
    have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
      NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
    rw [h2, map_neg, h1]
    simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (D.host.d : ℤ) + 1 = 8 * n :=
    ⟨((D.host.d : ℤ) + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  have hnE : (D.host.d : D.host.E) = 8 * n - 1 := by
    have := congrArg (Int.cast (R := D.host.E)) hn
    push_cast at this
    linear_combination this
  set w₀ : D.host.E := (1 + D.host.sqrtMinusD) / 2 with hw₀
  have hstw : star w₀ = 1 - w₀ := by
    rw [hw₀, star_div₀, star_add, star_one, hst, star_ofNat]
    ring
  have hnorm : w₀ * (1 - w₀) = 2 * n := by
    rw [hw₀]
    linear_combination (-1 / 4 : D.host.E) * hsq + (1 / 4 : D.host.E) * hnE
  have hint : IsIntegral ℤ w₀ := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * n), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, eq_intCast]
    push_cast
    linear_combination (-1 : D.host.E) * hnorm
  let W : 𝓞 D.host.E := ⟨w₀, hint⟩
  let W' : 𝓞 D.host.E := 1 - W
  have hW : (W : D.host.E) = w₀ := rfl
  have hW' : (W' : D.host.E) = 1 - w₀ := by
    change algebraMap (𝓞 D.host.E) D.host.E (1 - W) = 1 - w₀
    rw [map_sub, map_one]
    rfl
  have nW : (W : D.host.E) * star (W : D.host.E) = 2 * n := by rw [hW, hstw, hnorm]
  have nW' : (W' : D.host.E) * star (W' : D.host.E) = 2 * n := by
    rw [hW', star_sub, star_one, hstw, sub_sub_cancel, mul_comm, hnorm]
  set u := GlobalTheory.VacUnique.finRat S T (-v) with hu_def
  have h1 := heisO_smul_fix hψ hS hT W nW hv f hf
  have h2 := heisO_smul_fix hψ hS hT W' nW' hv f hf
  have hsum : incA D (W : D.host.E) • u + incA D (W' : D.host.E) • u = u := by
    rw [← add_smul, ← map_add, hW, hW', add_sub_cancel, map_one, one_smul]
  have key := GlobalTheory.LatVac.heisO_heisO ψ (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u) f
  rw [h2, h1, hsum] at key

  set z : D.host.E := D.host.xi0 * w₀ ^ 2 * GlobalTheory.LatVac.hRat S T v v with hz
  have hpair : symplO S T (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (Algebra.trace D.host.F D.host.E z)) := by
    rw [hu_def, finRat_eq, incA_smul_finTens, incA_smul_finTens, GlobalTheory.LatVac.symplO_finTens, one_mul, one_mul]
    congr 3
    rw [hz, ← neg_one_smul D.host.E v, smul_smul, smul_smul, hRat_smul_smul, hW, hW', star_mul', star_sub,
      star_one, hstw, star_neg, star_one]
    ring
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Algebra.trace ℚ D.host.E z = k := by
    have := GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (smul_mem_latO' W hv) (smul_mem_latO' W' hv)
    rw [hpair] at this
    exact (GlobalTheory.LatVac.char_rat hψ z).1 this
  have hsign : ψ (symplOH S T (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u)) = (-1 : ℂ) ^ k := by
    rw [symplOH, hpair, algebraMap_mul_pair, ← map_mul, GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace D ψ hψ]
    have e : Algebra.trace ℚ D.host.F (1 / 2 * Algebra.trace D.host.F D.host.E z) = (1 / 2 : ℚ) * k := by
      have h12 : (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) := by simp
      rw [h12, ← Algebra.smul_def, map_smul, Algebra.trace_trace, hk, smul_eq_mul]
    rw [e, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  rw [hsign] at key
  refine ⟨k, hk.symm, ?_⟩
  have hsq1 : ((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_zpow]; norm_num
  calc heisO ψ S T u f = (((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k) • heisO ψ S T u f := by rw [hsq1, one_smul]
    _ = (-1 : ℂ) ^ k • f := by rw [mul_smul, ← key]
