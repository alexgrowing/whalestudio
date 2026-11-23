import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

noncomputable section

namespace GlobalTheory.PushCob

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage TensorProduct

theorem contract_equivariant {R Y Q : Type} [CommRing R] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Q] [Module R Q] (ψ : Y →ₗ[R] R) (A : Y →ₗ[R] Y) (B : Q →ₗ[R] Q) (u t : R)
    (h : ∀ y, ∃ z, ψ (A y) - u * ψ y = t * z) (x : Y ⊗[R] Q) :
    ∃ q : Q, TensorProduct.lid R Q (ψ.rTensor Q (TensorProduct.map A B x)) =
      u • B (TensorProduct.lid R Q (ψ.rTensor Q x)) + t • q := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul y q =>
    obtain ⟨z, hz⟩ := h y
    refine ⟨z • B q, ?_⟩
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul,
      smul_smul, ← add_smul]
    rw [← hz]; congr 1; ring
  | add x x' hx hx' =>
    obtain ⟨q, hq⟩ := hx
    obtain ⟨q', hq'⟩ := hx'
    refine ⟨q + q', ?_⟩
    simp only [map_add, hq, hq', smul_add]
    abel

theorem actQab_mk {O G WC : Type} [CommRing O] [Group G] [CommRing WC] [Algebra O WC]
    {AA : Subalgebra O WC} {act : G →* (WC ≃ₐ[O] WC)} {ξ : WCˣ} (h : XiOK AA act ξ) (a b : ℤ)
    (g : G) (m : ↥(Mxi AA ξ a)) :
    actQab h a b g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (actM h a g m) := rfl

variable {l : ℕ} [Fact l.Prime]

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem inclW_zl (z : ℤ_[l]) :
    inclW l (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (WCb l) z := (inclWA l).commutes z

theorem mem_Mxi {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) (w : WCb l)
    (hw : w ∈ Mxi (AinfSub l) (xiU AI) (k : ℤ)) : ∃ a : Ainf l, w = inclW l (AI.ξ ^ k * a) := by
  obtain ⟨y, ⟨a, rfl⟩, rfl⟩ := hw
  refine ⟨a, ?_⟩
  rw [LinearMap.mulLeft_apply, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow]
  rfl

theorem mem_Mxi_zero {P : LocPrime l} (AI : LocAinf l P) (w : ↥(Mxi (AinfSub l) (xiU AI) 0)) :
    ∃ a : Ainf l, (w : WCb l) = inclW l a := by
  simpa using mem_Mxi AI 0 w w.2

def scaled {Y : Type} [AddCommGroup Y] [Module ℤ_[l] Y] (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (r : ℕ)
    (h : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) : Y →ₗ[ℤ_[l]] ℤ_[l] where
  toFun y := ⟨(l : ℚ_[l]) ^ r * ψ y, by
    have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
    exact h y⟩
  map_add' y y' := by
    apply Subtype.ext
    change _ = (l : ℚ_[l]) ^ r * ψ y + (l : ℚ_[l]) ^ r * ψ y'
    rw [← mul_add, ← map_add]
  map_smul' z y := by
    apply Subtype.ext
    change (l : ℚ_[l]) ^ r * ψ (z • y) = (z : ℚ_[l]) * ((l : ℚ_[l]) ^ r * ψ y)
    rw [map_smul, Algebra.smul_def, PadicInt.algebraMap_apply]
    ring

theorem scaled_coe {Y : Type} [AddCommGroup Y] [Module ℤ_[l] Y] (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (r : ℕ)
    (h : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) (y : Y) :
    ((scaled ψ r h y : ℤ_[l]) : ℚ_[l]) = (l : ℚ_[l]) ^ r * ψ y := rfl

theorem push_coboundary : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s e r N : ℕ) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y] (ρ : ↥(Gj K s) →* (Y →ₗ[ℤ_[l]] Y)) (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]), (∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) → (∀ (σ : GQ l) (hσ : σ ∈ Gj K s) (y : Y), ‖ψ (ρ ⟨σ, hσ⟩ y) - (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * ψ y‖ ≤ 1) → ∀ (f : ↥(Gj K s) → Y) (c : GQ l → ℚ_[l]), (∀ (σ : GQ l) (hσ : σ ∈ Gj K s), c σ = ψ (f ⟨σ, hσ⟩)) → ∀ one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0), (one : WCb l) = 1 → IsCob (repQ (D.locA l) (Gj K s) ρ 0 ((e : ℤ) + 1)) (fun g => (l : ℤ_[l]) ^ N • (f g ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))) → ∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l, algebraMap ℚ_[l] (D.loc l).R.BdR ((l : ℚ_[l]) ^ N * c σ) - (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈ ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1) := by
  intro D l _ K s e r N Y _ _ ρ ψ hψ hρ f c hc one hone hcob
  obtain ⟨x, hx⟩ := hcob
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlr : (l : ℚ_[l]) ^ r ≠ 0 := pow_ne_zero _ hl
  obtain ⟨m0, hm0⟩ := Submodule.Quotient.mk_surjective _
    (TensorProduct.lid ℤ_[l] _ ((scaled ψ r hψ).rTensor _ x))
  obtain ⟨a0, ha0⟩ := mem_Mxi_zero _ m0
  refine ⟨qB (D.loc l) ((l : ℚ_[l]) ^ r)⁻¹ * io (D.locA l) a0, qB_mul_mem _ (io_mem _ _), ?_⟩
  intro σ hσ
  have hn : ‖(((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, (cyc_basic l _ (D.loc l).χQ_cyc).1, one_zpow]
  set u' : ℚ_[l] := (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) with hu'
  let u : ℤ_[l] := ⟨u', hn⟩
  have hu : (u : ℚ_[l]) = u' := rfl
  obtain ⟨q, hq⟩ := contract_equivariant (scaled ψ r hψ) (ρ ⟨σ, hσ⟩)
    (actQab (act := (D.locA l).actWCbHom.comp (Gj K s).subtype)
      ⟨fun g x hx => (xiOK (D.locA l)).1 (g : GQ l) x hx, (xiOK (D.locA l)).2.1,
        fun g => (xiOK (D.locA l)).2.2 (g : GQ l)⟩ 0 ((e : ℤ) + 1) ⟨σ, hσ⟩) u ((l : ℤ_[l]) ^ r)
    (fun y => ⟨⟨_, hρ σ hσ y⟩, by
      apply Subtype.ext
      change (l : ℚ_[l]) ^ r * ψ (ρ ⟨σ, hσ⟩ y) - u' * ((l : ℚ_[l]) ^ r * ψ y) =
        (((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * (ψ (ρ ⟨σ, hσ⟩ y) - u' * ψ y)
      push_cast
      ring⟩) x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha⟩ := mem_Mxi_zero _ m
  have h1 := congrArg (fun w => TensorProduct.lid ℤ_[l] _ ((scaled ψ r hψ).rTensor _ w))
    (hx ⟨σ, hσ⟩)
  simp only [map_smul, map_sub, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h1
  rw [← hm0] at hq
  have h2 := h1.trans (congrArg₂ (· - ·) hq hm0.symm)
  beta_reduce at h2
  erw [actQab_mk] at h2
  simp only [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add,
    ← Submodule.Quotient.mk_sub] at h2
  rw [Submodule.Quotient.eq, Submodule.mem_comap] at h2
  obtain ⟨a', ha'⟩ := mem_Mxi (D.locA l) (e + 1) _ (by rw [Nat.cast_succ]; exact h2)
  have h3 : algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ N * scaled ψ r hψ (f ⟨σ, hσ⟩)) -
      (algebraMap ℤ_[l] (Ainf l) u * (D.locA l).actW σ a0 +
        algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ r) * a - a0) = (D.locA l).ξ ^ (e + 1) * a' := by
    apply inclW_injective
    rw [← ha']
    have h4 : inclW l ((D.locA l).actW σ a0) = (D.locA l).actWCbHom σ (m0 : WCb l) := by
      rw [ha0, inclW_act]; rfl
    rw [map_sub, map_sub, map_add, inclW_zl, map_mul (inclW l), map_mul (inclW l), inclW_zl,
      inclW_zl, h4, ← ha0, ← ha]
    change _ = (l : ℤ_[l]) ^ N • scaled ψ r hψ (f ⟨σ, hσ⟩) • (one : WCb l) -
      (u • (D.locA l).actWCbHom σ (m0 : WCb l) + (l : ℤ_[l]) ^ r • (m : WCb l) - (m0 : WCb l))
    rw [hone, smul_smul, ← Algebra.algebraMap_eq_smul_one, Algebra.smul_def, Algebra.smul_def]
  have h5 := congrArg (io (D.locA l)) h3
  rw [map_sub, map_sub, map_add, io_zl _ (D.locT l), map_mul (io _), map_mul (io _),
    map_mul (io _), map_pow (io _), io_zl _ (D.locT l), io_zl _ (D.locT l), io_act] at h5
  have h6 : io (D.locA l) (D.locA l).ξ ^ (e + 1) * io (D.locA l) a' ∈
      FilB (D.loc l) ((e : ℤ) + 1) := by
    have := FilB_mul (FilB_pow (io_ξ_mem (D.locA l)) (e + 1)) (io_mem (D.locA l) a')
    simpa using this
  refine ⟨a, ?_⟩
  have h7 := qB_mul_mem ((l : ℚ_[l]) ^ r)⁻¹ h6
  rw [← h5] at h7
  convert h7 using 1
  have h8 : qB (D.loc l) ((l : ℚ_[l]) ^ r)⁻¹ * qB (D.loc l) ((l : ℚ_[l]) ^ r) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hlr, map_one]
  rw [map_mul ((D.loc l).actQdR σ), AlgEquiv.commutes, hc σ hσ, ← io_apply, PadicInt.coe_mul,
    scaled_coe, PadicInt.coe_pow, PadicInt.coe_pow, PadicInt.coe_natCast, hu]
  simp only [map_mul]
  linear_combination (-(qB (D.loc l) ((l : ℚ_[l]) ^ N) * qB (D.loc l) (ψ (f ⟨σ, hσ⟩))) + io (D.locA l) a) * h8

end GlobalTheory.PushCob
