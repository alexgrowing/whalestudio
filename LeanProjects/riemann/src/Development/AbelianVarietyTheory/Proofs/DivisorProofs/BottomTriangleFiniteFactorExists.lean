import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleFiniteFactor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFinRef

theorem exists_dual_eq_one {M : Type} [AddCommGroup M] [Module ℂ M] {a : M} (ha : a ≠ 0) :
    ∃ φ : M →ₗ[ℂ] ℂ, φ a = 1 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ M, φ a ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha ((Module.forall_dual_apply_eq_zero_iff ℂ a).1 h)
  exact ⟨(φ a)⁻¹ • φ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]⟩

theorem contract_tmul {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (φ : M →ₗ[ℂ] ℂ)
    (a : M) (b : N) : (TensorProduct.lid ℂ N) (φ.rTensor N (a ⊗ₜ b)) = φ a • b := by
  simp

theorem exists_smul_of_tmul_eq {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {a c : M}
    {b d : N} (ha : a ≠ 0) (h : a ⊗ₜ[ℂ] b = c ⊗ₜ[ℂ] d) : ∃ l : ℂ, b = l • d := by
  obtain ⟨φ, hφ⟩ := exists_dual_eq_one ha
  refine ⟨φ c, ?_⟩
  have := congrArg (fun z => (TensorProduct.lid ℂ N) (φ.rTensor N z)) h
  simp only [contract_tmul, hφ, one_smul] at this
  exact this

theorem tensor_eq_zero_of_subsingleton {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    [Subsingleton M] (z : M ⊗[ℂ] N) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem exists_smul_of_factor {Q Q' Pr Pf Pi : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q']
    [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] [AddCommGroup Pi] [Module ℂ Pi] [Nontrivial Pi]
    (q : Q →ₗ[ℂ] Pr) (q' : Q' →ₗ[ℂ] Pr) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi) (hq : Function.Surjective q) (x x' : Pf)
    (a : Q → Pi) (a' : Q' → Pi) (ha : ∀ P, a P = e (q P ⊗ₜ x)) (ha' : ∀ P', a' P' = e (q' P' ⊗ₜ x'))
    (H : (∀ P, a P = 0) ∨ ∃ (P : Q) (P' : Q') (κ : ℂ), a P ≠ 0 ∧ a P = κ • a' P') : ∃ κ : ℂ, x = κ • x' := by
  rcases H with H | ⟨P, P', κ, h0, h1⟩
  ·
    have hPr : Nontrivial Pr := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      obtain ⟨z, hz⟩ := exists_ne (0 : Pi)
      refine hz ?_
      rw [← e.apply_symm_apply z, tensor_eq_zero_of_subsingleton (e.symm z), map_zero]
    obtain ⟨y, hy⟩ := exists_ne (0 : Pr)
    obtain ⟨P, rfl⟩ := hq y
    have h2 : q P ⊗ₜ[ℂ] x = q P ⊗ₜ[ℂ] (0 : Pf) := by
      rw [TensorProduct.tmul_zero]
      apply e.injective
      rw [← ha, H, map_zero]
    obtain ⟨l, hl⟩ := exists_smul_of_tmul_eq hy h2
    exact ⟨0, by rw [hl, smul_zero, zero_smul]⟩
  · have h2 : q P ⊗ₜ[ℂ] x = q' P' ⊗ₜ[ℂ] (κ • x') := by
      apply e.injective
      rw [← ha, h1, ha', ← LinearEquiv.map_smul, TensorProduct.tmul_smul]
    have hy : q P ≠ 0 := by
      intro h
      exact h0 (by rw [ha, h, TensorProduct.zero_tmul, map_zero])
    obtain ⟨l, hl⟩ := exists_smul_of_tmul_eq hy h2
    exact ⟨l * κ, by rw [hl, smul_smul]⟩

theorem gBig_mono {Q₁ Q₂ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₂ := by
  obtain ⟨a₁, h₁⟩ := h₁
  refine ⟨a₁, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF hCF
  exact ⟨C₁, x₁, fun C hC D large₂ he hx r T Lc μ hLc G => H G μ C _ _ (h₁ C hC D large₂ he hx r T Lc μ hLc G)⟩

end GlobalTheory.BotFinRef

namespace GlobalTheory.BotFinRef

theorem exists_match_finData : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧ ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  intro hH hP hK hL
  refine gBig_mono (GlobalTheory.T.bottom_triangle_finite_factor hH hP hK hL) fun {D T Lc sc} G μ₀ C x b hA => ?_
  intro W i j A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨Pi, rf, rl, p, p', hm, hc⟩ := hA W i j A A' WW X hX FA FA' FW t hf hf'
  refine ⟨Pi, rf, rl, p, p', hm, fun Pr Pf q q' r r' e hq hq' hp hp' => ?_⟩
  haveI : Nontrivial Pi := hm.irred.1
  exact exists_smul_of_factor q q' e hq (r (X.f t)) (r' (X.f' t)) (fun P => p (fockF W.ψ W.θ true FA FW (X.f t) P))
    (fun P' => p' (fockF W.ψ W.θ false FA' FW (X.f' t) P')) (hp _ hf) (hp' _ hf') hc

end GlobalTheory.BotFinRef
