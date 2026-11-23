import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.HeisWeil

variable {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V] {Bf : V → V → R}
  {κ : Type} [Fintype κ]

theorem rho_add (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (w : V) (f g : (κ → R) → ℂ) :
    dc.rho ψ w (f + g) = dc.rho ψ w f + dc.rho ψ w g := by
  funext x
  simp [Darboux.rho, schr, mul_add]

theorem rho_smul (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (w : V) (c : ℂ) (f : (κ → R) → ℂ) :
    dc.rho ψ w (c • f) = c • dc.rho ψ w f := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem rho_zero (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (w : V) : dc.rho ψ w (0 : (κ → R) → ℂ) = 0 := by
  funext x
  simp [Darboux.rho, schr]

end GlobalTheory.ArchDecay.HeisWeil

open GlobalTheory.ArchDecay.HeisWeil

theorem GlobalTheory.ArchDecay.HeisWeil.exists_hasDerivAt_adm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (ψ : AddChar (AF F) ℂ) {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)}
    (dc : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (hψ : IsStd ψ) (u : Matrix α β (AE F E))
    (hu : At (evI F) u) (f : (κ → AF F) → ℂ) (hf : f ∈ schA F κ) :
    ∃ Df : (κ → AF F) → ℂ, ∀ l ∈ (adeleClass F).adm κ,
      HasDerivAt (fun t : ℝ => l (dc.rho ψ (realAd F t • u) f)) (l Df) 0 := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ α β κ ψ JA JB dc hψ
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₀, g, hg, rfl⟩ := hx
    exact ⟨pureA F (D u f₀) g, fun l hl => (hD u hu f₀).1 g hg l hl⟩
  | zero =>
    refine ⟨0, fun l _ => ?_⟩
    simp only [rho_zero, map_zero]
    exact hasDerivAt_const _ _
  | add x y _ _ hx hy =>
    obtain ⟨Dx, hDx⟩ := hx
    obtain ⟨Dy, hDy⟩ := hy
    refine ⟨Dx + Dy, fun l hl => ?_⟩
    simp only [rho_add, map_add]
    exact (hDx l hl).add (hDy l hl)
  | smul c x _ hx =>
    obtain ⟨Dx, hDx⟩ := hx
    refine ⟨c • Dx, fun l hl => ?_⟩
    simp only [rho_smul, map_smul, smul_eq_mul]
    exact (hDx l hl).const_mul c

theorem GlobalTheory.ArchDecay.HeisWeil.heisD_weil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u → ∀ f ∈ schA F (Fin n × Fin d), heisD M B.ψ u (om p f) = om p (heisD M B.ψ (actAB (cA σ) p⁻¹ u) f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP p u hu f hf
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  set u' := actAB (cA σ) p⁻¹ u with hu'def
  have hu' : At (evI F) u' := fun a ha => by
    rw [hu'def, actAB, ← Matrix.smul_mul, ← Matrix.mul_smul, hu a ha, Matrix.mul_zero, Matrix.zero_mul]
  have hact : ∀ t : ℝ, actAB (cA σ) p (realAd F t • u') = realAd F t • u := fun t => by
    simp only [hu'def, actAB]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, Matrix.mul_assoc]
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]
  obtain ⟨Df, hDf⟩ := exists_hasDerivAt_adm B.ψ M.co hψ u' hu' f hf
  have hDfx : Df = heisD M B.ψ u' f := by
    funext x
    exact ((hDf _ (GlobalTheory.RealLift.eval_mem_adm x)).deriv).symm
  funext x
  have hl := hS.adm p _ (GlobalTheory.RealLift.eval_mem_adm x)
  have h1 := hDf _ hl
  have e : (fun t : ℝ => M.heisLine B.ψ u t (om p f) x) =
      fun t : ℝ => ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om p)
        (M.co.rho B.ψ (realAd F t • u') f) := by
    funext t
    rw [LinearMap.comp_apply, hS.impl p _ f hf, hact t]
    rfl
  show deriv (fun t : ℝ => M.heisLine B.ψ u t (om p f) x) 0 = _
  rw [e, h1.deriv, ← hDfx]
  rfl
