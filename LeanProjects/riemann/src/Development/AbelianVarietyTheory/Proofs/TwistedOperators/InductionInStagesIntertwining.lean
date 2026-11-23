import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem stageFun_law : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (s : Fin a → ℂ) (s' : Fin b → ℂ) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V), (∀ m ∈ leviOne ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W') → (∀ x t, IsSplit ε W x t → IsSplit ε W' (x ∘ β) t ∧ ∀ m ∈ leviOne ε W, m * t = t * m) → (∀ v, τ 1 v = v) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (s' + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) → (∀ y ∈ leviOne ε W, ∀ f f' : Fsp, (∀ g, f'.1 g = f.1 (g * y)) → σ (uMat y) (ι f) = ι f') → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → (∀ g, restr (leviOne ε W) F g ∈ Fsp) → ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → ∀ g, stageFun (leviOne ε W) Fsp ι F (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • σ (uMat m) (stageFun (leviOne ε W) Fsp ι F g) := by
  intro n a b ε j W W' β U V _ _ _ _ τ σ s s' Fsp ι hconj hsplit hτ hpair htrans F hF hmem u hu m hm x t ht g
  set M := leviOne ε W with hM
  have uMat_one : uMat (1 : UJ ε) = 1 := rfl
  have hlaw := (mem_indFun_top.1 hF).2
  have h1N : (1 : UJ ε) ∈ flagN ε W' := ⟨fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩

  have hN : ∀ u' ∈ flagN ε W', ∀ h, F (u' * h) = F h := fun u' hu' h => by
    have := hlaw u' hu' 1 (leviOne ε W').one_mem 0 1 isSplit_one h
    simpa [uMat_one, hτ, pairing] using this
  obtain ⟨ht', hcomm⟩ := hsplit x t ht
  have hA : ∀ h, F (t * h) = Complex.exp (pairing j (s + rho n j) x) • F h := fun h => by
    have := hlaw 1 h1N 1 (leviOne ε W').one_mem (x ∘ β) t ht' h
    simpa [uMat_one, hτ, hpair] using this
  have hr : restr M F (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • restr M F (m * g) := by
    funext m'
    by_cases hm' : m' ∈ M
    · rw [Pi.smul_apply, restr_of_mem _ _ hm', restr_of_mem _ _ hm']
      have e1 : m' * (u * m * t * g) = (m' * u * m'⁻¹) * (t * ((m' * m) * g)) := by
        rw [← mul_assoc t, ← hcomm _ (M.mul_mem hm' hm)]; group
      rw [e1, hN _ (hconj m' hm' u hu), hA, mul_assoc]
    · rw [Pi.smul_apply, restr_of_not_mem _ _ hm', restr_of_not_mem _ _ hm', smul_zero]
  have hr2 : ∀ h, restr M F (m * g) h = restr M F g (h * m) := fun h => by
    by_cases hh : h ∈ M
    · rw [restr_of_mem _ _ hh, restr_of_mem _ _ (M.mul_mem hh hm), mul_assoc]
    · rw [restr_of_not_mem _ _ hh, restr_of_not_mem _ _ (fun e => hh (by simpa using M.mul_mem e (M.inv_mem hm)))]
  rw [stageFun_of_mem ι (hmem g), stageFun_of_mem ι (hmem _)]
  have e2 : (⟨restr M F (u * m * t * g), hmem _⟩ : Fsp) = Complex.exp (pairing j (s + rho n j) x) • ⟨restr M F (m * g), hmem _⟩ :=
    Subtype.ext hr
  rw [e2, map_smul, htrans m hm ⟨_, hmem g⟩ ⟨_, hmem (m * g)⟩ hr2]

end GlobalTheory.RealInd.Stages
