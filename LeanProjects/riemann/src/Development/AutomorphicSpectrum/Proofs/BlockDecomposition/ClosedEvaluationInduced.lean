import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCompactModParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceLocalCoefficientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjShiftedEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCommuteShiftedEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantUnipotentActionTrivialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantLeviActionModulusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusMirabolicBlockFactorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLinearChangeModulusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalConstancyTwistedTranslateStatement

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.MemC
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cocompact (i t : ℕ) : ∃ C : Set (Mir k ((i + 1) + t)), IsCompact C ∧
    ∀ g : Mir k ((i + 1) + t), ∃ h ∈ MirabolicParabolic k (i + 1) t, ∃ c ∈ C, g = h * c := GlobalTheory.T.mirabolic_compact_mod_parabolic k i t

theorem smooth_eC {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) :
    IsOpen {g : Mir k ((i + 1) + t) | ∀ m, eC ψ f (m * g) = eC ψ f m} := GlobalTheory.T.isOpen_right_invariance_local_coefficient k i t ψ τ σ f

theorem conj_data {i t : ℕ} (h : MirabolicParabolic k (i + 1) t) :
    ∃ η : HPG k (i + 1) (t + 1), (η : Mir k ((i + 1) + t + 1)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∧
      pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1,
        (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)) := GlobalTheory.T.parabolic_proj_shifted_embedding k i t h

theorem conj_d {i t : ℕ} (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k) :
    ∃ u : HPG k (i + 1) (t + 1), (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1) ∧ (pgProj k (i + 1) (t + 1) u).2 = 1 ∧
      dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) =
        sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * (u : Mir k ((i + 1) + t + 1)) *
          dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) := GlobalTheory.T.unipotent_commute_shifted_embedding k i t h d

theorem qC_sigX_unip {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : HPG k (i + 1) (t + 1))
    (h1 : (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1)) (h2 : (pgProj k (i + 1) (t + 1) u).2 = 1)
    (w : τ.V ⊗[ℂ] σ.V) : qC τ σ (sigX τ σ u w) = qC τ σ w := GlobalTheory.T.coinvariant_unipotent_action_trivial k i t τ σ u h1 h2 w

theorem qC_sigX_levi {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (h : MirabolicParabolic k (i + 1) t) (η : HPG k (i + 1) (t + 1))
    (hη : pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1,
        (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k))) (w : τ.V ⊗[ℂ] σ.V) :
    qC τ σ (sigX τ σ η w) =
      ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 *
        dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) •
      sigC τ σ h (qC τ σ w) := GlobalTheory.T.coinvariant_levi_action_modulus k i t τ σ h η hη w

theorem dpowM_hgp {i t : ℕ} (s : ℝ) (h : MirabolicParabolic k (i + 1) t) :
    dpowM ((i + 1) + t) s (h : Mir k ((i + 1) + t)) =
      dpow (i + 1) s (gpProj k (i + 1) t h).1 *
        dpow (t + 1) s (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := GlobalTheory.T.modulus_mirabolic_block_factor k i t s h

theorem smInt_scale {t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (A : GL (Fin t) k) (φ : (Fin t → k) → W)
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k t) (fun d => φ ((A⁻¹ : GL (Fin t) k).val *ᵥ d)) =
      ((dpow t 1 A : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k t) φ := GlobalTheory.T.integral_linear_change_modulus k t W A φ l c

theorem integrand_lc {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}
    (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) ∧
    HasCompactSupport (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) := GlobalTheory.T.local_constancy_twisted_translate k i t ψ hψ τ σ f y

theorem dpow_add (n : ℕ) (a b : ℝ) (g : GL (Fin n) k) : dpow n (a + b) g = dpow n a g * dpow n b g := by
  unfold dpow
  rw [Complex.ofReal_add, absPow_add]
  rfl

theorem dpow_zero (n : ℕ) (g : GL (Fin n) k) : dpow n 0 g = 1 := by
  unfold dpow
  rw [Complex.ofReal_zero, absPow_zero]
  rfl

theorem isFinite_muD (t : ℕ) : @MeasureTheory.IsFiniteMeasureOnCompacts (Fin t → k) (_root_.borel _) _ (muD k t) := by
  letI : MeasurableSpace (Fin t → k) := borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  unfold muD
  infer_instance

theorem eval_mul {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (h : HPG k (i + 1) (t + 1))
    (x : Mir k ((i + 1) + (t + 1))) : evX f ((h : Mir k ((i + 1) + (t + 1))) * x) = sigX τ σ h (evX f x) :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 h x

theorem pointwise {i t : ℕ} (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (h : MirabolicParabolic k (i + 1) t) (y : Mir k ((i + 1) + t + 1)) (d : Fin (t + 1) → k) :
    qC τ σ (evX f (dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * y)) =
      ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 *
        dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) •
      sigC τ σ h (qC τ σ (evX f (dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) * y))) := by
  obtain ⟨η, hη1, hη2⟩ := conj_data h
  obtain ⟨u, hu1, hu2, hu3⟩ := conj_d h d
  rw [hu3, ← hη1, mul_assoc, mul_assoc]
  have e1 := eval_mul f η ((u : Mir k ((i + 1) + t + 1)) * (dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) * y))
  have e2 := eval_mul f u (dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) * y)
  refine (congrArg (qC τ σ) e1).trans ?_
  rw [qC_sigX_levi τ σ h η hη2]
  refine congrArg _ (congrArg _ ?_)
  refine (congrArg (qC τ σ) e2).trans ?_
  exact qC_sigX_unip τ σ u hu1 hu2 _

theorem last_inv {t : ℕ} (p : Mir k t) (d : Fin (t + 1) → k) :
    (((p : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) (Fin.last t) = d (Fin.last t) :=
  mulVec_last_of_mem k _ (inv_mem p.2) d

theorem scalar_one {i t : ℕ} (g : GL (Fin (i + 1)) k) (A : GL (Fin (t + 1)) k) :
    (dpow (i + 1) (-1 / 2) g * dpow (t + 1) (-1 / 2) A) * (dpow (t + 1) 1 A * (dpow (i + 1) (1 / 2) g * dpow (t + 1) (-1 / 2) A)) = 1 := by
  have h1 : dpow (i + 1) (-1 / 2) g * dpow (i + 1) (1 / 2) g = 1 := by
    rw [← dpow_add, show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, dpow_zero]
  have h2 : dpow (t + 1) (-1 / 2) A * dpow (t + 1) (-1 / 2) A * dpow (t + 1) 1 A = 1 := by
    rw [← dpow_add, ← dpow_add, show (-1 / 2 + -1 / 2 + 1 : ℝ) = 0 by norm_num, dpow_zero]
  calc _ = (dpow (i + 1) (-1 / 2) g * dpow (i + 1) (1 / 2) g) * (dpow (t + 1) (-1 / 2) A * dpow (t + 1) (-1 / 2) A * dpow (t + 1) 1 A) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = 1 := by rw [h1, h2, one_mul]

theorem equiv_eC {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (h : MirabolicParabolic k (i + 1) t) (m : Mir k ((i + 1) + t)) :
    eC ψ f ((h : Mir k ((i + 1) + t)) * m) = sigC τ σ h (eC ψ f m) := by
  letI : MeasurableSpace (Fin (t + 1) → k) := _root_.borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI := isFinite_muD (k := k) (t + 1)
  obtain ⟨g, hg⟩ : ∃ g, g = (gpProj k (i + 1) t h).1 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin (t + 1)) k, A = (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η, η = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = sEmb k ((i + 1) + t) m := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂˣ, κ = dpow (i + 1) (1 / 2) g * dpow (t + 1) (-1 / 2) A := ⟨_, rfl⟩
  have hp := fun d => pointwise ψ f h y d
  rw [← hη, ← hg, ← hA, ← hκ] at hp
  obtain ⟨l, c⟩ := integrand_lc ψ hψ f y
  obtain ⟨l', c'⟩ := integrand_lc ψ hψ f (η * y)
  let T : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (psiN τ).V ⊗[ℂ] σ.V := (κ : ℂ) • ((sigC τ σ h) ∘ₗ (qC τ σ))
  have e1 : qC τ σ (intC ψ f (η * y)) = ((dpow (t + 1) 1 A : ℂˣ) : ℂ) • T (intC ψ f y) := by
    have a1 := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) (qC τ σ) l' c'
    have a2 := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T l c
    have a3 := smInt_scale A (T ∘ fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y))
      (IsLocallyConstant.comp l T) (c.comp_left (map_zero T))
    refine a1.symm.trans (Eq.trans ?_ (a3.trans (congrArg _ a2)))
    congr 1
    funext d
    have b := hp d
    rw [mul_assoc] at b
    simp only [Function.comp, map_smul]
    rw [b, hA, last_inv, ← hA]
    simp only [T, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, Units.smul_def]
  have key : (((dpow (i + 1) (-1 / 2) g * dpow (t + 1) (-1 / 2) A : ℂˣ) : ℂ)) * (((dpow (t + 1) 1 A : ℂˣ) : ℂ) * (κ : ℂ)) = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (scalar_one g A)
    simpa only [Units.val_mul, Units.val_one, hκ] using this
  show ((dpowM ((i + 1) + t) (-1 / 2) ((h : Mir k ((i + 1) + t)) * m) : ℂˣ) : ℂ) •
      qC τ σ (intC ψ f (sEmb k _ ((h : Mir k ((i + 1) + t)) * m))) =
    sigC τ σ h (((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m)))
  rw [map_mul (sEmb k ((i + 1) + t)), ← hη, ← hy, e1, map_mul (dpowM ((i + 1) + t) (-1 / 2)), dpowM_hgp, ← hg, ← hA, map_smul]
  simp only [T, LinearMap.smul_apply, LinearMap.comp_apply, smul_smul, Units.val_mul] at key ⊢
  congr 1
  linear_combination ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) * key

theorem memC : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ),
    ∃ y : cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ), (y : smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ))).1.1 = eC ψ f := by
  intro k _ _ _ _ i t ψ hψ τ σ _ _ f
  have hind : eC ψ f ∈ indSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ) := fun h g => equiv_eC ψ hψ f h g
  have hsm : (⟨eC ψ f, hind⟩ : indSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)) ∈ smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ)) := by
    show IsOpen {g | ind (MirabolicParabolic k (i + 1) t) (sigC τ σ) g ⟨eC ψ f, hind⟩ = ⟨eC ψ f, hind⟩}
    convert smooth_eC ψ τ σ f using 3 with g
    rw [Subtype.ext_iff, funext_iff]
    rfl
  obtain ⟨C, hC, hcov⟩ := cocompact (k := k) i t
  exact ⟨⟨⟨_, hsm⟩, C, hC, fun g _ => hcov g⟩, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPG.MemC
end
