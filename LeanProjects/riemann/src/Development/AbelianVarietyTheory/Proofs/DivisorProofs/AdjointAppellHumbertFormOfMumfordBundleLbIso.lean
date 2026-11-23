import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupSixTermRelationToZpowForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.AdjFwd

theorem adjoint_hermForm_of_lbIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (N : LB A.left), N.IsLB → Out.RelAmple A N → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (f f' : A ⟶ A) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) → ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  intro A _ _ g hA _ N _ _ M u Hm χ hM hF f f' F F' hf hf' e e' hiso
  haveI := hf
  haveI := hf'
  obtain ⟨Mr, hMr, ⟨c⟩⟩ := GlobalTheory.AHWeilAny.exists_cubical A hA M hM
  subst hMr
  have hR := GlobalTheory.AdjPolLocal.rosatiAdj_of_lbIso _ A Mr.L f f' hM hiso
  have hFl : ∀ a : u.Λ, F a ∈ u.Λ := fun a => by rw [← u.ker, e, (u.ker _).2 a.2, MonObj.one_comp]
  have hF'l : ∀ a : u.Λ, F' a ∈ u.Λ := fun a => by rw [← u.ker, e', (u.ker _).2 a.2, MonObj.one_comp]
  refine GlobalTheory.HermAdjoint.adjoint_of_im Hm F F' _ u.full fun a ha b hb => ?_
  obtain ⟨E₁, hE₁⟩ := GlobalTheory.AHWeilFactor.im_hermForm_int hM u hF ⟨_, hFl ⟨a, ha⟩⟩ ⟨b, hb⟩
  obtain ⟨E₂, hE₂⟩ := GlobalTheory.AHWeilFactor.im_hermForm_int hM u hF ⟨a, ha⟩ ⟨_, hF'l ⟨b, hb⟩⟩
  have hE : E₁ = E₂ := GlobalTheory.HermAdjoint.int_eq_of_exp fun n hn => by
    have hx := GlobalTheory.HermAdjoint.ex_period_pow u hn ⟨a, ha⟩
    have hy := GlobalTheory.HermAdjoint.ex_period_pow u hn ⟨b, hb⟩
    have hy' : (u.ex ((n : ℂ)⁻¹ • b) ≫ f') ^ n = 1 := by
      rw [← MonObj.pow_comp]
      exact (congrArg (· ≫ f') hy).trans (MonObj.one_comp _)
    let c₁ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (E₁ : ℂ) / n))
    let c₂ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (E₂ : ℂ) / n))
    have v₁ : Out.WeilIs A Mr.L n (u.ex ((n : ℂ)⁻¹ • a) ≫ f) (u.ex ((n : ℂ)⁻¹ • b)) (unitOn c₁) := by
      rw [← e, map_smul]
      refine GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm A hA Mr.L hM g u Hm χ hF n (F a) b c₁ hn
        (hFl ⟨a, ha⟩) hb ?_
      show Complex.exp _ = _
      rw [← hE₁, Complex.ofReal_intCast]
    have v₂ : Out.WeilIs A Mr.L n (u.ex ((n : ℂ)⁻¹ • a)) (u.ex ((n : ℂ)⁻¹ • b) ≫ f') (unitOn c₂) := by
      rw [← e', map_smul]
      refine GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm A hA Mr.L hM g u Hm χ hF n a (F' b) c₂ hn
        ha (hF'l ⟨b, hb⟩) ?_
      show Complex.exp _ = _
      rw [← hE₂, Complex.ofReal_intCast]
    have v₁' := (GlobalTheory.WeilCube.weilIs_rosati c GlobalTheory.globalFns_holds hA f f' hR hx hy _).1 v₁
    obtain ⟨e₀, he₀⟩ := GlobalTheory.WeilCube.exists_isRatio c n _ _ hx hy'
    have h₁ := (GlobalTheory.WeilCube.weilIs_iff c GlobalTheory.globalFns_holds hA hx hy' he₀ _).1 v₁'
    have h₂ := (GlobalTheory.WeilCube.weilIs_iff c GlobalTheory.globalFns_holds hA hx hy' he₀ _).1 v₂
    exact congrArg Units.val (GlobalTheory.HermAdjoint.unitOn_injective (h₁.trans h₂.symm))
  show (F a ⬝ᵥ Hm *ᵥ star b).im = (a ⬝ᵥ Hm *ᵥ star (F' b)).im
  rw [← hE₁, ← hE₂, hE]

end GlobalTheory.AdjFwd
