import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateFixesThetaDeepLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharHalfSymplecticMovedFinitePointTriviaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelCurvePhaseEqOfCloseStatement

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedTr
variable {D : D7}

theorem heisO_add_eq (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ u : WO S T) (F : WO S T → ℂ) :
    heisO ψ S T (w₀ + u) F = ψ (-symplOH S T w₀ u) • heisO ψ S T w₀ (heisO ψ S T u F) := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.IndefR.Fin.symplOH_add_right, Formalism.IndefR.Fin.symplOH_add_left, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, add_assoc]
  have h1 : ψ (-symplOH S T w₀ u) * ψ (symplOH S T w₀ u) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (-(ψ (symplOH S T w w₀) * ψ (symplOH S T w u) * F (w + (w₀ + u)))) * h1

theorem closeTo_of_mul {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {k m : ℕ} {g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)}
    {g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)} {z z' : Matrix (Fin N') (Fin N) D.host.E}
    (h : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc (k * m) g g' z z') : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc m g g' z z' := by
  intro i j
  obtain ⟨t, ht, e⟩ := h i j
  refine ⟨(k : Formalism.MainNotions.StandardLatticesGL3.AE D) * t, ?_, ?_⟩
  · have : (k : Formalism.MainNotions.StandardLatticesGL3.AE D) * t = k • t := by rw [nsmul_eq_mul]
    rw [this]; exact AddSubgroup.nsmul_mem _ ht k
  · rw [e]; push_cast; ring

theorem moved_translate : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • om (g, h) (heisO ψ S T (finPt hS hT r z) f₀) =
      Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') • heisO ψ S T (finPt hS hT r z') (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset χS χT om hom x y g h hg hh f₀ hf₀ z
  have hF := hom.om_pres (g, h) f₀ hf₀
  obtain ⟨n₁, hn₁, H₁⟩ := GlobalTheory.T.heisenbergTranslate_fixes_theta_deepLevel ψ θ S T hS hT cc δ r hset x y g h hg hh _ hF z
  obtain ⟨n₂, hn₂, H₂⟩ := GlobalTheory.T.standardChar_halfSymplectic_movedFinitePoint_trivial ψ θ S T hS hT cc δ r hset x y g h hg hh z
  obtain ⟨n₃, hn₃, H₃⟩ := GlobalTheory.T.exists_level_curvePhase_eq_of_close cc δ hset.crv x y z
  refine ⟨n₁ * n₂ * n₃, by positivity, fun z' hz' => ?_⟩
  have c1 : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n₁ (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' :=
    closeTo_of_mul (k := n₂ * n₃) (by rwa [show n₂ * n₃ * n₁ = n₁ * n₂ * n₃ by ring])
  have c2 : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n₂ (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' :=
    closeTo_of_mul (k := n₁ * n₃) (by rwa [show n₁ * n₃ * n₂ = n₁ * n₂ * n₃ by ring])
  have c3 : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n₃ (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' :=
    closeTo_of_mul (k := n₁ * n₂) (by rwa [show n₁ * n₂ * n₃ = n₁ * n₂ * n₃ by ring])
  rw [hom.om_heis g h _ f₀ hf₀, H₃ z' c3]
  have e : actO S T g h (finPt hS hT r z) =
      finPt hS hT r z' + (actO S T g h (finPt hS hT r z) - finPt hS hT r z') := by abel
  have hψ : ψ (-symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) = 1 := by
    have h2 := H₂ z' c2
    have h0 : ψ (-symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) *
        ψ (symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rwa [h2, mul_one] at h0
  rw [e, heisO_add_eq, H₁ z' c1, hψ, one_smul]

end GlobalTheory.MovedTr
