import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleKernelIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleIntegralVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTriangleTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTrianglePolynomialStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StageFactor

open MeasureTheory

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem ker_add_smul (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (P Q : PolF D WW.rank A.rank) (c : ℂ) (h : GA D WW) :
    X.ker ψ θ t (P + c • Q) h = fun g => X.ker ψ θ t P h g + c * X.ker ψ θ t Q h g := by
  funext g
  simp [Tri.ker, thetaKO, map_add, map_smul]

def linI (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (hint : ∀ P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) : PolF D WW.rank A.rank →ₗ[ℂ] (GA D WW → ℂ) where
  toFun P := X.I ψ θ t P
  map_add' P Q := by
    funext h
    have e := ker_add_smul X ψ θ t P Q 1 h
    simp only [one_smul, one_mul] at e
    simp only [Tri.I, Pi.add_apply, e]
    exact integral_add (hint P h) (hint Q h)
  map_smul' c Q := by
    funext h
    have e := ker_add_smul X ψ θ t 0 Q c h
    simp only [zero_add] at e
    have e0 : X.ker ψ θ t 0 h = 0 := by funext g; simp [Tri.ker, thetaKO]
    simp only [Tri.I, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, e, e0, Pi.zero_apply, zero_add]
    exact integral_const_mul c _

theorem linI_apply (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (hint : ∀ P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) (P : PolF D WW.rank A.rank) :
    linI X ψ θ t hint P = X.I ψ θ t P := rfl

theorem factor_of_parts (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (hint : ∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m)
    (hker : ∀ t t' P, X.I ψ θ t P = 0 → X.I ψ θ t' P = 0)
    (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank) (hlam : ∀ t, lam t ≠ 0)
    (hs : ∀ t P', (∀ h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') → X.I ψ θ t (s P') = lam t • X.I' ψ θ t P')
    (hconv : ∃ P', (∀ t h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' ψ θ t P' ≠ 0) :
    Factor X ψ θ lam := by
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · refine ⟨hlam, ModuleCat.of ℂ ℂ, MvPolynomial.lcoeff ℂ 0, MvPolynomial.lcoeff ℂ 0, fun _ => 0,
      fun z => ⟨MvPolynomial.C z, by simp⟩, fun t => hT.elim t, fun t => hT.elim t, fun t => hT.elim t,
      fun t => hT.elim t, 1, by simp, fun t => hT.elim t⟩
  · let K : Submodule ℂ (PolF D WW.rank A.rank) := LinearMap.ker (linI X ψ θ t₀ (hint t₀))
    have hK : ∀ t, LinearMap.ker (linI X ψ θ t (hint t)) = K := fun t => by
      ext P
      simp only [K, LinearMap.mem_ker, linI_apply]
      exact ⟨hker t t₀ P, hker t₀ t P⟩
    let Jb : T → ((PolF D WW.rank A.rank ⧸ K) →ₗ[ℂ] (GA D WW → ℂ)) := fun t =>
      K.liftQ (linI X ψ θ t (hint t)) (hK t).ge
    have hJb : ∀ t, Function.Injective (Jb t) := fun t => by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (hK t).le
    refine ⟨hlam, ModuleCat.of ℂ (PolF D WW.rank A.rank ⧸ K), K.mkQ, K.mkQ ∘ₗ s, fun t => (lam t)⁻¹ • Jb t,
      K.mkQ_surjective, fun t => ?_, hint, fun t P => ?_, fun t P' hP' => ?_, ?_⟩
    · intro x y hxy
      exact hJb t (smul_right_injective _ (inv_ne_zero (hlam t)) hxy)
    · show X.I ψ θ t P = lam t • ((lam t)⁻¹ • Jb t (K.mkQ P))
      rw [smul_smul, mul_inv_cancel₀ (hlam t), one_smul]
      rfl
    · show X.I' ψ θ t P' = (lam t)⁻¹ • Jb t (K.mkQ (s P'))
      have : Jb t (K.mkQ (s P')) = X.I ψ θ t (s P') := rfl
      rw [this, hs t P' hP', smul_smul, inv_mul_cancel₀ (hlam t), one_smul]
    · obtain ⟨P', hc, hne⟩ := hconv
      refine ⟨P', fun h0 => hne t₀ ?_, hc⟩
      have h1 : s P' ∈ K := (Submodule.Quotient.mk_eq_zero K).1 h0
      have h2 : X.I ψ θ t₀ (s P') = 0 := h1
      rw [hs t₀ P' (hc t₀)] at h2
      exact (smul_eq_zero.1 h2).resolve_left (hlam t₀)

end GlobalTheory.StageFactor

open GlobalTheory.StageFactor

theorem GlobalTheory.StageFactor.factor_stage : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ lam : T → ℂ, Factor X W.ψ W.θ lam := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.T.stage_triangle_kernel_integrable hP hK hL) (GlobalTheory.T.stage_triangle_integral_vanishing hP hK hL))
    (GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.T.exists_stage_triangle_transfer hP hK hL) (GlobalTheory.T.exists_stage_triangle_polynomial hP hK hL))
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hL G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h C hC D large₂ a b r T Lc μ hL G
  obtain ⟨lam, s, hlam, hs⟩ := h3 W S hW hN i j p q A A' WW X hX
  exact ⟨lam, factor_of_parts X W.ψ W.θ (h1 W S hW hN i j p q A A' WW X hX) (h2 W S hW hN i j p q A A' WW X hX) lam s hlam hs
    (h4 W S hW hN i j p q A A' WW X hX)⟩

end
