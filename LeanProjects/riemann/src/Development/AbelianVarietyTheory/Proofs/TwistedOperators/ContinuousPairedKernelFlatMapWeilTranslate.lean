import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.XLastLin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselFlatMapEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLawsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedDownIsTameThetaFunctional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.KerContFB

set_option maxHeartbeats 400000 in

theorem kerFB_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → Continuous fun q : GA D B.V × GA D J.W₀ × GA D B.A => contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ))) (omz (q.2.1, 1) Φ₀) 0 := by
  intro D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.JacMean.xLast_lin B.d B.o B.line
  have hn : ∀ t, ψ t * star (ψ t) = 1 := fun t => by
    have h1 : ‖ψ t‖ = 1 := s.weil₀.std.1.2.1 t
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  have hpsi : psiBes ψ B.d 1 (vecB B.o B.ζ) 1 = 1 :=
    (GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1).2.1 _ 1 (one_mem _)
  have hfl : ∀ Ψ, flFB s Ψ = flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0 Ψ := fun Ψ => by
    simp only [flFB, flatS, hxe]
  have heq : ∀ h h₀ h₁, s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ)) =
      flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) := by
    intro h h₀ h₁
    have e := GlobalTheory.T.jacobiToBesselFlatMap_equivariant D ψ σ J B s (s.om (1, h) Φ) (s.weil.om_pres _ Φ hΦ) h₀ 1 (one_mem _) h₁
    rw [hpsi, star_one, one_smul, one_mul] at e
    rw [← e, hfl]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hth : ∀ h, IsThetaFunO ψ J.W₀ B.V₀ (flFB s (s.om (1, h) Φ)) := fun h => by
    rw [hfl]
    exact (GlobalTheory.Unf.Flat.flatLaw D ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU x hx 0 _
      (s.weil.om_pres _ Φ hΦ)).2
  set K : Mx D B.L.rank J.W₀.rank → GA D B.V × GA D J.W₀ × GA D B.A → ℂ := fun w q =>
    s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ)) (B.o.jB ⬝ w) * star (omz (q.2.1, 1) Φ₀ w) with hK
  have hP : ∀ q : GA D B.V × GA D J.W₀ × GA D B.A, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (q.2.1, B.o.emb (q.2.2, 1))
      (flFB s (s.om (1, q.1) Φ))) (omz (q.2.1, 1) Φ₀) 0 = ∫ w in vL.𝓕, K w q ∂vL.μ := fun q => by
    simp only [contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, hK]
  have hc : Continuous (Function.uncurry K) := by
    have h1 := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x hx Φ hΦ
    have hJ := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ χ χz omz homz Φ₀ hΦ₀
    have hK' : Function.uncurry K = fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0
          (s.om (J.d.emb0 p.2.2.1, embA B.d B.o p.2.2.2 * p.2.1) Φ) (B.o.jB ⬝ p.1) * star (omz (p.2.2.1, 1) Φ₀ p.1) := by
      funext p
      simp only [Function.uncurry, hK, heq]
    rw [hK']
    have ha : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => p.2.2.1 :=
      continuous_fst.comp (continuous_snd.comp continuous_snd)
    have hb : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => p.2.2.2 :=
      continuous_snd.comp (continuous_snd.comp continuous_snd)
    have hh : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => p.2.1 :=
      continuous_fst.comp continuous_snd
    have hA : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => embA B.d B.o p.2.2.2 := by
      simp only [embA_apply]
      exact B.d.continuous_embed.comp (B.o.continuous_emb.comp (hb.prodMk continuous_const))
    have h2 : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        (((J.d.emb0 p.2.2.1, embA B.d B.o p.2.2.2 * p.2.1) : GA D J.W × GA D B.V), ((0 : Mx D J.W₀.rank σ),
          (B.o.jB ⬝ p.1 : WO J.W₀ B.V₀))) :=
      ((J.d.continuous_embed.comp ha).prodMk (hA.mul hh)).prodMk
        (continuous_const.prodMk (continuous_const.matrix_mul continuous_fst))
    have h3 : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0
          (s.om (J.d.emb0 p.2.2.1, embA B.d B.o p.2.2.2 * p.2.1) Φ) (B.o.jB ⬝ p.1) := by
      convert h1.comp h2 using 2
      simp only [Function.comp_apply]
    have h4 : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        omz (p.2.2.1, 1) Φ₀ p.1 :=
      hJ.comp (f := fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        (((p.2.2.1, 1) : GA D J.W₀ × GA D B.L), (p.1 : WO J.W₀ B.L))) ((ha.prodMk continuous_const).prodMk continuous_fst)
    exact h3.mul h4.star
  have hper : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ w q, K (γ + w) q = K w q := by
    rintro _ ⟨γ, rfl⟩ w q
    have e1 := (s.weil₀.om_pres (q.2.1, B.o.emb (q.2.2, 1)) _ (hth q.1)).quasi (B.o.iB * γ) (B.o.jB ⬝ w)
    have e2 := (homz.om_pres (q.2.1, 1) Φ₀ hΦ₀).quasi γ w
    rw [ratW_eq, rat_mul] at e1
    rw [ratW_eq] at e2
    have e3 : symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ w) = symplOH J.W₀ B.L (rat γ) w := by
      rw [B.o.symplOH_resT]
      simp only [OrthDec.resT_apply, cancel₂ B.o.pA_jB, cancel₂ B.o.pB_jB, Matrix.zero_mul, Matrix.one_mul,
        symplOH_zero_left, zero_add]
    change s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ)) (B.o.jB ⬝ (rat γ + w)) *
        star (omz (q.2.1, 1) Φ₀ (rat γ + w)) =
      s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ)) (B.o.jB ⬝ w) * star (omz (q.2.1, 1) Φ₀ w)
    rw [Matrix.mul_add, e2]
    refine (congrArg (· * _) e1).trans ?_
    change ψ (-symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ w)) * _ * _ = _
    rw [e3, star_mul', mul_mul_mul_comm, hn, one_mul]
  obtain ⟨-, hcont, -, -⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D _ _ vL _ K hc hper
  have : (fun q : GA D B.V × GA D J.W₀ × GA D B.A => contractT B.o J.W₀ vL.μ vL.𝓕
      (s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ))) (omz (q.2.1, 1) Φ₀) 0) =
      fun q => ∫ w in vL.𝓕, K w q ∂vL.μ := funext hP
  rw [this]; exact hcont

end GlobalTheory.KerContFB

end
