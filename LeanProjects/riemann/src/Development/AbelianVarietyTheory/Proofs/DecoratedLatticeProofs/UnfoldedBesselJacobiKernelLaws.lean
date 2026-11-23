import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.UnfKer

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem zEll_rat (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) : zEll T ρ z ∈ ratMx D T.rank ρ := by
  refine ⟨vecMulVec z (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0), ?_⟩
  rw [zEll, GlobalTheory.CharLaws.ell_eq]
  ext i j
  change incA D (_ * _) = _
  rw [map_mul]; rfl

theorem incAdj_rat {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {y : Mx D S.rank ρ}
    (hy : y ∈ ratMx D S.rank ρ) : d.incAdj S y ∈ ratMx D T.rank S.rank := by
  rw [d.incAdj_apply, d.incY_apply]
  exact ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))

theorem jacT_rat (hψ : IsCharAF D.host.F ψ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {y : Mx D S.rank ρ}
    (hy : y ∈ ratMx D S.rank ρ) {n : GA D T} (hn : n ∈ GQ T) {f : WO S T₀ → ℂ} (hf : IsThetaFunO ψ S T₀ f) :
    jacT ψ d S y n f 0 = f 0 := by
  have h1 := incAdj_rat d S hy
  have h2 : mt T n⁻¹ ⬝ d.incAdj S y ∈ ratMx D T.rank S.rank := ratMx_mul ((mem_GQ_iff T _).1 (inv_mem hn)) h1
  obtain ⟨a, ha⟩ := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 _ h1 _ h2
  obtain ⟨δ, hδ⟩ : ptT d S y n ∈ ratMx D T₀.rank S.rank := ratMx_mul (rat_mem _) h2
  have h3 := hf.quasi δ 0
  rw [show ratW T₀ S δ = ptT d S y n from hδ, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul,
    add_zero] at h3
  rw [jacT, Pi.smul_apply, cenT, ha, hψ.2.2.1, one_smul, heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul,
    zero_add, h3]

variable {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)

theorem flatBF_eq (Ψ : WO B.V J.W → ℂ) : flatBF s Ψ =
    flatAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat J.d.e) (yZero B.V₀ ρ (vecB B.o B.ζ)) Ψ := rfl

theorem flatBF_theta {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) : IsThetaFunO ψ B.V₀ J.W₀ (flatBF s Ψ) :=
  (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e
    (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).1.1 _ Ψ hΨ).2

variable {om' : Om B.V₀ J.W} (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om')
include hom

theorem flat_rat {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) {γ₀ : GA D B.A} (h₀ : γ₀ ∈ GQ B.A) {γ : GA D J.W}
    (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d) : flatBF s (s.om (embA B.d B.o γ₀, γ) Ψ) 0 = flatBF s Ψ 0 := by
  obtain ⟨n, hn, h', rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff J.d).1 hγ.2
  obtain ⟨hnQ, hh'⟩ := ((GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).2.2.2.2.2 n hn h').1 hγ.1
  have hψ := s.weil.std.1
  have hΞ := flatBF_theta s hΨ
  have hy : yZero B.V₀ ρ (vecB B.o B.ζ) ∈ ratMx D B.V₀.rank ρ := neg_mem (zEll_rat _ _ _)
  have e1 : flatBF s (s.om (embA B.d B.o 1, n * J.d.emb0 h') Ψ) 0 = flatBF s Ψ 0 := by
    rw [GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom Ψ hΨ 1 n hn h', psiFlag_eq, GlobalTheory.CharLaws.psiBes_rat ψ J.d hψ.2.2.1 1 0 hnQ,
      star_one, one_smul, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply, opA,
      jacT_rat hψ J.d B.V₀ hy hnQ (s.weil₀.om_pres _ _ hΞ), s.weil₀.om_aut 1 (one_mem _) h' hh' _ hΞ]
  have hΨ' := s.weil.om_pres (embA B.d B.o 1, n * J.d.emb0 h') Ψ hΨ
  have e2 : s.om (embA B.d B.o γ₀, n * J.d.emb0 h') Ψ =
      s.om (embA B.d B.o γ₀, 1 * J.d.emb0 1) (s.om (embA B.d B.o 1, n * J.d.emb0 h') Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul s.om, Prod.mk_mul_mk, map_one, map_one, mul_one, mul_one, one_mul]
  rw [e2, GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom _ hΨ' γ₀ 1 (one_mem _) 1, psiFlag_eq,
    GlobalTheory.CharLaws.psiBes_rat ψ J.d hψ.2.2.1 1 0 (one_mem _), star_one, one_smul, opA, jacT_one, Prod.mk_one_one, map_one,
    Module.End.one_apply, id, s.weil₀.om_aut _ (B.o.emb_mem_GQ h₀ (one_mem _)) 1 (one_mem _) _ (flatBF_theta s hΨ'), e1]

theorem flat_left {Φ : WO B.V J.W → ℂ} (hΦ : IsThetaFunO ψ B.V J.W Φ) {γ₀ : GA D B.A} (h₀ : γ₀ ∈ GQ B.A) {γ : GA D J.W}
    (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d) (g : GA D B.A) (h : GA D J.W) :
    flatBF s (s.om (embA B.d B.o (γ₀ * g), γ * h) Φ) 0 = flatBF s (s.om (embA B.d B.o g, h) Φ) 0 := by
  rw [map_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
  exact flat_rat s hom (s.weil.om_pres _ _ hΦ) h₀ hγ

end GlobalTheory.UnfKer

namespace GlobalTheory.Unf

theorem kerBF_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → Continuous (kerBF s φ G Φ) ∧ (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, kerBF s φ G Φ (γ * h) = kerBF s φ G Φ h) ∧ (∀ γ ∈ GQ B.A, ∀ h₀ h, flatBF s (s.om (embA B.d B.o (γ * h₀), h) Φ) 0 = flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) ∧ ∀ h h' (n : flagN J.d), kerBF s φ G Φ (n.1 * J.d.emb0 h' * h) = fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flatBF s (s.om (1, h) Φ)) h' n := by
  intro D ψ ρ B J s om' hom φ G Φ hφ hG hΦ
  have h3 : ∀ γ ∈ GQ B.A, ∀ h₀ h, flatBF s (s.om (embA B.d B.o (γ * h₀), h) Φ) 0 =
      flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0 := fun γ hγ h₀ h => by
    have := GlobalTheory.UnfKer.flat_left s hom hΦ hγ (one_mem _) h₀ h
    rwa [one_mul] at this
  refine ⟨?_, fun γ hγ h => ?_, h3, fun h h' n => ?_⟩
  · have hc := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e
      (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).1.1 Φ hΦ
    have he : Continuous (embA B.d B.o) :=
      B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
    have hq : Continuous fun p : GA D B.A × GA D J.W =>
        (((embA B.d B.o p.1, p.2), yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
          (GA D B.V × GA D J.W) × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      ((he.comp continuous_fst).prodMk continuous_snd).prodMk continuous_const
    have hF : Continuous fun p : GA D B.A × GA D J.W => flatBF s (s.om (embA B.d B.o p.1, p.2) Φ) 0 := by
      refine (hc.comp hq).congr fun p => ?_
      rw [Function.comp_apply, GlobalTheory.UnfKer.flatBF_eq]
    have hK : Continuous (Function.uncurry fun (h₀ : GA D B.A) (h : GA D J.W) =>
        φ h₀ * flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) := by
      refine ((hφ.2.comp continuous_fst).mul hF).congr fun p => ?_
      rw [Function.uncurry, Pi.mul_apply, Function.comp_apply]
    exact hG.2.1.mul (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D B.A B.cpt B.vA (GA D J.W) _ hK
      (fun γ hγ g p => by rw [hφ.1 γ hγ, h3 γ hγ])).2.1
  · rw [kerBF, kerBF, hG.1 γ hγ.1]
    congr 2
    funext h₀
    have := GlobalTheory.UnfKer.flat_left s hom hΦ (one_mem _) hγ h₀ h
    rw [one_mul] at this
    rw [this]
  · rw [kerBF, fjAllFun, rTrans, mul_assoc (G _), ← integral_const_mul (star _)]
    congr 2
    funext h₀
    have e : s.om (embA B.d B.o h₀, n.1 * J.d.emb0 h' * h) Φ =
        s.om (embA B.d B.o h₀, n.1 * J.d.emb0 h') (s.om (1, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul s.om, Prod.mk_mul_mk, mul_one]
    rw [e, GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom _ (s.weil.om_pres _ _ hΦ) h₀ n.1 n.2 h', Pi.smul_apply, smul_eq_mul, fjKer]
    ring

end GlobalTheory.Unf

end
