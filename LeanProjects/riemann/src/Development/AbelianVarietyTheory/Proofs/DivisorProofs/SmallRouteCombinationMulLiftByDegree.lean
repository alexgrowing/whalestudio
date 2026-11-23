import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SmallRoute

theorem setIntegral_mul_right_of_left_inv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] (Γ : Subgroup H) [Countable Γ] (ν : Measure H)
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] {fd : Set H} (hfd : IsFundamentalDomain Γ fd ν) {φ : H → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ u, φ (γ * u) = φ u) (hi : IntegrableOn φ fd ν) (k : H) :
    IntegrableOn (fun u => φ (u * k)) fd ν ∧ ∫ u in fd, φ (u * k) ∂ν = ∫ u in fd, φ u ∂ν := by
  have hmp : MeasurePreserving (· * k) ν ν := measurePreserving_mul_right ν k
  have hme : MeasurableEmbedding (· * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd' : IsFundamentalDomain Γ ((· * k⁻¹) ⁻¹' fd) ν := by
    refine hfd.preimage_of_equiv (measurePreserving_mul_right ν k⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ g : Γ, ∀ x, φ (g • x) = φ x := fun g x => hφ g g.2 x
  have hpre : (· * k) ⁻¹' ((· * k⁻¹) ⁻¹' fd) = fd := by
    ext u; simp
  refine ⟨?_, ?_⟩
  · have h1 : IntegrableOn φ ((· * k⁻¹) ⁻¹' fd) ν := (hfd'.integrableOn_iff hfd hinv).2 hi
    have h2 := (hmp.integrableOn_comp_preimage hme (f := φ) (s := (· * k⁻¹) ⁻¹' fd)).2 h1
    rw [hpre] at h2
    exact h2
  · have h3 := hmp.setIntegral_preimage_emb hme φ ((· * k⁻¹) ⁻¹' fd)
    rw [hpre] at h3
    rw [h3]
    exact hfd'.setIntegral_eq hfd hinv

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem mem_support_tensT (W : G.Weil) {X Y : Node} {p : Path T X Y} {τi : PolT G p →₀ ℂ} {τf : TotT G p} {d : PureT G p}
    (hd : d ∈ (tensT W τi τf).support) :
    ∃ d₀ ∈ τf.support, ∃ P, d = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d₀ P := by
  classical
  unfold tensT at hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d₀, hd₀, h⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  exact ⟨d₀, hd₀, P, Finset.mem_singleton.1 (Finsupp.support_single_subset h)⟩

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem theta_of_matched {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (hΘ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeSmall t i j)} (hd : d ∈ Θ'.support) :
    IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vT_is t i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _,
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _⟩

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem outer_left (W : G.Weil) (M : Vol G) {t : T} {i j : Fin D.R.m} {d : PureT G (routeSmall t i j)}
    (h2 : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2)
    (h1 : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2) (F : Fn G (.grid i (j + 1)))
    (g₁ : GA D (G.V (.grid (i + 1) j))) {γ : GA D (G.V (.grid i j))} (hγ : γ ∈ GQ (G.V (.grid i j)))
    (u : GA D (G.V (.grid i j))) : outer W M d F g₁ (γ * u) = outer W M d F g₁ u := by
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have hm := W.om_is (.mu t (i : ℕ) j) ⟨i.2.le, j.2⟩
  unfold outer
  congr 1
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (γ * u) d.2 = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u d.2
    unfold thetaKO
    have e : ((negGA _ g₁, γ * u) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (1, γ) * (negGA _ g₁, u) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h2)
  · refine integral_congr_ae (.of_forall fun g => ?_)
    show thetaKO (W.om (.mu t (i : ℕ) j)) (γ * u) g d.1.2 * F g = thetaKO (W.om (.mu t (i : ℕ) j)) u g d.1.2 * F g
    unfold thetaKO
    have e : ((γ * u, g) : GA D (G.pS (.mu t (i : ℕ) j)) × GA D (G.pT (.mu t (i : ℕ) j))) = (γ, 1) * (u, g) := by simp
    rw [e, map_mul, Module.End.mul_apply, hm.om_aut γ hγ 1 (one_mem _) _ (hm.om_pres _ _ h1)]

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

theorem zdeg_mul_liftT : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j)))
    (z : GA D (G.V (.grid i j)) →₀ ℂ),
    (∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    zdeg z * liftT W M (routeSmall t i j) Θ' F g₁ =
      Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ F hF hB g₁ z
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid i j))
  haveI := hH
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ (M.ν (.grid i j)) hH
  have key : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)) ∧
      ∫ u in M.fd (.grid i j), outer W M d F g₁ (u * k) ∂M.ν (.grid i j) =
        ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := fun d hd k => by
    obtain ⟨h2, h1⟩ := theta_of_matched hΘ hd
    refine setIntegral_mul_right_of_left_inv (GQ (G.V (.grid i j))) (M.ν (.grid i j)) hfd
      (fun γ hγ u => outer_left W M h2 h1 F g₁ hγ u) ?_ k
    exact (hB d hd).2 g₁
  refine ⟨fun d hd k => (key d hd k).1, ?_⟩
  rw [liftT_routeSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : ∫ u in M.fd (.grid i j), translates z (outer W M d F g₁) u ∂M.ν (.grid i j) =
      zdeg z * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := by
    unfold translates zdeg
    simp only [Finsupp.sum]
    rw [integral_finset_sum _ fun k _ => ((key d hd k).1.integrable.const_mul _),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, (key d hd k).2]
  rw [e]
  ring

end GlobalTheory.SmallRoute
