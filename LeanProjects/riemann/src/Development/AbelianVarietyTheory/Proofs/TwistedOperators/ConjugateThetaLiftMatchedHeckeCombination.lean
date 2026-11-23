import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaPForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFormsSpherical
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumFockVectorsIsVacuumOffLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvalInjective

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjLiftHecke

variable {D : D7}

theorem theta_form_conj {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {P : Pl D.host.E} (hW : IsWeilDatumO ψ S T χS χT om)
    (hs : S.SigOK) (hp : S.IsPosDef) {Kf : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {ν : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hν : IsMeasDef S Kf ν 𝓕) (hfix : GlobalTheory.Hk3.VacFix ψ om P) {cS cT : List ℤ →₀ ℂ}
    (hM : GlobalTheory.Hk3.Match ψ om P (GlobalTheory.Hk3.dualC cS) cT) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ S.rank) (χ' : (levEnv S β L).J →* ℂˣ) (hχ : ∀ k, (levEnv S β L).χ k = 1 → χ' k = 1)
    (hG : ∀ k ∈ GlobalTheory.Hk3.hyp S P, k ∈ GfC S) {f f' : Bridge.Gf S → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (hsph : ∀ k ∈ GlobalTheory.Hk3.hyp S P, ∀ h, f (h * (finHom S).rangeRestrict k) = f h) (hf' : f' = GlobalTheory.Hk3.hkF S P cS f)
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ φ, GlobalTheory.Hk3.IsVacAt ψ S T P (pt φ))
    (io : c.W →ₗ[ℂ] PolF D T.rank S.rank) {u u' : GA D T → ℂ}
    (hu : ∀ g, u g = ∫ h in 𝓕, thetaKO om h g (pt (io (c.ext f h))) ∂ν)
    (hu' : ∀ g, u' g = ∫ h in 𝓕, thetaKO om h g (pt (io (c.ext f' h))) ∂ν) : u' = GlobalTheory.Hk3.hk T P cT u := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  funext g
  have key := GlobalTheory.DefLiftHecke.theta_comb hW hpos hν.1.1 hν.2 hfix hM (pt ∘ₗ io) (fun w => hpt _) (c.ext f)
    (GlobalTheory.ConjThetaIntegral.ext_continuous c hc β L χ' hχ hf) (GlobalTheory.ThetaIntegrand.ext_invariant c hf)
    (fun k hk h => by
      rw [GlobalTheory.DefLiftHecke.ext_mul c hc f (hG k hk) h, hsph k hk]
      rfl) g
  rw [hu', funext hu, hf']
  simp only [GlobalTheory.DefLiftHecke.ext_hkF c hc]
  exact key

theorem theta_right_hyp {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    {P : Pl D.host.E} (hfix : GlobalTheory.Hk3.VacFix ψ om P) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)}
    {φ : GA D S → (WO S T → ℂ)} (hφ : ∀ h, GlobalTheory.Hk3.IsVacAt ψ S T P (φ h)) {u : GA D T → ℂ}
    (hu : ∀ g, u g = ∫ h in 𝓕, thetaKO om h g (φ h) ∂ν) : ∀ k ∈ GlobalTheory.Hk3.hyp T P, ∀ g, u (g * k) = u g := by
  intro k hk g
  rw [hu, hu]
  refine congrArg (fun w : GA D S → ℂ => ∫ h in 𝓕, w h ∂ν) (funext fun h => ?_)
  unfold thetaKO
  rw [show ((h, g * k) : GA D S × GA D T) = (h, g) * (1, k) by simp, map_mul, Module.End.mul_apply,
    hfix _ (hφ h) 1 (GlobalTheory.DefLiftHecke.one_mem_hyp _ P) k hk]

theorem gaL_hk_of_hyp {G : Type} [Group G] [Fintype G] {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {L : LevDat D.host.E ℂ V.rank}
    {P : Pl D.host.E} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (eG : G ≃* G0 L.Pg L.r) (z : G → ℂ) (c : List ℤ →₀ ℂ) {Φ : GA D V → ℂ}
    (hΦ : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, Φ (h * k) = Φ h) :
    gaL V β L eG z (GlobalTheory.Hk3.hk V P c Φ) = GlobalTheory.Hk3.hk V P c (gaL V β L eG z Φ) := by
  obtain ⟨n, hB⟩ := hβ
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.LevOp.level_operators V β Λ _ L hB P (GlobalTheory.DefLiftHecke.one_pow_notMem P n) hP
  exact GlobalTheory.DefLiftHecke.gaL_hk eG z fun g0 => h4 c g0 _ hΦ

theorem eq_of_eval {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {Hh : Type} [NormedAddCommGroup Hh]
    [InnerProductSpace ℂ Hh] (e : Hh →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hip : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) {Wa : Submodule ℂ (MMap M)} (hr : LinearMap.range e = Wa)
    (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) {a : Hh} {U : MMap M} (hU : U ∈ Wa) (h : e a v = U v) : e a = U := by
  rw [← hr] at hU
  obtain ⟨b, rfl⟩ := hU
  exact congrArg e (GlobalTheory.EvalAtUnitVector.eval_injective M Hh e d μ 𝓕 hip v hv h)

set_option maxHeartbeats 1000000 in
theorem lift_match : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → GlobalTheory.GalLift.IsProjOf R i σ thP th → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.VacFix R.ψ ω P → ∀ cV cW, GlobalTheory.Hk3.Match R.ψ ω P (GlobalTheory.Hk3.dualC cV) cW → ∀ y y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) → (R.HW i σ).e (th y') = postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L hT i σ c c₁ H j hK hj μ' η' th ω f₀ f B io thP hD hPr P hG hfix cV cW hM y y' hy
  have hW := hD.1
  have hV := hD.2.1
  have hIo := hD.2.2.1
  have hTh := hD.2.2.2
  refine hj.model.elim fun χ' hm => ?_
  have hχ := hm.1
  have hH := hm.2
  have hvac := GlobalTheory.T.conjugateDatum_fockVectors_isVacuum_off_level R hC.lev hC.models.inf i σ f₀ f B hV P hG
  have hform : ∀ x, H.e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).J χ' :=
    fun x => hH.2.1.le (LinearMap.mem_range_self _ x)
  have hχ1 : ∀ k, (levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k = 1 → χ' k = 1 := fun k hk =>
    Units.ext (GlobalTheory.ConjThetaIntegral.conjVal_one (hχ k) (congrArg Units.val hk))
  have hsph := (GlobalTheory.ConjSph.conjForms_spherical R hC.lev i σ c c₁ H j _ hj P hG cV y).1
  refine (hC.lev.βV i).elim fun nV hBV => ?_
  have hlevV := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) _ (R.datVt i A.μ0) hBV P
    (GlobalTheory.DefLiftHecke.one_pow_notMem P nV) hG).1
  have hStep : ∀ w : LowT (R.MW i σ), thP ((c.ext ∘ₗ H.e).rangeRestrict y') w =
      GlobalTheory.Hk3.hk (Wc D i) P cW (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w) := fun w => by
    refine theta_form_conj hW (D.sp.V_sig _) (hC.models.vpos i) (hC.models.νV i A.μ0) hfix hM c hj.coef (R.βV i)
      (R.datVt i A.μ0) χ' hχ1 (fun k hk => (hlevV k hk).1.1) (hform y) hsph hy
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f) hvac (io w)
      (fun g => hTh.eq _ w g) (fun g => hTh.eq _ w g)
  have hWinv : ∀ (w : LowT (R.MW i σ)), ∀ k ∈ GlobalTheory.Hk3.hyp (Wc D i) P, ∀ g,
      thP ((c.ext ∘ₗ H.e).rangeRestrict y) w (g * k) = thP ((c.ext ∘ₗ H.e).rangeRestrict y) w g := fun w =>
    theta_right_hyp hfix (fun h => hvac _) (fun g => hTh.eq _ w g)
  have hGW : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P :=
    fun PP h => hG PP (h.imp_right fun h => absurd h (Finset.notMem_empty _))
  have hcomm : ∀ w : LowT (R.MW i σ), R.eWf i σ (GlobalTheory.Hk3.hk (Wc D i) P cW (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w)) =
      GlobalTheory.Hk3.hk (Wc D i) P cW (R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w)) := fun w =>
    gaL_hk_of_hyp (hC.lev.βW i) hGW R.eG _ cW (hWinv w)
  have hmod := hC.models.HW i σ
  have hU : (R.HW i σ).e (th y) ∈ R.Wall i σ := hmod.2.1.le (LinearMap.mem_range_self _ _)
  have hU' : postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) ∈ R.Wall i σ :=
    (GlobalTheory.DefLiftHecke.mult_laws hC.models.inf (R.MW i σ) (hC.lev.βW i) (L := R.datWp i R.triv) hGW R.eG
      (RealDat.eC (A := A) σ) cW hU).1
  refine hIo.2.2.elim fun v hv => hv.elim fun _ hw => ?_
  refine eq_of_eval (R.MW i σ) (R.HW i σ).e _ (R.νW i) (R.fdW i) hmod.2.2 hmod.2.1 (fun ρ => v ρ) hw.1 hU' ?_
  exact (hPr y' v).trans ((congrArg (R.eWf i σ) (hStep _)).trans ((hcomm _).trans
    ((congrArg (GlobalTheory.Hk3.hk (Wc D i) P cW) (hPr y v).symm).trans (postOn_apply _ _ _ _).symm)))

end GlobalTheory.ConjLiftHecke
