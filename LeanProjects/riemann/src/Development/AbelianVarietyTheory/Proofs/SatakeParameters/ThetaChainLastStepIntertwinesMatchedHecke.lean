import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralVacuumIntertwinesSphericalHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevelsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Formalism.LocalRingCardinality.PosOfIsomEmb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.Hk3.StepX

variable {D : D7}

theorem gram_posDef_X (τ : D.what₂.Tau) : (gramAt D D.sp.X' τ).PosDef := by
  have := D.sp.X'_sig (tauE D τ)
  rw [D7.X'_posDef D] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem lift_symm_comp {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (x : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) :
    PiTensorProduct.lift.symm (L ∘ₗ x) = postOn M L (PiTensorProduct.lift.symm x) := by
  refine MultilinearMap.ext fun v => ?_
  rw [postOn_apply]
  simp [PiTensorProduct.lift_symm]

theorem integ_X {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D D.sp.X' →* Module.End ℂ (WO S D.sp.X' → ℂ)}
    (hW : IsWeilDatumO ψ S D.sp.X' χS χT om) {f : WO S D.sp.X' → ℂ} (hf : IsThetaFunO ψ S D.sp.X' f)
    (Φ : GA D D.sp.X' → ℂ) (hΦc : Continuous Φ) (hl : ∀ γ ∈ GQ D.sp.X', ∀ h, Φ (γ * h) = Φ h)
    (ν : Measure (GA D D.sp.X')) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D D.sp.X'))
    (h𝓕 : IsFundamentalDomain (GQ D.sp.X') 𝓕 ν) (g : GA D S) (y : GA D D.sp.X') :
    IntegrableOn (fun h => thetaKO om g h f * Φ (h * y)) 𝓕 ν := by
  have : IsTopologicalGroup (GA D D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D D.sp.X') := ⟨rfl⟩
  have : Countable (GQ D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig D.sp.X'.gram
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact D.sp.X' gram_posDef_X
  refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (GQ D.sp.X') C hC (fun h => ?_) ν hν 𝓕 h𝓕 _ ?_ ?_
  · obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  · exact ((hW.om_cont f hf 0).comp (Continuous.prodMk_right g)).mul (hΦc.comp (continuous_mul_right y))
  · intro γ hγ h
    have h1 := (GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S D.sp.X' χS χT om hW f hf).1 1 (one_mem _) γ hγ g h
    rw [one_mul] at h1
    show thetaKO om g (γ * h) f * Φ (γ * h * y) = thetaKO om g h f * Φ (h * y)
    rw [h1, mul_assoc, hl γ hγ]

theorem hyp_inv {V : HSp D} (c : CoefA V) (hc : c.Is) {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {L : LevDat D.host.E ℂ V.rank}
    {P : Pl D.host.E} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {f : Bridge.Gf V → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) :
    ∀ k ∈ hyp V P, ∀ h, c.ext f (h * k) = c.ext f h := by
  obtain ⟨n, hB⟩ := hβ
  have hlev := (GlobalTheory.LevOp.level_operators V β Λ _ (flag1L L) hB P (GlobalTheory.DefLiftHecke.one_pow_notMem P n) hP).1
  exact fun k hk h => GlobalTheory.DefLiftHecke.ext_level c hc hf (hlev k hk).1 (hlev k hk).2 h

theorem mult_stable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hβ : IsSDFrame V β Λ N) {L : LevDat D.host.E ℂ V.rank} {P : Pl D.host.E} (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) (c : List ℤ →₀ ℂ) {U : MMap M}
    (hU : U ∈ Mult θ M (levS V β L) (levChi V β L)) : postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  obtain ⟨n, hB⟩ := hβ
  have hN' : ((N ^ n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h' =>
    hN (P.isPrime.mem_of_pow_mem n (by rwa [Nat.cast_pow] at h'))
  exact (GlobalTheory.LevOp.level_operators V β Λ _ L hB P hN' hP).2.2.2.2 S θ M c hθ U hU

theorem toMap_hkF {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (P : Pl D.host.E) (z : List ℤ →₀ ℂ) (f : Bridge.Gf V → c.W) (w : Dm) :
    c.toMap pr (hkF V P z f) w = hk V P z (c.toMap pr f w) := by
  funext h
  show pr (c.ext (hkF V P z f) h) w = _
  rw [GlobalTheory.DefLiftHecke.ext_hkF c hc, GlobalTheory.ThetaIntHecke.hk_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

set_option maxHeartbeats 2000000 in

theorem liftInt_toMap_hk {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D D.sp.X' →* Module.End ℂ (WO S D.sp.X' → ℂ)} {P : Pl D.host.E}
    (hW : IsWeilDatumO ψ S D.sp.X' χS χT om) {ν : Measure (GA D D.sp.X')} {𝓕 : Set (GA D D.sp.X')}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ D.sp.X') 𝓕 ν) (hfix : VacFix ψ om P)
    (cS cX : List ℤ →₀ ℂ) (hM : Match ψ om P cS (dualC cX)) {f0 : WO S D.sp.X' → ℂ} (hf0 : IsVacAt ψ S D.sp.X' P f0)
    (c : CoefA D.sp.X') (hc : c.Is) {β : GL (Fin D.sp.X'.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (hβ : IsSDFrame D.sp.X' β Λ 1)
    {L : LevDat D.host.E ℂ D.sp.X'.rank} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm] (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) {f : Bridge.Gf D.sp.X' → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') c.coef.ρ (levEnv _ β L).J (levEnv _ β L).χ) (w : Dm) :
    Lift.liftInt ν 𝓕 (thetaKO om) f0 (c.toMap pr (hkF D.sp.X' P cX f) w) =
      hk S P cS (Lift.liftInt ν 𝓕 (thetaKO om) f0 (c.toMap pr f w)) := by
  have he : c.toMap pr f w = (pr.flip w) ∘ c.ext f := rfl
  have hlev := hyp_inv c hc hβ hP hf
  have hcont : Continuous (c.toMap pr f w) := by
    rw [he]
    exact (LinearMap.continuous_of_finiteDimensional (pr.flip w)).comp (GlobalTheory.ThetaIntegrand.ext_continuous c hc β L hf)
  have hl : ∀ γ ∈ GQ D.sp.X', ∀ h, c.toMap pr f w (γ * h) = c.toMap pr f w h := fun γ hγ h => by
    rw [he, Function.comp_apply, Function.comp_apply, GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ h]
  have hr : ∀ k ∈ hyp D.sp.X' P, ∀ h, c.toMap pr f w (h * k) = c.toMap pr f w h := fun k hk h => by
    rw [he, Function.comp_apply, Function.comp_apply, hlev k hk h]
  rw [toMap_hkF c hc pr]
  exact GlobalTheory.ThetaIntHecke.liftInt_hk ψ S D.sp.X' χS χT om P hW ν 𝓕 hν h𝓕 hfix cS cX hM f0 hf0 _ hl hr
    (fun g z _ => integ_X hW hf0.1 _ hcont hl ν hν 𝓕 h𝓕 g z)

theorem sub_comp_apply {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (u u' : M →ₗ[ℂ] N)
    (H : N →ₗ[ℂ] N) (x : M) (h : u' x = H (u x)) : (u' - H ∘ₗ u) x = 0 := by
  rw [LinearMap.sub_apply, LinearMap.comp_apply, h, sub_self]

theorem eq_of_sub_comp {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (u u' : M →ₗ[ℂ] N)
    (H : N →ₗ[ℂ] N) (h : u' - H ∘ₗ u = 0) (x : M) : u' x = H (u x) := by
  have := congrArg (fun L => L x) h
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, sub_eq_zero] at this
  exact this

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 2000000 in

theorem at_It (R : RealDat D A Ks) (F : Face D A) (hC : Core R F) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (hfix : VacFix R.ψ (R.ωX t) P) (cS cX : List ℤ →₀ ℂ) (hM : Match R.ψ (R.ωX t) P cS (dualC cX))
    (y y' : (R.HX t).H) (hy : (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y)) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank)
    (w : SmT R.MX) :
    (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 (R.ItX φ w) =
      hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX φ w)) := by
  have hIo := hC.chain.ioX t
  have hν := hC.models.νX t
  have hmem : (R.HX t).e y ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ :=
    (hC.models.HX t).2.1.le (LinearMap.mem_range_self _ y)
  have k := liftInt_toMap_hk (hC.chain.ωX t) hν.1.1 hν.2 hfix cS cX hM ((GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels R F hC t P hP).2.1 φ)
    R.cX hC.models.cX hC.lev.βX (L := R.datXt t) hP R.prX hmem w
  have e1 : (((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y' : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
      SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w = R.cX.toMap R.prX (hkF D.sp.X' P cX ((R.HX t).e y)) w :=
    congrArg (fun f => R.cX.toMap R.prX f w) hy
  have hyY : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ) (R.cX.toMap R.prX ((R.HX t).e y) w) =
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX φ w) :=
    funext fun g' => hIo.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y) φ w g'
  have hyY' : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ)
      ((((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y' : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
        SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w) =
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 (R.ItX φ w) :=
    funext fun g' => hIo.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y') φ w g'
  exact hyY'.symm.trans ((congrArg (Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ)) e1).trans
    (k.trans (congrArg (hk _ P cS) hyY)))

end GlobalTheory.Hk3.StepX

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.Hk3.StepX.stepX_hk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ t P, Good R t P → VacFix R.ψ (R.ωX t) P → ∀ cS cX, Match R.ψ (R.ωX t) P cS (dualC cX) → ∀ y y' : (R.HX t).H, (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y) → ∀ v, (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 v = hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS t P hP hfix cS cX hM y y' hy
  have hm := D.R.two_le_m
  have hu : (hk (Yc D (D.R.m - 1)) P cS ∘ₗ
      ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1)) ∈ R.CC t (D.R.m - 1) := by
    rw [mem_multT, GlobalTheory.Hk3.StepX.lift_symm_comp]
    exact GlobalTheory.Hk3.StepX.mult_stable R.θ hC.models.inf (R.MY (D.R.m - 1)) (hC.lev.βY (D.R.m - 1) (by omega))
      (L := R.datYt t (D.R.m - 1) R.triv) ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).1 hP cS
      ((mem_multT _ _ _ _ _).1 (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).2)
  have hz := GlobalTheory.multT_eq_zero_of_apply_eq_zero R.θ (R.MY (D.R.m - 1)) _ _ (R.νY t (D.R.m - 1)) (R.fdY t (D.R.m - 1))
    hC.models.inf (hC.models.νY' t).1.1 (hC.models.νY' t).2 (hS.1 t (D.R.m - 1) (by omega))
    (((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1) - hk (Yc D (D.R.m - 1)) P cS ∘ₗ
      ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1))
    (sub_mem (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).2 hu)
  have hex : ∃ φ w, R.ItX φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact (hC.chain.ItX t).ne (LinearMap.ext fun φ => LinearMap.ext fun w => hcon φ w)
  refine hex.elim fun φ0 hw0 => hw0.elim fun w0 hne => ?_
  have h0 := hz _ hne (GlobalTheory.Hk3.StepX.sub_comp_apply _ _ _ _ (GlobalTheory.Hk3.StepX.at_It R F hC t P hP hfix cS cX hM y y' hy φ0 w0))
  exact GlobalTheory.Hk3.StepX.eq_of_sub_comp _ _ _ h0
