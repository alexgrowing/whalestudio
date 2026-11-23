import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDualityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguezStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomDictionaryFramesExponentsKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteChainFrameBottomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralFiniteRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingTripleSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleMatchExistenceStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameSignatureRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomPairsWeightsEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BotMatch

open GlobalTheory.SquareComm in
theorem finRel_le_ker {D : D7} {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {S : Submodule ℂ (WO M X → ℂ)} {Pi : Type} [AddCommGroup Pi]
    [Module ℂ Pi] (p : (WO M X → ℂ) →ₗ[ℂ] Pi) (h : ∀ g ∈ GfC M, ∀ Φ ∈ S, p (ω (g, 1) Φ) = p Φ) : finRel ω S ≤ LinearMap.ker p := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
  simp [map_sub, h u hu Ψ hΨ]

theorem thetaKO_smul {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    (c : ℂ) (f : WO S T → ℂ) : thetaKO om g h (c • f) = c * thetaKO om g h f := by
  simp [thetaKO, map_smul]

theorem thetaKO_sub {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    (f f' : WO S T → ℂ) : thetaKO om g h (f - f') = thetaKO om g h f - thetaKO om g h f' := by
  simp [thetaKO, map_sub]

theorem thetaKO_add {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    (f f' : WO S T → ℂ) : thetaKO om g h (f + f') = thetaKO om g h f + thetaKO om g h f' := by
  simp [thetaKO, map_add]

theorem thetaKO_zero {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T) :
    thetaKO om g h 0 = 0 := by
  simp [thetaKO]

theorem tmul_ne_zero' {Pr Pf : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] {x : Pr} {y : Pf}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

set_option maxHeartbeats 1000000 in
open GlobalTheory.SqTop GlobalTheory.SquareComm in

theorem theta_minor_match : GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (δ t0 : ℂ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ea' : P'.a = A'.rank) (ed : P.d = WW.rank) (ed' : P'.d = WW.rank),
        ∃ (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
          ∀ (g : GA D WW) T, X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
            κ₀ * c0 s * ∑ T', (M T T' : ℂ) * X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea' ed' T') g := by
  intro hMg hP hK hM _ _
  have hH : GlobalTheory.Published.HoweDualityReal := hP.howeDualityReal
  have hLM := GlobalTheory.T.local_matching_of_howe_duality hH hP hK hM
  have hTA := GlobalTheory.T.theta_integrals_of_minguez hMg hP hK hM
  obtain ⟨CF1, H1⟩ := GlobalTheory.T.definiteBottom_dictionary_frames_exponents_kernel
  obtain ⟨CF2, H2⟩ := GlobalTheory.T.finite_chain_frame_bottom hH hP hK hM
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, G1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, G2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W _ i j A A' WW X c0 hX hc => ?_⟩
  obtain ⟨FA, FA', FW, a, b, hdA, hdef, hdW, hD⟩ :=
    G1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  have hF := G2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b

  obtain ⟨ρ, hρ, hrel⟩ := GlobalTheory.T.chain_frame_signature_relation hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b hX.is.rank hdA hdef hdW
    ⟨_, _, (hD μ₀).1, (hD μ₀).2.1⟩ Pr q q' hq hq' hLMt
  choose εf hεf using hrel

  have eI : ∀ t P, thetaInt (X.ω t) X.m X.fd (fockF W.ψ W.θ true FA FW (X.f t) P) = X.I W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I, (hD t).2.2.2.2.1]
  have eI' : ∀ t P, thetaInt (X.ω' t) X.m' X.fd' (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.I' W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I', (hD t).2.2.2.2.2]
  have iI' : ∀ t P h, IntegrableOn (fun g => thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P)) X.fd' X.m' :=
    fun t P h => by simp only [(hD t).2.2.2.2.2]; exact (hX.integrable t).2 P h

  have key : ∀ t, (∀ P', q' P' = 0 → X.I' W.ψ W.θ t P' = 0) ∧
      ((∀ P', X.I' W.ψ W.θ t P' = 0) ∨ ∀ P', X.I' W.ψ W.θ t P' = 0 → q' P' = 0) ∧
      (∃ lam : ℂ, ∀ P P', q P = q' P' → X.I W.ψ W.θ t P = lam • X.I' W.ψ W.θ t P') := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, -⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, p, p', hm⟩ := GlobalTheory.T.triple_match_existence hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex (X.ω t) (X.ω' t)
      (hX.is.weil t) (hX.is.weil' t)
    obtain ⟨Pf, r, r', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    obtain ⟨c, hc0, hc⟩ := hTA D W.ψ W.θ W.θ_is A A' WW FA FA' FW _ _ hTr X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas'
      (X.ω t) (X.ω' t) Pm rf rl p p' hm
    have hrel := GlobalTheory.T.theta_integral_finite_relation hP D W.ψ W.θ W.ψ_std W.θ_is A' WW FA' FW _ _ (X.ω' t) (hX.is.weil' t) hdef X.m' X.fd' hX.is.meas'
    have kerp' := finRel_le_ker p' hm.mapB.invf
    have memF : ∀ P', fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ algF W.ψ W.θ false FA' FW :=
      fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩
    have same : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') →
        ∀ Φ₀, Ψ - Φ₀ ∈ finRel (X.ω' t) (algF W.ψ W.θ false FA' FW) → ModInt W.θ (X.ω' t) X.m' X.fd' Φ₀ →
        thetaInt (X.ω' t) X.m' X.fd' Ψ = thetaInt (X.ω' t) X.m' X.fd' Φ₀ := by
      intro Ψ _ hΨ Φ₀ hd hmod
      obtain ⟨N, K, hmod⟩ := hmod
      funext h
      have h0 := congrFun (hrel _ hd) h
      simp only [thetaInt, thetaKO_sub] at h0 ⊢
      rw [integral_sub (hΨ h) (hmod h).1] at h0
      exact sub_eq_zero.1 h0
    have kill : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') →
        p' Ψ = 0 → thetaInt (X.ω' t) X.m' X.fd' Ψ = 0 := by
      intro Ψ hΨ hi hp
      obtain ⟨Φ₀, hΦ₀, hd, hmod, hI⟩ := hc Ψ hΨ
      have hp0 : p' Φ₀ = 0 := by
        have := kerp' hd
        rw [LinearMap.mem_ker, map_sub, hp, zero_sub, neg_eq_zero] at this
        exact this
      have h1 := hI 0 (zero_mem _) (by rw [map_zero, hp0])
      have h2 : thetaInt (X.ω t) X.m X.fd 0 = 0 := by funext h; simp [thetaInt, thetaKO_zero]
      rw [h2] at h1
      rw [same Ψ hΨ hi Φ₀ hd hmod]
      exact ((smul_eq_zero.1 h1.symm).resolve_left hc0)
    have hp'F : ∀ P', p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') = e (q' P' ⊗ₜ r' (X.f' t)) := hr' _ hf'
    refine ⟨fun P' h0 => ?_, ?_, ?_⟩
    · rw [← eI']
      exact kill _ (memF P') (iI' t P') (by rw [hp'F, h0, TensorProduct.zero_tmul, map_zero])
    · by_cases hall : ∀ P', X.I' W.ψ W.θ t P' = 0
      · exact Or.inl hall
      refine Or.inr fun P' h0 => ?_
      by_contra hq0
      refine hall fun P'' => ?_
      rw [← eI']
      by_cases hy : r' (X.f' t) = 0
      · exact kill _ (memF P'') (iI' t P'') (by rw [hp'F, hy, TensorProduct.tmul_zero, map_zero])
      · have hne : p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
          rw [hp'F]; exact e.map_ne_zero_iff.2 (tmul_ne_zero' hq0 hy)
        exact GlobalTheory.T.matching_triple_signature hH hP hK hM hTA D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdA hdef hdW X.m X.fd X.m' X.fd'
          hX.is.meas hX.is.meas' (X.ω t) (X.ω' t) Pm rf rl p p' hm _ (memF P') hne (by rw [eI']; exact h0) _ (memF P'')
    · obtain ⟨κ, hκ⟩ := hF FA FA' FW t hf hf' Pm rf rl p p' hm Pr Pf q q' r r' e hq hq' hr hr'
      refine ⟨c * κ, fun P P' hPP => ?_⟩
      set Ψ := κ • fockF W.ψ W.θ false FA' FW (X.f' t) P' with hΨdef
      have hΨ : Ψ ∈ algF W.ψ W.θ false FA' FW := Submodule.smul_mem _ _ (memF P')
      have hΨi : ∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m' := fun h => by
        simp only [hΨdef, thetaKO_smul]; exact (iI' t P' h).const_mul κ
      obtain ⟨Φ₀, -, hd, hmod, hI⟩ := hc Ψ hΨ
      have hpp : p (fockF W.ψ W.θ true FA FW (X.f t) P) = p' Φ₀ := by
        have h1 : p' Φ₀ = p' Ψ := by
          have := kerp' hd
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this.symm
        rw [h1, hΨdef, map_smul, hp'F, hr _ hf, hκ, hPP, TensorProduct.tmul_smul, map_smul]
      have h2 := hI _ (Submodule.subset_span ⟨_, P, hf, rfl⟩) hpp
      rw [eI, ← same Ψ hΨ hΨi Φ₀ hd hmod] at h2
      rw [h2, ← eI', mul_smul]
      congr 1
      funext h
      simp [hΨdef, thetaInt, thetaKO_smul, integral_const_mul]
  choose hker hirr hlam using key

  let Il : T → PolF D WW.rank A'.rank →ₗ[ℂ] (GA D WW → ℂ) := fun t =>
    { toFun := fun P' => X.I' W.ψ W.θ t P'
      map_add' := fun P Q => by
        show X.I' W.ψ W.θ t (P + Q) = X.I' W.ψ W.θ t P + X.I' W.ψ W.θ t Q
        rw [← eI', ← eI', ← eI', map_add]; funext h
        simp only [thetaInt, thetaKO_add, Pi.add_apply]
        exact integral_add (iI' t P h) (iI' t Q h)
      map_smul' := fun c P => by
        show X.I' W.ψ W.θ t (c • P) = c • X.I' W.ψ W.θ t P
        rw [← eI', ← eI', map_smul]; funext h
        simp [thetaInt, thetaKO_smul, integral_const_mul] }
  have hK : ∀ t, LinearMap.ker q' ≤ LinearMap.ker (Il t) := fun t P' h0 => hker t P' h0
  let J : T → (Pr →ₗ[ℂ] (GA D WW → ℂ)) := fun t =>
    ((LinearMap.ker q').liftQ (Il t) (hK t)) ∘ₗ (q'.quotKerEquivOfSurjective hq').symm.toLinearMap
  have hJ : ∀ t P', J t (q' P') = X.I' W.ψ W.θ t P' := fun t P' => by
    have : (q'.quotKerEquivOfSurjective hq').symm (q' P') = Submodule.Quotient.mk P' := by
      rw [LinearEquiv.symm_apply_eq]; exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm
    simp only [J, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]; rfl
  have hJI : ∀ t, ∃ lam : ℂ, ∀ P, X.I W.ψ W.θ t P = lam • J t (q P) := fun t => by
    obtain ⟨lam, hl⟩ := hlam t
    refine ⟨lam, fun P => ?_⟩
    obtain ⟨P', hP'⟩ := hq' (q P)
    rw [← hP', hJ]; exact hl P P' hP'.symm
  choose lam hlamJ using hJI

  obtain ⟨⟨t₁, ht₁⟩, P0, P0', hc⟩ := hc
  have hJne : ∀ t, J t (q' P0') ≠ 0 := fun t h0 => by
    obtain ⟨h, hh⟩ := (hc t).2.1
    exact hh (by rw [← hJ, h0]; rfl)
  have hq0 : q' P0' ≠ 0 := fun h0 => hJne t₁ (by rw [h0, map_zero])
  have hinj : ∀ t, Function.Injective (J t) := fun t => by
    rcases hirr t with h | h
    · exact absurd (by rw [hJ]; exact h P0') (hJne t)
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx0
      obtain ⟨P', rfl⟩ := hq' x
      rw [hJ] at hx0
      exact h P' hx0
  have heq : ∀ t, lam t • q P0 = c0 t • q' P0' := fun t => by
    apply hinj t
    rw [map_smul, map_smul, ← hlamJ, hJ]
    funext h
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (hc t).2.2 h
  have hlam1 : lam t₁ ≠ 0 := fun h0 => by
    have := heq t₁
    rw [h0, zero_smul] at this
    exact (smul_eq_zero.1 this.symm).elim ht₁ hq0
  set κ := c0 t₁ / lam t₁ with hκdef
  have hκ0 : κ ≠ 0 := div_ne_zero ht₁ hlam1
  have hqP0 : q P0 = κ • q' P0' := by
    rw [hκdef, div_eq_inv_mul, mul_smul, ← heq t₁, smul_smul, inv_mul_cancel₀ hlam1, one_smul]
  have hlc : ∀ t, lam t = c0 t / κ := fun t => by
    have h1 := heq t
    rw [hqP0, smul_smul, ← sub_eq_zero, ← sub_smul] at h1
    have h2 := (smul_eq_zero.1 h1).resolve_right hq0
    rw [eq_div_iff hκ0]; exact sub_eq_zero.1 h2
  refine ⟨ρ / κ, div_ne_zero hρ hκ0, fun s Q δ t0 P P' hB ea ea' ed ed' => ?_⟩
  have hn : P'.n = P.n := GlobalTheory.T.squareBottomPairs_weights_eq G s i j _ P P' hB
  have core : ∀ (a₁ a₁' d₁ d₁' : ℕ) (n n' : D.what₂.Tau → ℕ) (ea : a₁ = A.rank) (ea' : a₁' = A'.rank) (ed : d₁ = WW.rank)
      (ed' : d₁' = WW.rank) (hn : n' = n), ∃ (M : Tup D a₁ d₁ n → Tup D a₁' d₁' n' → ℤ) (M' : Tup D a₁' d₁' n' → Tup D a₁ d₁ n → ℤ),
        (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
        ∀ (g : GA D WW) T, X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
          ρ / κ * c0 s * ∑ T', (M T T' : ℂ) * X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea' ed' T') g := by
    intro a₁ a₁' d₁ d₁' n n' ea ea' ed ed' hn
    subst ea ea' ed ed' hn
    obtain ⟨M, M', hMM, hMf⟩ := exists_signed_perm (complTup D hX.is.rank) (complTup_bijective D hX.is.rank) (εf _)
    refine ⟨M, M', fun T₁ T₂ => by rw [hMM T₁ T₂]; congr, fun g T => ?_⟩
    rw [hMf T (fun T' => X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF rfl rfl T') g), hlamJ, hεf, map_smul, ← hJ, hlc]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  exact core P.a P'.a P.d P'.d P.n P'.n ea ea' ed ed' hn

end GlobalTheory.BotMatch

end
