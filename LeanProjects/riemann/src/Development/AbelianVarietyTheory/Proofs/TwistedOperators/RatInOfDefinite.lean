import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharactersStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridNodeSignatureSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeHasRigidificationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSumSelfDualExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeIndexAdditive
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemOrth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecondStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralDefiniteSourceConvergesContinuousInStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousAutomorphicEqZeroOfVanishOnFiniteAdeliStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterFiniteOrderValuesInField

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConstRatio

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

section RatPart

variable {L ι : Type} [Field L] (σ : L →+* ℂ)

def ratPart (φ : ℂ → L) (w : ℂ) (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  ∑ k ∈ P.support, σ (φ (w * P.coeff k)) • MvPolynomial.monomial k 1

variable {σ}

theorem ratPart_rat {ℓ : MvPolynomial ι ℂ →ₗ[ℂ] ℂ} {Ω : ℂ} (h : ∀ k, ∃ z : L, ℓ (MvPolynomial.monomial k 1) = Ω * σ z)
    (φ : ℂ → L) (w : ℂ) (P : MvPolynomial ι ℂ) : ∃ z : L, ℓ (ratPart σ φ w P) = Ω * σ z := by
  choose z hz using h
  refine ⟨∑ k ∈ P.support, φ (w * P.coeff k) * z k, ?_⟩
  simp only [ratPart, map_sum, map_smul, hz, map_mul, Finset.mul_sum, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ratPart_eq {ℓ : MvPolynomial ι ℂ →ₗ[ℂ] ℂ} {Ω : ℂ} (h : ∀ k, ∃ z : L, ℓ (MvPolynomial.monomial k 1) = Ω * σ z)
    (φ : ℂ →+ L) (hφ : ∀ x y, φ (x * σ y) = φ x * y) (w : ℂ) (P : MvPolynomial ι ℂ) :
    ℓ (ratPart σ φ (w * Ω) P) = Ω * σ (φ (w * ℓ P)) := by
  choose z hz using h
  have e : ℓ P = ∑ k ∈ P.support, P.coeff k * (Ω * σ (z k)) := by
    conv_lhs => rw [P.as_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hz, ← smul_eq_mul, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  simp only [ratPart, map_sum, map_smul, hz, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show w * (P.coeff k * (Ω * σ (z k))) = (w * Ω * P.coeff k) * σ (z k) by ring, hφ, σ.map_mul]
  ring

theorem exists_dual {x : ℂ} (hx : x ≠ 0) : ∃ φ : ℂ →+ L, (∀ a y, φ (a * σ y) = φ a * y) ∧ φ x ≠ 0 := by
  letI : Algebra L ℂ := σ.toAlgebra
  obtain ⟨φ, hφ⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff L x).1 hx)
  refine ⟨φ.toAddMonoidHom, fun a y => ?_, hφ⟩
  have : a * σ y = y • a := by rw [Algebra.smul_def, mul_comm]; rfl
  show φ (a * σ y) = φ a * y
  rw [this, map_smul, smul_eq_mul, mul_comm]

end RatPart

variable {D : D7}

section Bottom

variable {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem Factor.ratIn {L : Type} [Field L] {σ : L →+* ℂ} {lam : T → ℂ} (h : Factor X ψ θ lam) (hr : X.RationalSums ψ θ σ)
    (hi' : ∀ t P g, IntegrableOn (X.ker' ψ θ t P g) X.fd' X.m')
    (hz : ∀ t P P' (a b : ℂ), (∀ g ∈ GfC WW, a * X.I ψ θ t P g - b * X.I' ψ θ t P' g = 0) →
      ∀ g, a * X.I ψ θ t P g - b * X.I' ψ θ t P' g = 0) (t₀ : T) : RatIn σ t₀ lam := by
  obtain ⟨h0, Pi, p, p', J, hs, hJ, -, hI, hI', P', hP', -⟩ := h
  obtain ⟨Ω, Ω', hΩ, hΩ', H⟩ := hr
  obtain ⟨P, hP⟩ := hs (p' P')
  have hI'' : ∀ t Q, X.I' ψ θ t Q = J t (p' Q) := fun t Q => hI' t Q (hi' t Q)
  let ℓ : T → GA D WW → (PolF D WW.rank A.rank →ₗ[ℂ] ℂ) := fun t g => lam t • (LinearMap.proj g ∘ₗ J t ∘ₗ p)
  let ℓ' : T → GA D WW → (PolF D WW.rank A'.rank →ₗ[ℂ] ℂ) := fun t g => LinearMap.proj g ∘ₗ J t ∘ₗ p'
  have hℓ : ∀ t g Q, ℓ t g Q = X.I ψ θ t Q g := fun t g Q => by rw [hI]; rfl
  have hℓ' : ∀ t g Q, ℓ' t g Q = X.I' ψ θ t Q g := fun t g Q => by rw [hI'']; rfl
  have r : ∀ t, ∀ g ∈ GfC WW, ∀ k, ∃ z : L, ℓ t g (MvPolynomial.monomial k 1) = Ω * σ z := fun t g hg k => by
    rw [hℓ]; exact ((H t g hg).1 k).2
  have r' : ∀ t, ∀ g ∈ GfC WW, ∀ k, ∃ z : L, ℓ' t g (MvPolynomial.monomial k 1) = Ω' * σ z := fun t g hg k => by
    rw [hℓ']; exact ((H t g hg).2 k).2
  have sep : ∀ t Q Q' (a b : ℂ), (∀ g ∈ GfC WW, a * ℓ t g Q - b * ℓ' t g Q' = 0) → (a * lam t) • p Q = b • p' Q' :=
    fun t Q Q' a b hh => hJ t (funext fun g => by
      have := hz t Q Q' a b (fun g hg => by rw [← hℓ, ← hℓ']; exact hh g hg) g
      rw [hI, hI''] at this
      simp only [map_smul, _root_.Pi.smul_apply, smul_eq_mul] at this ⊢
      linear_combination this)
  have nz : ∀ t Q', p' Q' ≠ 0 → ∃ g ∈ GfC WW, ℓ' t g Q' ≠ 0 := fun t Q' hQ => by
    by_contra hc
    push Not at hc
    have := sep t P Q' 0 1 fun g hg => by rw [hc g hg]; simp
    exact hQ (by simpa using this.symm)
  obtain ⟨g₀, hg₀, hn₀⟩ := nz t₀ P' hP'
  obtain ⟨φ, hφ, hφ0⟩ := exists_dual (σ := σ) hn₀
  have e0 : ∀ g, (lam t₀)⁻¹ * ℓ t₀ g P = 1 * ℓ' t₀ g P' := fun g => by
    show (lam t₀)⁻¹ * (lam t₀ * J t₀ (p P) g) = 1 * J t₀ (p' P') g
    rw [hP, inv_mul_cancel_left₀ (h0 _), one_mul]
  set Q := ratPart σ φ ((lam t₀)⁻¹ * Ω) P
  set Q' := ratPart σ φ (1 * Ω') P'
  have e1 : (Ω' * lam t₀) • p Q = Ω • p' Q' := sep t₀ Q Q' Ω' Ω fun g hg => by
    rw [ratPart_eq (r t₀ g hg) φ hφ, ratPart_eq (r' t₀ g hg) φ hφ, e0]; ring
  have hQ' : p' Q' ≠ 0 := fun hh => by
    have h1 : ℓ' t₀ g₀ Q' = 0 := by
      show J t₀ (p' Q') g₀ = 0
      rw [hh, map_zero]; rfl
    rw [ratPart_eq (r' t₀ g₀ hg₀) φ hφ, one_mul] at h1
    exact mul_ne_zero hΩ' ((map_ne_zero σ).2 hφ0) h1
  intro t
  refine ⟨h0 t, ?_⟩
  obtain ⟨g, hg, hn⟩ := nz t Q' hQ'
  obtain ⟨z, hz1⟩ := ratPart_rat (r t g hg) φ ((lam t₀)⁻¹ * Ω) P
  obtain ⟨z', hz2⟩ := ratPart_rat (r' t g hg) φ (1 * Ω') P'
  have e2 : Ω' * lam t₀ * ℓ t g Q = lam t * Ω * ℓ' t g Q' := by
    have := congrArg (fun x => J t x g) e1
    simp only [map_smul, _root_.Pi.smul_apply, smul_eq_mul] at this
    show Ω' * lam t₀ * (lam t * J t (p Q) g) = lam t * Ω * J t (p' Q') g
    linear_combination lam t * this
  have hz' : σ z' ≠ 0 := fun hh => hn (hz2.trans (by rw [hh, mul_zero]))
  have e3 : σ (z / z') = lam t / lam t₀ := by
    rw [show ℓ t g Q = _ from hz1, show ℓ' t g Q' = _ from hz2] at e2
    have := h0 t₀
    rw [map_div₀]
    field_simp
    have e4 : Ω * Ω' * (σ z * lam t₀ - lam t * σ z') = 0 := by linear_combination e2
    have := (mul_eq_zero.1 e4).resolve_left (mul_ne_zero hΩ hΩ')
    linear_combination this
  have hne : z / z' ≠ 0 := fun hh => div_ne_zero (h0 t) (h0 t₀) (by rw [← e3, hh, map_zero])
  exact ⟨Units.mk0 _ hne, e3⟩

theorem ideal_ne_bot (X : Tri T A A' WW) (S : T → Finset (Pl D.host.E)) (t : T) : X.ideal S t ≠ ⊥ :=
  Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

variable {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (Pl D.host.E)}

theorem theta_f (h : X.Is ψ θ α β νH S) (t : T) : IsThetaFunO ψ (neg A) WW (X.f t) ∧ IsThetaFunO ψ A' WW (X.f' t) := by
  have hν : IsHeckeChar D (α t / β t) := (h.weil' t).hecT
  obtain ⟨f, h1, h2⟩ := GlobalTheory.T.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW _ _ _ _ _ h.rigA h.rigW hν (h.idem t) (ideal_ne_bot X S t) h.isVac
  obtain ⟨f', h1', h2'⟩ := GlobalTheory.T.exists_thetaFunction_standardPairSecond D ψ θ A' WW X.rA' X.rW _ _ _ _ A.rank _ h.rigA' h.rigW hν (h.idem t) (ideal_ne_bot X S t) h.isVac'
  obtain ⟨Tm, hT⟩ := h1.1
  obtain ⟨Tm', hT'⟩ := h1'.1
  exact ⟨((h.fst t).2 Tm hT).trans (h1.2 Tm hT).symm ▸ h2, ((h.snd t).2 Tm' hT').trans (h1'.2 Tm' hT').symm ▸ h2'⟩

theorem ratIn_of_definite {L : Type} [Field L] {σ : L →+* ℂ} {lam : T → ℂ} (h : X.Is ψ θ α β νH S)
    (hA : ∀ τ, (gramAt D A τ).PosDef) (hA' : ∀ τ, (gramAt D A' τ).PosDef) (hW : ∀ τ, (gramAt D WW τ).PosDef)
    (hF : Factor X ψ θ lam) (hr : X.RationalSums ψ θ σ) (t₀ : T) : RatIn σ t₀ lam := by
  have c := fun t P => GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D ψ true A WW _ _ (X.ω t) X.m X.fd _ (h.weil t) hA h.meas.1 h.meas.2
    (GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B (theta_f h t).1 P)
  have c' := fun t P => GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (h.weil' t) hA' h.meas'.1 h.meas'.2
    (GlobalTheory.Chain.InnerSteps.theta_pureTensorO h.isVac.1 h.isVac.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B (theta_f h t).2 P)
  refine hF.ratIn hr (fun t P g => (c' t P).1 g) (fun t P P' a b => ?_) t₀
  refine GlobalTheory.T.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic D WW (fun g => a * X.I ψ θ t P g - b * X.I' ψ θ t P' g) hW
    ((continuous_const.mul (c t P).2.1).sub (continuous_const.mul (c' t P').2.1)) fun γ hγ g => ?_
  exact congrArg₂ (fun u v => a * u - b * v) ((c t P).2.2 γ hγ g) ((c' t P').2.2 γ hγ g)

theorem posDef_of_std {V : HSp D} {r : Rig V} (h : r.IsStd) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  have : gramAt D V τ = 1 := by rw [gramAt, h.1]; simp
  rw [this]; exact Matrix.PosDef.one

end Bottom

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {Fam : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D Fam Ks} {F : Face D Fam} {G : GridPre R}

theorem exists_expAt (χ : Formalism.L2.Host.HChar D.host.E) (w : Pl D.host.E) : ∃ n, GlobalTheory.CMVal.ExpAt χ w n := by
  classical
  have h := GlobalTheory.Mem.UnrAe.exists_levelLe χ w
  refine ⟨Nat.find h, fun m => ⟨fun hm => Nat.find_min' h hm, fun hm x hx hx' => Nat.find_spec h x hx (hx'.trans ?_)⟩⟩
  rw [WithZero.exp_le_exp]
  omega

theorem exists_meas (V : HSp D) : ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 μ := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨𝓕, h⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V Measure.haar inferInstance
  exact ⟨Measure.haar, 𝓕, inferInstance, h⟩

theorem exists_isWeil {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) (ε : Bool)
    (S W : HSp D) {χS χW : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χW) (h3 : ResEta D χS S.rank)
    (h4 : ResEta D χW W.rank) : ∃ ω : WRep S W, IsWeil ψ ε S W χS χW ω := by
  obtain ⟨om, h⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hψ (sgn ε S) W χS χW hη h1 h2 h3 h4
  exact ⟨om.comp ((ofSgn ε S).symm.toMonoidHom.prodMap (MonoidHom.id _)), h⟩

end GlobalTheory.ConstRatio

end
