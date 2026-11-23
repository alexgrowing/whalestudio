import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeModPowActionIsLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1H0TransportLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticeQuotPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodCyclotomicCharReducesModPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceFormIntegralIffGoodCoeffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePairingInjectiveEquivariantLevelMapStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.EulerLevel

theorem card_H2_eq (N : ℕ) [NeZero N] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) :
    Nat.card (ReciprocityTheory.Gal.H2 rho) = Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.twDual χ rho)) := by
  have hT := GlobalTheory.CocycleCount.card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  let E : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have hA : Finite A := Subtype.finite
  rw [Nat.card_congr E]
  exact GlobalTheory.ZModDual.card_dual_eq N A

set_option maxHeartbeats 1600000 in

theorem core_pos (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (hG : GoodO (Qp := ℚ_[l]) LL O) (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hm : IsDualLat1 (P.PD K) LA LA' m) (r : ℕ) (hr : 0 < r) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T))
    (M : Type) [AddCommGroup M] (tM : TopologicalSpace M) (dM : @DiscreteTopology M tM) (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) :
    Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hp : l.Prime := Fact.out
  obtain ⟨-, -, hfinO, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  have hcO : Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ≠ 0 := by
    have := hfinO 1
    rw [pow_one] at this
    exact Nat.card_pos.ne'
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcM : Nat.card M = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
    rw [← Nat.card_congr e.toEquiv]
    exact GlobalTheory.T.card_lattice_quot_prime_pow l _ LL O hG A LA r
  have hcM' : Nat.card (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) =
      Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
    rw [GlobalTheory.T.card_lattice_quot_prime_pow l _ LL O hG A' LA' r, ← hm.1.2.2.2]
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hcM]; exact pow_ne_zero _ hcO)
  have htor : ∀ x : M, l ^ r • x = 0 := by
    intro x
    rw [← e.apply_symm_apply x, ← map_nsmul]
    generalize e.symm x = y
    induction y using Submodule.Quotient.induction_on with
    | H t =>
      rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2, map_zero]
      rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  haveI instM : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule htor
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  have hφ1 : φ.symm 1 = 1 := map_one _
  have hφm : ∀ g h, φ.symm (g * h) = φ.symm g * φ.symm h := map_mul _
  have hact1 : ∀ x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), actQ LA _ hI 1 x = x := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        show A.ρ 1 (t : A.V) = t
        rw [map_one]
        rfl))
  have hactm : ∀ (g h : ↥(GK K)) (x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))),
      actQ LA _ hI (g * h) x = actQ LA _ hI g (actQ LA _ hI h x) := by
    intro g h x
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        show A.ρ (g * h) (t : A.V) = A.ρ g (A.ρ h t)
        rw [map_mul]
        rfl))
  have hex : ∃ rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M,
      ∀ (g : Formalism.GaloisCohomology.GK l K.1) (x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))), rho g (e x) = e (actQ LA _ hI (φ.symm g) x) :=
    ⟨GlobalTheory.CocycleCount.repOfAction _
      (fun g => e.toAddMonoidHom.comp ((actQ LA _ hI (φ.symm g)).toAddMonoidHom.comp e.symm.toAddMonoidHom))
      (fun x => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddEquiv.coe_toAddMonoidHom, hφ1, hact1, AddEquiv.apply_symm_apply])
      (fun g h x => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddEquiv.coe_toAddMonoidHom, hφm, hactm, AddEquiv.symm_apply_apply]),
      fun g x => congrArg (fun y => e (actQ LA _ hI (φ.symm g) y)) (e.symm_apply_apply x)⟩
  obtain ⟨rho, hcomp⟩ := hex
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun x => ?_
    have hx : (fun g => rho g x) = fun g => e (actQ LA _ hI (φ.symm g) (e.symm x)) := by
      funext g
      rw [← hcomp, e.apply_symm_apply]
    rw [hx]
    exact ((GlobalTheory.T.lattice_modPow_action_isLocallyConstant l ↥(GK K) LL O hG A LA r hI (e.symm x)).comp e).continuous.comp hφ.2
  have hT1 := hT l K.1 hK r M rho hr hrho
  obtain ⟨⟨eH⟩, -, -, -, hb⟩ := hT1
  have hEu := hE l K.1 hK r M rho hr hrho
  have hTr := GlobalTheory.T.card_H1_H0_transport_lattice l K LL O A LA _ hI (l ^ r) M e rho hcomp
  obtain ⟨h1Q, h0Q⟩ := hTr
  have hTDfin : Finite (ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M) :=
    (GlobalTheory.CocycleCount.card_linear_le (l ^ r) M).1
  have hH2 := card_H2_eq (l ^ r) _ M _ rho eH hb
  have hD := GlobalTheory.T.exists_trace_form_integral_iff_goodCoeff l LL O hG
  obtain ⟨lam, hlam⟩ := hD
  have hMp := GlobalTheory.T.tracePairing_injective_equivariant_levelMap l P K LL O A A' LA LA' m hm lam hlam r hI hI' (GlobalTheory.T.periodCyclotomicChar_reduces_mod_prime_pow l P K r) M e rho hcomp
  obtain ⟨Ψ, hΨi, hΨe⟩ := hMp
  have hcD : Nat.card (ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M) = Nat.card M :=
    GlobalTheory.ZModDual.card_dual_eq (l ^ r) M
  have hΨb : Function.Bijective Ψ :=
    hΨi.bijective_of_nat_card_le (by rw [hcD, hcM, hcM'])
  have hfix' : Nat.card {y : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) // ∀ g, actQ LA' _ hI' g y = y} =
      Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho)) := by
    refine Nat.card_congr ((Equiv.ofBijective _ hΨb).subtypeEquiv fun y => ?_)
    rw [Equiv.ofBijective_apply, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro hy g
      exact (hΨe g y).symm.trans (congrArg Ψ (hy _))
    · intro hy g
      have h := hΨe (φ g) y
      have h2 : (IntermediateField.fixingSubgroupEquiv K.1).symm (φ g) = g := φ.symm_apply_apply g
      rw [h2, hy (φ g)] at h
      exact hΨb.1 h
  rw [h1Q, hEu, ← h0Q, hH2, ← hfix', hcM, ← pow_mul]
  rw [show r * finrank LL A.V * finrank ℚ_[l] ↥K.1 = r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V) by ring]

theorem card_H1Q_eq : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  intro hT hE l _ P K LL _ _ _ O _ _ hG A A' LA LA' m hm r hI hI'
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hp : l.Prime := Fact.out
  obtain ⟨-, -, hfinO, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  have hcO : Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ≠ 0 := by
    have := hfinO 1
    rw [pow_one] at this
    exact Nat.card_pos.ne'
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hs : ∀ (X : Type) [AddCommGroup X] [Module O X],
        Subsingleton (X ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O X)) := by
      intro X _ _
      rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one, Submodule.top_smul]
    haveI := hs ↥LA.T
    haveI := hs ↥LA'.T
    have e1 : Nat.card (QuotientCohomology LA _ hI) = 1 := by
      haveI : Subsingleton (QuotientCohomology LA _ hI) := (Submodule.Quotient.mk_surjective _).subsingleton
      exact Nat.card_unique
    have e2 : Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} = 1 := by
      haveI : Unique {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} :=
        { default := ⟨0, fun g => map_zero _⟩, uniq := fun _ => Subsingleton.elim _ _ }
      exact Nat.card_unique
    have e3 : Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} = 1 := by
      haveI : Unique {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} :=
        { default := ⟨0, fun g => map_zero _⟩, uniq := fun _ => Subsingleton.elim _ _ }
      exact Nat.card_unique
    simp only [e1, e2, e3]
    simp
  · exact core_pos hT hE l P K LL O hG A A' LA LA' m hm r hr hI hI' _ ⊥ (@DiscreteTopology.mk _ ⊥ rfl) (AddEquiv.refl _)

end GlobalTheory.EulerLevel
