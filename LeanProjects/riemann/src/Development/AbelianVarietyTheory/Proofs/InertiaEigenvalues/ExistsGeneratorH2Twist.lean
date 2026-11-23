import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCocyclesQuotientPowSmulModuleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteOfPadicCoeffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntRingHomContinuousOfPadicCoeffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycEqImageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoCocycleMemCoboundariesOfModUniformizerPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoCocycleFundamentalMultipleModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalTwoCocycleMultipleNotCoboundaryStatement

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.FreeTwistH2

theorem powSub_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) (n : ℕ) :
    ((powSub (M := O) ϖ n : Submodule O O) : Set O) = ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
  ext x
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, SetLike.mem_coe,
    mem_powSub, Ideal.mem_span_singleton']
  simp only [smul_eq_mul, mul_comm]

theorem powSub_open_basis {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] (hO : PadicCoeff p O) {ϖ : O} (hϖ : Irreducible ϖ) :
    (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) ∧
      ∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U := by
  haveI := hO.ring
  obtain ⟨h1, h2⟩ := (isAdic_iff).1 hO.adic
  refine ⟨fun n => ?_, fun U hU => ?_⟩
  · rw [powSub_eq hϖ]; exact h1 n
  · obtain ⟨n, hn⟩ := h2 U hU
    exact ⟨n, by rw [powSub_eq hϖ]; exact hn⟩

theorem exists_free_H2_twist : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K →
    PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) →
    ∃ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) := by
  intro p _ K O _ _ _ _ _ G _ _ hT hK hO i ε hε
  haveI := hO.compact
  haveI := hO.t2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hopen, hbasis⟩ := powSub_open_basis hO hϖ
  haveI := GlobalTheory.T.isAdicComplete_of_padicCoeff' hO
  have hd : ∀ n : ℕ, ringChar (O ⧸ IsLocalRing.maximalIdeal O ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)),
      Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow hO.p_mem n
  let φ : ℤ_[p] →+* O := IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal O)
    (fun n => (ZMod.castHom (hd n) (O ⧸ IsLocalRing.maximalIdeal O ^ n)).comp (PadicInt.toZModPow n))
    (fun {m n} hle => by
      rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
      congr 1
      exact RingHom.ext_zmod _ _)
  have hφ : Continuous φ := GlobalTheory.T.padicInt_ringHom_continuous_of_padicCoeff' hO φ
  let χZ : Formalism.GaloisCohomology.GK p K →* ℤ_[p]ˣ := (cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p))
  have hχc : Continuous fun g => (χZ g : ℤ_[p]) :=
    Units.continuous_val.comp (cyclotomicCharacter.continuous p K (PadicAlgCl p))
  obtain ⟨c, hc⟩ := GlobalTheory.TateTop.exists_gen_all hχc fun r => by
    have : NeZero (p ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    exact GlobalTheory.TateTop.exists_gen hχc
      (hT p K hK (r + 1) (ZMod (p ^ (r + 1))) (ReciprocityTheory.Gal.charRep (GlobalTheory.Cyc.TwistLift.redChar χZ (r + 1)))
        (Nat.succ_pos _) (GlobalTheory.Cyc.TwistLift.contAction_charRep _
          ((GlobalTheory.PadicH2Separated.continuous_reduction _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT p K hK (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  let e : G ≃* Formalism.GaloisCohomology.GK p K := i.toMulEquiv
  have he : Continuous e := i.continuous
  have he' : Continuous e.symm := i.symm.continuous
  let χ : G →* ℤ_[p]ˣ := χZ.comp e.toMonoidHom
  let cG : G × G → ℤ_[p] := fun q => c (e q.1, e q.2)
  have hcG : ∀ r, GlobalTheory.TateTop.Gen χ r cG := fun r => (hc r).transport e he he'
  have hεφ : ∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p]) := fun g => GlobalTheory.T.eq_cyclotomicCharacter_of_isCyc hO φ i hε g
  have hχGc : Continuous fun g => (χ g : ℤ_[p]) := hχc.comp he
  have hεc : Continuous fun g => ((ε g : Oˣ) : O) := by
    simp_rw [hεφ]
    exact hφ.comp hχGc
  have hcont : ContAction (twist ε O) := by
    show Continuous fun q : G × O => twist ε O q.1 q.2
    simp only [twist_apply, smul_eq_mul]
    exact (hεc.comp continuous_fst).mul continuous_snd
  have hfin := fun n => GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen hT hK hO.p_mem i (twist ε O) hcont ϖ hϖ hopen n
  have hG := fun r => GlobalTheory.GenSpan.gen_zmod (hcG r)
  have hcc : Continuous cG :=
    GlobalTheory.PadicH2Separated.continuous_of_reductions cG fun s => (hG (s + 1)).1.1.continuous
  have hcoc : ∀ g h k, (χ g : ℤ_[p]) * cG (h, k) - cG (g * h, k) + cG (g, h * k) - cG (g, h) = 0 := by
    intro g h k
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    simpa only [map_sub, map_add, map_mul, map_zero] using (hG n).1.2 g h k
  let z0 : G × G → O := fun q => φ (cG q)
  have hz0 : z0 ∈ Z2 (twist ε O) := by
    refine (mem_cocycles2 _ _).2 ⟨hφ.comp hcc, fun g h k => ?_⟩
    simp only [twist_apply, smul_eq_mul, z0, hεφ]
    rw [← map_mul, ← map_sub, ← map_add, ← map_sub, hcoc, map_zero]
  let Z : H2 (twist ε O) := Submodule.Quotient.mk ⟨z0, hz0⟩
  refine ⟨Z, fun a b hab => ?_, fun y => ?_⟩
  · have h0 : (a - b) • Z = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 hab
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨f, hf, hfd⟩ := (separated_dvr_second_cohomology_mem _ _).1 h0
    refine sub_eq_zero.1 (GlobalTheory.T.fundamentalTwoCocycle_multiple_not_coboundary χ cG hcG φ ε hεφ ϖ hϖ hO.p_mem hopen (a - b) f hf
      fun g h => ?_)
    have e1 := congrFun hfd (g, h)
    rw [e1]
    rfl
  · induction y using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨a, ha⟩ := GlobalTheory.T.twoCocycle_fundamental_multiple_mod_pow χ cG hcG φ ε hεφ ϖ hϖ hO.p_mem hopen w.1 w.2
      refine ⟨a, ?_⟩
      show a • Z = Submodule.Quotient.mk w
      rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
      show (w.1 - a • z0) ∈ B2 (twist ε O)
      refine GlobalTheory.T.twoCocycle_mem_coboundaries_of_mod_uniformizer_pow ε ϖ hopen hbasis hfin _
        (sub_mem w.2 (Submodule.smul_mem _ a hz0)) fun n => ?_
      obtain ⟨b, hb, hbd⟩ := ha n
      exact ⟨b, hb, fun g h => by rw [hbd]; rfl⟩

end GlobalTheory.FreeTwistH2
