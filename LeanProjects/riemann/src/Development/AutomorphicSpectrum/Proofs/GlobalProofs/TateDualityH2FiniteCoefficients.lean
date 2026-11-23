import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.TmulOneMemDcris
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCocycle
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCoboundary
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicCupTwoCochainLocallyConstant
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLattices
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycle
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.BkMain
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTop
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTopEuler
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CupFlip

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.BK

open GlobalTheory.CompanionTheory.LocDual.Q in
theorem actLoc (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l)
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL] (hG : GoodO (Qp := ℚ_[l]) LL O)
    (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (hϖ : Irreducible ϖ) (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (m : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) :
    IsLocallyConstant fun g => actQ LA _ hI g m :=
  act_lc A LA ϖ r hI (latTop l Lp K LL O hG A LA ϖ hϖ).2.1 m

open GlobalTheory.CompanionTheory.LocDual.Q in
set_option maxHeartbeats 1000000 in

theorem dualQ : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l),
    TopInj (Lp.PD K) → DualQ (Lp.PD K) := by
  intro hT l _ Lp K hTop LL _ _ _ O _ _ hG L1 hL1 A A' LA LA' P hdual ϖ hϖ r hI hI'
  have hG0 : ∃ hO : IsDomain O, @IsDiscreteValuationRing O _ hO ∧ IsFractionRing O LL := hG.1
  haveI hDom : IsDomain O := hG0.choose
  haveI hDVR : IsDiscreteValuationRing O := hG0.choose_spec.1
  haveI hFrac : IsFractionRing O LL := hG0.choose_spec.2
  have h50 := GlobalTheory.CompanionTheory.GoodCoeff.goodO_structure l LL O hG ϖ hϖ
  have hFin := h50.2.1
  have hle : (l : O) ∈ Ideal.span {ϖ} := h50.2.2.2.1.choose_spec.1
  have hInt := h50.2.2.2.2.2
  have hdual' := (latTop l Lp K LL O hG A LA ϖ hϖ).2.2.2.2 A' LA' P hdual
  have hF1 := finite_quot O A.V LA.T ϖ r hFin LA.fg
  have hF2 := finite_quot O A'.V LA'.T ϖ r hFin LA'.fg
  have hlp : l.Prime := Fact.out
  have hn : 0 < r + 1 := Nat.succ_pos r
  have hlO : ((l ^ (r + 1) : ℕ) : O) ∈ Ideal.span {ϖ ^ r} := by
    refine (Ideal.mem_span_singleton.1 hle).elim fun b hb => Ideal.mem_span_singleton.2 ?_
    rw [Nat.cast_pow, hb, mul_pow, pow_succ ϖ r]
    exact ⟨ϖ * b ^ (r + 1), by ring⟩
  let w : ↥(GK K) →* ℤ_[l] := GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo.chiInt Lp K
  let χ : ↥(GK K) →* (ZMod (l ^ (r + 1)))ˣ := ((PadicInt.toZModPow (r + 1)).toMonoidHom.comp w).toHomUnits
  have hcomp : ∀ g, ∃ u : ℤ_[l], (u : ℚ_[l]) = (((Lp.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧
      PadicInt.toZModPow (r + 1) u = (χ g : ZMod (l ^ (r + 1))) := fun g => ⟨w g, rfl, rfl⟩
  have hu0 : ∀ g, ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (w g : ℚ_[l]) := fun g => hInt (w g)
  refine (GlobalTheory.CompanionTheory.LocDual.GenChar.exists_generating_character O ϖ hϖ r (l ^ (r + 1)) (pow_pos hlp.pos _) hF1.1 hlO).elim fun ψ₀ hψ => ?_
  exact dual_core (Lp.PD K) hTop hG L1 hL1 A A' LA LA' P hdual (fun x => hdual'.2 x) ϖ hϖ r hI hI'
    hF1.1 hF1.2 hF2.2 (l ^ (r + 1)) hlO χ ψ₀ hψ.1 hψ.2 (fun g => (hu0 g).choose)
    (fun g => (hu0 g).choose_spec)
    (fun g => exists_nat_rep (IsFractionRing.injective O LL) hInt _ (r + 1) hlO (w g) _ (hu0 g).choose_spec)
    (actLoc l Lp K LL O hG A LA ϖ hϖ r hI) (actLoc l Lp K LL O hG A' LA' ϖ hϖ r hI')
    (cobChar hT l Lp K (r + 1) χ hn hcomp) (dblAnn hT l Lp K (r + 1) χ hn hcomp)
    (dblAnnR hT l Lp K (r + 1) χ hn hcomp)

open GlobalTheory.CompanionTheory.TdDualD in
open GlobalTheory.CompanionTheory.LocDual in

theorem dualDL : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), FinZQ (Lp.PD K) →
    DualQ (Lp.PD K) → DualD (Lp.PD K) := by
  intro l _ Lp K hF hQ LL _ _ _ O _ _ hG L1 hL1 A A' LA LA' P hP S hBS hSZ c hc H
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := id hG
  haveI := hdom
  haveI := hdvr
  haveI := hfrac
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : algebraMap O LL ϖ ≠ 0 := fun h =>
    hϖ.ne_zero ((IsFractionRing.injective O LL) (by rw [h, map_zero]))
  obtain ⟨hO, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ
  obtain ⟨-, hb, -, -, -⟩ := latTop l Lp K LL O hG A LA ϖ hϖ
  obtain ⟨-, -, -, hbd', -⟩ := latTop l Lp K LL O hG A' LA' ϖ hϖ
  haveI : CompactSpace ↥(GK K) :=
    haveI := K.2
    isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact
  haveI : Module.Free O ↥LA.T := LA.free
  haveI : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg
  refine core (Cob := CobO (Lp.PD K) L1) ?_ (fun x hx y hy => (hP.2 y).1 hy x hx) hne
    (GlobalTheory.CNorm.isAdicComplete_of_free_finite _ hO) hb ?_
    (fun r => hF LL O hG A LA ϖ hϖ r (Ip_stable LA ϖ r))
    (fun r => (hQ LL O hG L1 hL1 A A' LA LA' P hP ϖ hϖ r (Ip_stable LA ϖ r) (Ip_stable LA' ϖ r)).2)
    hBS hSZ hc H
  · intro z z' h
    have : (fun x => (Submodule.Quotient.mk (z x) : LL ⧸ L1.T)) =
        fun x => (Submodule.Quotient.mk (z' x) : LL ⧸ L1.T) := by
      funext x
      obtain ⟨a, ha⟩ := h x
      refine (Submodule.Quotient.eq _).2 ?_
      rw [ha, hL1]
      exact ⟨a, rfl⟩
    unfold CobO
    rw [this]
  · intro v
    obtain ⟨n, hn⟩ := hbd' (fun _ => v) continuous_const
    exact ⟨n, hn 1⟩

open GlobalTheory.CompanionTheory.LocDual.CobDetect in

theorem cobLO : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), FinZQ (Lp.PD K) → TopInj (Lp.PD K) → CobLO (Lp.PD K) := by
  intro l _ Lp K hfin htop LL _ _ _ O _ _ hO L1 hL1 z hz
  have hO' := hO
  obtain ⟨⟨hdom, hdvr, hfr⟩, hfd, hmt, htr, hop⟩ := hO'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hc, -, -, -, hb, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
  haveI : CompactSpace ↥(GK K) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  have hAlg : Continuous (algebraMap ℚ_[l] LL) := continuous_algebraMap ℚ_[l] LL
  have hχ : Continuous fun g : ↥(GK K) => ((cycLL (Lp.PD K) LL g : LLˣ) : LL) := by
    have h1 : (fun g : ↥(GK K) => ((cycLL (Lp.PD K) LL g : LLˣ) : LL)) =
        fun g : ↥(GK K) => algebraMap ℚ_[l] LL (Lp.χQ (g : GQ l) : ℚ_[l]) := by
      funext g
      rw [← Lp.PD_χ K g]
      rfl
    rw [h1]
    exact hAlg.comp ((GlobalTheory.Cyc.IsCyc.continuous Lp.χQ_cyc).comp continuous_subtype_val)
  let A : GRep ↥(GK K) ℚ_[l] LL O :=
    { V := LL
      ρ := charRep (cycLL (Lp.PD K) LL)
      cont := fun x => by
        simp only [charRep_apply]
        exact hχ.mul continuous_const }
  have hopT : IsOpen (L1.T : Set LL) := by
    have h1 : (L1.T : Set LL) = Set.range (algebraMap O LL) := by
      ext y
      exact mem_T L1 hL1
    rw [h1]
    exact hop
  exact ⟨fun h a => cobO_of_cobL L1 hopT h a, fun h =>
    cobL_of_all L1 hL1 hϖ hop hc hb (fun n => hfin LL O hO A L1 ϖ hϖ n (stable_pw L1 ϖ n))
      (fun r z hr hz' => htop LL O hO L1 hL1 ϖ hϖ r z hr hz') hz h⟩

open GlobalTheory.TateTop Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift Filter Topology in

theorem tate_duality_H2_finite_coefficients (hT : Formalism.GaloisCohomology.LocalTateDualityK) (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l) :
    LocalTateTopDegree (Lp.PD K) := by
  intro LL _ _ _ O _ _ hO L1 hL1
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc Lp.χQ := Lp.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (Lp.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  have hcpt : CompactSpace (GK K) := Φ.symm.surjective.compactSpace hΦ1
  obtain ⟨ι, hι⟩ := exists_ringHom hO
  let : Module ℤ_[l] (LL ⧸ L1.T) := Module.compHom _ ι
  have : SMulCommClass ℤ_[l] O (LL ⧸ L1.T) := ⟨fun a o x => smul_comm (ι a) o x⟩
  have hs : ∀ (a : ℤ_[l]) (x : LL), a • (Submodule.Quotient.mk x : LL ⧸ L1.T) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL a * x) := fun a x => by
    rw [← hι, ← Algebra.smul_def]
    rfl
  refine @h2_equiv_of_torsion_character l _ (GK K) _ _ _ _ _ _ hcpt _ (fun r => (hc r).transport Φ hΦ2 hΦ1)
    (fun x => ?_) O _ _ _ _ fun g x => ?_
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hO x
    refine ⟨n, ?_⟩
    rw [hs, Submodule.Quotient.mk_eq_zero, hL1]
    simpa using hn 1
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hs]
    have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← Lp.PD_χ K g] at h1
    change Submodule.Quotient.mk (algebraMap ℚ_[l] LL ((Lp.PD K).χ g : ℚ_[l]) * x) = _
    rw [← h1]
    rfl

open GlobalTheory.CompanionTheory.LocDual.Top in

theorem topLine : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l),
    LocalTateTopDegree (Lp.PD K) → CobLO (Lp.PD K) → TopLine (Lp.PD K) := by
  intro l _ Lp K hT hC LL _ _ _ O _ _ hO z z' hz hz' hd hd' hn
  obtain ⟨L1, hL1⟩ := (dualLat l Lp K).1 LL O hO
  obtain ⟨⟨hD, hDVR, hFrac⟩, -, -, htr, hopen⟩ := id hO
  haveI := hD
  haveI := hDVR
  haveI := hFrac
  haveI := htr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hc := (GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ).1
  have hop : IsOpen (L1.T : Set LL) := by
    have : (L1.T : Set LL) = Set.range (algebraMap O LL) := by
      rw [hL1]
      ext x
      simp [LinearMap.mem_range]
    rw [this]
    exact hopen
  obtain ⟨φ⟩ := hT LL O hO L1 hL1
  exact topLine_at L1 hL1 hop hϖ hc φ (hC LL O hO L1 hL1) hz hz' hd hd' hn

open GlobalTheory.CompanionTheory.LocDual.Kernels in

theorem rightKernel (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l)
    (hD : DualD (Lp.PD K)) (hC : CobLO (Lp.PD K))
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL] (hO : GoodO (Qp := ℚ_[l]) LL O) (A A' : GRep ↥(GK K) ℚ_[l] LL O)
    (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hP : IsDual1 (Lp.PD K) A.ρ A'.ρ P)
    (b : ↥(GK K) → A'.V) (hb : b ∈ continuousCocycles A'.ρ)
    (hab : ∀ a ∈ continuousCocycles A.ρ, CobL (Lp.PD K) (cupL A'.ρ P a b)) : b ∈ B1 A'.ρ := by
  classical
  obtain ⟨⟨hDom, hDVR, hFrac⟩, -⟩ := id hO
  haveI := hDom
  haveI := hDVR
  haveI := hFrac
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hCyc, hLat⟩ := dualLat l Lp K
  obtain ⟨L1, hL1⟩ := hCyc LL O hO
  obtain ⟨LA, LA', hLA, -⟩ := hLat LL O hO A A' P hP
  have hflip := cupFlip l Lp K LL O hO A A' P hP
  have hopen : IsOpen (LA'.T : Set A'.V) := (latTop l Lp K LL O hO A' LA' ϖ hϖ).1
  have hint : ∀ x ∈ LA.T, ∀ y ∈ LA'.T, P x y ∈ L1.T := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := (hLA.2 y).mp hy x hx
    rw [hL1, ha]
    exact ⟨a, rfl⟩
  have hlc : ∀ f : ↥(GK K) → A'.V, Continuous f →
      IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : A'.V ⧸ LA'.T)) := by
    intro f hf
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    refine ⟨(fun g => f g + -f x) ⁻¹' (LA'.T : Set A'.V),
      hopen.preimage (hf.add continuous_const), ?_, fun g hg => ?_⟩
    · simp
    · refine (Submodule.Quotient.eq _).mpr ?_
      rw [sub_eq_add_neg]
      exact hg
  have hact : ∀ (g : ↥(GK K)) (v : A'.V), actD LA' g (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (A'.ρ g v) := fun _ _ => rfl
  have hBZ : BD LA' ≤ divisibleCocycles LA' := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨?_, fun g h => ?_⟩
    · have hc : Continuous fun g => A'.ρ g v - v := by
        simp only [sub_eq_add_neg]
        exact (A'.cont v).add continuous_const
      have he : (LinearMap.pi fun g => actD LA' g - LinearMap.id)
          (Submodule.Quotient.mk v : A'.V ⧸ LA'.T) =
          fun g => (Submodule.Quotient.mk (A'.ρ g v - v) : A'.V ⧸ LA'.T) := by
        funext g
        rfl
      rw [he]
      exact hlc _ hc
    · simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, hact, map_mul,
        Module.End.mul_apply, map_sub]
      abel
  have key : ∀ n : ℕ, ∃ y : A'.V, ∀ g, ∃ t ∈ LA'.T, b g = cob A'.ρ y g + ϖ ^ n • t := by
    intro n
    have hϖ0 : algebraMap O LL ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr hϖ.ne_zero
    obtain ⟨u, hu⟩ : ∃ u : LL, algebraMap O LL (ϖ ^ n) * u = 1 :=
      ⟨(algebraMap O LL ϖ)⁻¹ ^ n, by rw [map_pow, ← mul_pow, mul_inv_cancel₀ hϖ0, one_pow]⟩
    have huv : ∀ x : A'.V, ϖ ^ n • (u • x) = x := by
      intro x
      rw [← algebraMap_smul LL (ϖ ^ n) (u • x), smul_smul, hu, one_smul]
    let c : ↥(GK K) → A'.V ⧸ LA'.T := fun g => Submodule.Quotient.mk (u • b g)
    have hc : c ∈ divisibleCocycles LA' := by
      refine ⟨hlc _ (hb.1.const_smul u), fun g h => ?_⟩
      show Submodule.Quotient.mk (u • b (g * h)) =
        Submodule.Quotient.mk (u • b g) + actD LA' g (Submodule.Quotient.mk (u • b h))
      rw [hb.2 g h, hact, map_smul, smul_add]
      rfl
    have horth : ∀ d ∈ latticeCocycles LA, CobO (Lp.PD K) L1 (cupLD LA' P d c) := by
      intro d hd
      have hdc : d ∈ continuousCocycles A.ρ := hd.1
      have hdT : ∀ g, d g ∈ LA.T := fun g => hd.2 g (Set.mem_univ g)
      have h1 := (hC LL O hO L1 hL1 _ (hflip.2 d hdc b hb).1).mp (hab d hdc) u
      have he : (fun x => (Submodule.Quotient.mk (cupLD LA' P d c x) : LL ⧸ L1.T)) =
          fun x => Submodule.Quotient.mk ((u • cupL A'.ρ P d b) x) := by
        funext x
        refine (Submodule.Quotient.eq _).mpr ?_
        have hl : liftD LA' (c x.2) - u • b x.2 ∈ LA'.T :=
          (Submodule.Quotient.eq _).mp (Submodule.Quotient.mk_surjective LA'.T (c x.2)).choose_spec
        have h2 := hint _ (hdT x.1) _ (LA'.stable x.1 _ hl)
        simpa [cupLD, cupL, map_sub, map_smul, smul_eq_mul] using h2
      unfold CobO
      rw [he]
      exact h1
    obtain ⟨xb, hxb⟩ := hD LL O hO L1 hL1 A A' LA LA' P hLA (BD LA') le_rfl hBZ c hc
      (fun d hd _ => horth d hd)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xb
    refine ⟨ϖ ^ n • x, fun g => ?_⟩
    have hg : (Submodule.Quotient.mk (u • b g) : A'.V ⧸ LA'.T) =
        Submodule.Quotient.mk (A'.ρ g x - x) := (congrFun hxb g).symm
    refine ⟨_, (Submodule.Quotient.eq _).mp hg, ?_⟩
    rw [smul_sub, huv, smul_sub]
    have hρ : A'.ρ g (ϖ ^ n • x) = ϖ ^ n • A'.ρ g x := LinearMap.map_smul_of_tower _ _ _
    simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, hρ]
    abel
  obtain ⟨F, hF⟩ := exists_finset_sep (k := LL)
    ((cob A'.ρ).coprod (LinearMap.toSpanSingleton LL (↥(GK K) → A'.V) b))
  let res : (↥(GK K) → A'.V) →ₗ[O] (↥F → A'.V) := LinearMap.funLeft O A'.V Subtype.val
  haveI : Module.Finite O ↥LA'.T := Module.Finite.iff_fg.mpr LA'.fg
  have hΛ : (LinearMap.range (LinearMap.compLeft LA'.T.subtype ↥F)).FG :=
    Module.Finite.iff_fg.mp (Module.Finite.range _)
  have hw : res b ∈ ((B1 A'.ρ).restrictScalars O).map res := by
    refine mem_of_forall_pow _ _ hΛ ϖ hϖ.not_isUnit _ fun n => ?_
    obtain ⟨y, hy⟩ := key n
    choose t ht hbt using hy
    refine ⟨res (cob A'.ρ y), Submodule.mem_map_of_mem ⟨y, rfl⟩,
      (LinearMap.compLeft LA'.T.subtype ↥F) (fun i => ⟨t i, ht i⟩), ⟨_, rfl⟩, ?_⟩
    funext i
    exact hbt i
  obtain ⟨_, ⟨y, rfl⟩, hres⟩ := hw
  have hz := hF (y, -1) (fun g hg => by
    have h1 : cob A'.ρ y g = b g := congrFun hres ⟨g, hg⟩
    simp [h1])
  refine ⟨y, ?_⟩
  have hz' : cob A'.ρ y + (-1 : LL) • b = 0 := by simpa using hz
  rw [neg_one_smul, ← sub_eq_add_neg] at hz'
  exact sub_eq_zero.mp hz'

open GlobalTheory.CompanionTheory.LocDual.Kernels in

theorem nondegLL : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), DualD (Lp.PD K) →
    CobLO (Lp.PD K) → NondegL (Lp.PD K) := by
  intro l _ Lp K hD hC LL _ _ _ O _ _ hO A A' P hP
  have hf := cupFlip l Lp K LL O hO A A' P hP
  refine ⟨fun a ha h => ?_, fun b hb h => rightKernel l Lp K hD hC LL O hO A A' P hP b hb h⟩
  exact rightKernel l Lp K hD hC LL O hO A' A P.flip hf.1 a ha
    (fun b hb => ((hf.2 a ha b hb).2.2.1).mp (h b hb))

open GlobalTheory.CompanionTheory.LocDual.FinT in

theorem finrank_H1_rational_eq_lattice : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), FinZQ (Lp.PD K) → TateFiniteness (Lp.PD K) ∧ ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite LL (H1V A.ρ) ∧ finrank LL (H1V A.ρ) = finrank O (LatticeCohomology LA) := by
  intro l _ Lp K hZ
  have key : ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
      [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O)
      (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) := by
    intro LL _ _ _ O _ _ hO A LA
    obtain ⟨⟨hD, hV, hF⟩, -, -, hTR, -⟩ := id hO
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨-, -, hK, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
    obtain ⟨-, hB, -⟩ := latTop l Lp K LL O hO A LA ϖ hϖ
    haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
    haveI : ContinuousSMul LL A.V := IsModuleTopology.toContinuousSMul LL A.V
    haveI : T2Space A.V := t2Space_of_lattice_nhds_basis LA hϖ.not_isUnit hB
    have h0 : algebraMap O LL ϖ ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    have hI : StableSub LA (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥LA.T) := by
      intro g x hx
      obtain ⟨y, rfl⟩ := (mem_smulTop LA ϖ x).1 hx
      exact (mem_smulTop LA ϖ _).2 ⟨actT LA g y, (map_smul _ _ _).symm⟩
    have hfg := fg_Z1T LA h0 hB hK hI (hZ LL O hO A LA ϖ hϖ 1 hI)
    haveI : Module.Finite O ↥(latticeCocycles LA) := Module.Finite.iff_fg.2 hfg
    infer_instance
  refine ⟨key, ?_⟩
  intro LL _ _ _ O _ _ hO A LA
  haveI := key LL O hO A LA
  obtain ⟨⟨hD, hV, hF⟩, -, -, hTR, -⟩ := id hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, -, -, hInt, -⟩ := latTop l Lp K LL O hO A LA ϖ hϖ
  haveI := isLocalized_toV LA hϖ.ne_zero hInt
  refine ⟨Module.Finite.of_isLocalizedModule (nonZeroDivisors O) (Rₚ := LL) (toV LA), ?_⟩
  have h1 : Module.rank LL (H1V A.ρ) = Module.rank O (H1V A.ρ) :=
    IsLocalization.rank_eq LL (nonZeroDivisors O) le_rfl
  have h2 : Module.rank O (H1V A.ρ) = Module.rank O (LatticeCohomology LA) :=
    IsLocalizedModule.rank_eq (nonZeroDivisors O) le_rfl (toV LA)
  rw [finrank, finrank, h1, h2]

open GlobalTheory.CompanionTheory.GrowthOfInvariants in

theorem H0_torsion_growth_bound : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), TateFiniteness (Lp.PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∃ C : ℕ, ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL ↥(H0V A.ρ)) ≤ Nat.card {x : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ∧ Nat.card {x : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ≤ C * Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL ↥(H0V A.ρ)) := by
  intro l _ Lp K hcore LL _ _ _ O _ _ hG A LA ϖ hϖ
  obtain ⟨⟨hO, hD, hF⟩, -⟩ := id hG
  haveI := hO
  haveI := hD
  haveI := hF
  exact growth A LA (hcore LL O hG A LA) hϖ (GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ).2.1

end GlobalTheory.CompanionTheory.Hypotheses₂.BK
