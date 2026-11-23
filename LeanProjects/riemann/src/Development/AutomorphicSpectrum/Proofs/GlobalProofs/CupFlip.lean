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

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.BK

open GlobalTheory.CompanionTheory.LocDual.Lat in

theorem cycMem (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hG : GoodO (Qp := ℚ_[l]) LL O) (g : ↥(GK K)) :
    ((cycLL (Lp.PD K) LL g : LLˣ) : LL) ∈ Set.range (algebraMap O LL) := by
  obtain ⟨χ, hχ, -, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l Lp
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := id hG
  haveI := hdom
  haveI := hdvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h := (GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ).2.2.2.2.2 ((χ (g : GQ l) : ℤ_[l]ˣ) : ℤ_[l])
  rw [hχ, ← Lp.PD_χ K g] at h
  exact h

open GlobalTheory.CompanionTheory.LocDual.Lat in

theorem dualLat : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), cycIntCore (Lp.PD K) ∧ ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (Lp.PD K) A.ρ A'.ρ P → ∃ (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ), IsDualLat1 (Lp.PD K) LA LA' P ∧ IsDualLat1 (Lp.PD K) LA' LA P.flip := by
  intro l _ Lp K
  haveI : CompactSpace ↥(GK K) := by
    haveI := K.2
    exact isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact
  refine ⟨?_, ?_⟩
  · intro LL _ _ _ O _ _ hG
    have hχ := cycMem l Lp K LL O hG
    obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := hG
    haveI := hdom
    haveI := hdvr
    haveI := hfr
    have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
    refine ⟨{ T := LinearMap.range (Algebra.linearMap O LL), stable := ?_, fg := ?_,
              free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj),
              span := ?_ }, rfl⟩
    · rintro g _ ⟨a, rfl⟩
      obtain ⟨c, hc⟩ := hχ g
      refine ⟨c * a, ?_⟩
      change algebraMap O LL (c * a) = ((cycLL (Lp.PD K) LL g : LLˣ) : LL) • algebraMap O LL a
      rw [map_mul, hc, smul_eq_mul]
    · rw [← Submodule.map_top]
      exact Module.Finite.fg_top.map _
    · rw [eq_top_iff]
      intro x _
      have h : (1 : LL) ∈ Submodule.span LL (LinearMap.range (Algebra.linearMap O LL) : Set LL) :=
        Submodule.subset_span ⟨1, by simp⟩
      simpa using Submodule.smul_mem _ x h
  · intro LL _ _ _ O _ _ hG A A' P hP
    have hχ := cycMem l Lp K LL O hG
    obtain ⟨⟨hdom, hdvr, hfr⟩, -, -, htr, hop⟩ := hG
    haveI := hdom
    haveI := hdvr
    haveI := hfr
    haveI := htr
    obtain ⟨LA⟩ := exists_stable (O := O) hop A.ρ A.cont
    obtain ⟨T', hfg, hfree, hspan, h1, h2⟩ :=
      exists_dual LA.T LA.fg LA.free LA.span P hP.2.2.1 hP.2.2.2
    have hst : ∀ g, ∀ y ∈ T', A'.ρ g y ∈ T' := by
      intro g y hy
      refine (h1 _).2 fun x hx => ?_
      obtain ⟨a, ha⟩ := (h1 y).1 hy (A.ρ g⁻¹ x) (LA.stable _ _ hx)
      obtain ⟨c, hc⟩ := hχ g
      refine ⟨c * a, ?_⟩
      have h3 := hP.1 g (A.ρ g⁻¹ x) y
      have h4 : A.ρ g (A.ρ g⁻¹ x) = x := by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      rw [h4, ha, ← hc] at h3
      rw [h3, map_mul]
    refine ⟨LA, { T := T', stable := hst, fg := hfg, free := hfree, span := hspan }, ⟨hP, h1⟩,
      ⟨fun g x y => hP.1 g y x, hP.2.2.1, hP.2.1, hP.2.2.2.symm⟩, ?_⟩
    intro x
    exact h2 x

open GlobalTheory.CompanionTheory.LatTop in

theorem latTop : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → IsOpen (LA.T : Set A.V) ∧ (nhds (0 : A.V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (LA.T : Set A.V)) ∧ IsCompact (LA.T : Set A.V) ∧ (∀ c : ↥(GK K) → A.V, Continuous c → ∃ n : ℕ, ∀ g, ϖ ^ n • c g ∈ LA.T) ∧ ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (Lp.PD K) LA LA' P → IsDualLat1 (Lp.PD K) LA' LA P.flip := by
  intro l _ Lp K LL _ _ _ O _ _ hO A LA ϖ hϖ
  have I := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
  obtain ⟨⟨hd, hdvr, hfr⟩, hfd, hmt, htr, hop⟩ := hO
  obtain ⟨-, -, hC, -, hB, -⟩ := I
  haveI := hd
  haveI := hfr
  haveI := htr
  haveI : CompactSpace ↥(GK K) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K
  have hopen : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hop LA.T LA.fg LA.span
  have hcomp : IsCompact (LA.T : Set A.V) := isCompact_lattice hC LA.T LA.fg LA.free LA.span
  refine ⟨hopen, hasBasis_lattice LA.T hopen hcomp ϖ hϖ.ne_zero hB, hcomp,
    fun c hc => exists_pow_smul_mem LA.T hopen ϖ hB c hc, ?_⟩
  rintro A' LA' P ⟨⟨h1, h2, h3, h4⟩, h5⟩
  refine ⟨⟨fun g y x => h1 g x y, h3, h2, h4.symm⟩, fun x => ⟨fun hx y hy => (h5 y).1 hy x hx, fun hx => ?_⟩⟩
  exact mem_of_dual_dual LA.T LA.fg LA.free LA.span (LA'.T : Set A'.V) P h3 h4 h5 x hx

open GlobalTheory.CompanionTheory.CupFlip in

theorem cupFlip : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (Lp.PD K) A.ρ A'.ρ P → IsDual1 (Lp.PD K) A'.ρ A.ρ P.flip ∧ ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, Continuous (cupL A'.ρ P a b) ∧ ReciprocityTheory.Def.d2 (charRep (cycLL (Lp.PD K) LL)) (cupL A'.ρ P a b) = 0 ∧ (CobL (Lp.PD K) (cupL A'.ρ P a b) ↔ CobL (Lp.PD K) (cupL A.ρ P.flip b a)) ∧ ((a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ) → CobL (Lp.PD K) (cupL A'.ρ P a b)) := by
  intro l _ Lp K LL _ _ _ O _ _ hO A A' P hP
  have : IsTopologicalRing LL := hO.2.2.2.1
  have hd := hP.1
  have hdf : ∀ g y x, P.flip (A'.ρ g y) (A.ρ g x) =
      ((cycLL (Lp.PD K) LL g : LLˣ) : LL) * P.flip y x := fun g y x => hd g x y
  refine ⟨⟨hdf, hP.2.2.1, hP.2.1, hP.2.2.2.symm⟩, fun a ha b hb => ?_⟩
  obtain ⟨hac, hacoc⟩ := ha
  obtain ⟨hbc, hbcoc⟩ := hb
  have hc : Continuous fun g => P (a g) (b g) := (continuous_pair A A' P).comp (hac.prodMk hbc)
  have hflip : CobL (Lp.PD K) (cupL A.ρ P.flip b a) →
      CobL (Lp.PD K) (cupL A'.ρ P a b) := cob_of_flip _ hd hacoc hbcoc hc
  refine ⟨continuous_cup A A' P hac hbc, d2_cup _ hd hacoc hbcoc, ⟨fun h => ?_, hflip⟩, ?_⟩
  · refine cob_of_flip _ (P := P.flip) hdf hbcoc hacoc hc ?_
    rwa [LinearMap.flip_flip]
  · rintro (h | h)
    · obtain ⟨x, hx⟩ := LinearMap.mem_range.1 h
      exact cob_of_left _ hd (x := x) (fun g => by rw [← hx]; rfl) hbcoc
        ((continuous_pair A A' P).comp (continuous_const.prodMk hbc))
    · obtain ⟨y, hy⟩ := LinearMap.mem_range.1 h
      exact hflip (cob_of_left _ (P := P.flip) hdf (x := y) (fun g => by rw [← hy]; rfl) hacoc
        ((continuous_pair A' A P.flip).comp (continuous_const.prodMk hac)))

open GlobalTheory.CompanionTheory.FinCoc in

theorem finZQ : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), FinZQ (Lp.PD K) := by
  intro hT hE l _ Lp K LL _ _ _ O _ _ hg A LA ϖ hϖ r hI
  obtain ⟨-, -, -, ⟨-, hl, -⟩, -, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hg ϖ hϖ
  obtain ⟨-, hB, hC, -, -⟩ := latTop l Lp K LL O hg A LA ϖ hϖ
  have hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V) := hB.mem_of_mem trivial
  have hMfin := finite_quot LA hC hW
  have hfin := GlobalTheory.CocycleCount.cocycles_finite_ncard_le hT hE l K r _
    (fun g => (actQ LA _ hI g).toAddMonoidHom) (actQ_one' LA _ hI)
    (fun g h m => actQ_mul' LA _ hI g h m) (pow_nsmul_quot LA hl r)
    (actQ_isLocallyConstant LA hW A.cont hI)
  exact hfin.1.to_subtype

open GlobalTheory.CompanionTheory.LocDual.TopCoh ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift in

theorem cobChar : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), ∀ (n : ℕ) (χ : ↥(GK K) →* (ZMod (l ^ n))ˣ), 0 < n → (∀ g, ∃ u : ℤ_[l], (u : ℚ_[l]) = (((Lp.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧ PadicInt.toZModPow n u = (χ g : ZMod (l ^ n))) → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] (z : ↥(GK K) × ↥(GK K) → M), IsLocallyConstant z → (∀ g h k, (χ g : ZMod (l ^ n)) • z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → (∀ ψ : M →+ ZMod (l ^ n), ∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = ψ (z (g, h))) → ∃ f : ↥(GK K) → M, IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) • f h - f (g * h) + f g = z (g, h) := by
  intro hT l _ Lp K n χ hn hχ M _ _ _ z hz hcoc hchar
  obtain ⟨hΦ1, hΦ2⟩ := GlobalTheory.Cyc.TwistLift.continuous_fixingSubgroupEquiv K.1
  let Ψ : Formalism.GaloisCohomology.GK l K.1 ≃* ↥(GK K) := K.1.fixingSubgroupEquiv.symm
  have hΨ : Continuous Ψ := hΦ1
  have hΨ' : Continuous Ψ.symm := hΦ2
  have hcyc : IsCyc Lp.χQ := Lp.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (Lp.χQ (Ψ g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΨ)
  have hval : ∀ g : Formalism.GaloisCohomology.GK l K.1,
      (χ (Ψ g) : ZMod (l ^ n)) = (Formalism.GaloisCohomology.cycK l K.1 n g : ZMod (l ^ n)) := fun g => by
    obtain ⟨u, hu, hu'⟩ := hχ (Ψ g)
    rw [Lp.PD_χ K (Ψ g), ← hχZ] at hu
    rw [← hu', show u = (χZ g : ℤ_[l]) from Subtype.ext hu]
    rfl
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  obtain ⟨c, hc, hd⟩ := coboundary_of_characters hT l K.1 K.2 n hn
    ((continuous_toZModPow n).comp hχc) M (fun p => z (Ψ p.1, Ψ p.2))
    (hz.continuous.comp (hΨ.prodMap hΨ))
    (fun g h k => by
      have := hcoc (Ψ g) (Ψ h) (Ψ k)
      rw [hval, ← map_mul Ψ, ← map_mul Ψ] at this
      exact this)
    (fun ψ => by
      obtain ⟨f, hf, hd⟩ := hchar ψ
      refine ⟨fun g => f (Ψ g), hf.continuous.comp hΨ, fun g h => ?_⟩
      have := hd (Ψ g) (Ψ h)
      rw [hval, ← map_mul Ψ] at this
      exact this)
  refine ⟨fun g => c (Ψ.symm g), (IsLocallyConstant.iff_continuous _).2 (hc.comp hΨ'), fun g h => ?_⟩
  have := hd (Ψ.symm g) (Ψ.symm h)
  rw [← map_mul Ψ.symm, ← hval] at this
  simpa using this

open GlobalTheory.CompanionTheory.LocDual.Pair in

theorem dblAnn : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), ∀ (n : ℕ) (χ : ↥(GK K) →* (ZMod (l ^ n))ˣ), 0 < n → (∀ g, ∃ u : ℤ_[l], (u : ℚ_[l]) = (((Lp.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧ PadicInt.toZModPow n u = (χ g : ZMod (l ^ n))) → ∀ (W : Type) [AddCommGroup W] [Finite W] (a : ↥(GK K) → W →+ W), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m, IsLocallyConstant fun g => a g m) → ∀ (W' : Type) [AddCommGroup W'] [Finite W'] (a' : ↥(GK K) → W' →+ W'), (∀ m, a' 1 m = m) → (∀ g h m, a' (g * h) m = a' g (a' h m)) → (∀ m, IsLocallyConstant fun g => a' g m) → ∀ P : W →+ W' →+ ZMod (l ^ n), (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (a g x) (a' g y) = (χ g : ZMod (l ^ n)) * P x y) → ∀ S : AddSubgroup (↥(GK K) → W), (∀ m : W, (fun g => a g m - m) ∈ S) → (∀ s ∈ S, (IsLocallyConstant s ∧ ∀ g h, s (g * h) = s g + a g (s h))) → ∀ c : ↥(GK K) → W, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)) → (∀ c' : ↥(GK K) → W', (IsLocallyConstant c' ∧ ∀ g h, c' (g * h) = c' g + a' g (c' h)) → (∀ s ∈ S, (∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = P (s g) (a' g (c' h)))) → (∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = P (c g) (a' g (c' h)))) → c ∈ S := by
  intro hT l _ Lp K n χ hn hχ W _ _ a h1 hmul hlc W' _ _ a' h1' hmul' hlc' P hP1 hP2 hP S hBS hS c hc H
  have hne : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have mW : Module (ZMod (l ^ n)) W := AddCommGroup.zmodModule fun x => hP1 _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have mW' : Module (ZMod (l ^ n)) W' := AddCommGroup.zmodModule fun y => hP2 _ fun x => by
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  letI tW' : TopologicalSpace W' := ⊥
  haveI dW' : DiscreteTopology W' := ⟨rfl⟩
  haveI hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K.1) W' :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => a' (φ.symm g)) (fun m => by rw [map_one, h1'])
      (fun g h m => by rw [map_mul, hmul'])
  have hrho_apply : ∀ (g : Formalism.GaloisCohomology.GK l K.1) (m : W'), rho g m = a' (φ.symm g) m := fun _ _ => rfl
  have hrho : ReciprocityTheory.Gal.ContAction rho :=
    continuous_prod_of_discrete_right.2 fun m => (hlc' m).continuous.comp hφ.2
  obtain ⟨⟨e⟩, -, -, hb, -⟩ := hT l K.1 K.2 n W' rho hn hrho
  let ψ := Formalism.GaloisCohomology.cycK l K.1 n
  have hψ : ∀ g : ↥(GK K), ((ψ (φ g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) = (χ g : ZMod (l ^ n)) := by
    intro g
    obtain ⟨u, hu1, hu2⟩ := hχ g
    have hcyc : Lp.χQ = GlobalTheory.Cyc.cycChar l :=
      GlobalTheory.Cyc.TwistLift.isCyc_unique Lp.χQ_cyc (GlobalTheory.Cyc.isCyc_cycChar l)
    rw [Lp.PD_χ K g, hcyc] at hu1
    have hu : u = ((cyclotomicCharacter (PadicAlgCl l) l
        (MulSemiringAction.toRingAut (GQ l) (PadicAlgCl l) g.1) : ℤ_[l]ˣ) : ℤ_[l]) := Subtype.ext hu1
    rw [← hu2, hu]
    rfl
  obtain ⟨E, hE⟩ := exists_equiv_dual (n := l ^ n) P.flip hP2 hP1
  have hE' : ∀ x y, E x y = P x y := fun x y => hE x y
  let τ : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K.1) (ReciprocityTheory.Gal.TDual (ZMod (l ^ n)) W') :=
    (ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id _)
  have hEq : ∀ (g : ↥(GK K)) (x : W), E (a g x) = τ (φ g) (E x) := by
    intro g x
    apply ReciprocityTheory.Gal.TDual.ext
    intro y
    change E (a g x) y = ((ψ (φ g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * E x (rho (φ g)⁻¹ y)
    have hy : a' g (a' g⁻¹ y) = y := by rw [← hmul', mul_inv_cancel, h1']
    have hinv : rho (φ g)⁻¹ y = a' g⁻¹ y := by
      rw [hrho_apply, map_inv, MulEquiv.symm_apply_apply]
    rw [hE', hE', hψ, hinv, ← hP, hy]
  have ev : ∀ (g : Formalism.GaloisCohomology.GK l K.1) (t : ReciprocityTheory.Gal.TDual (ZMod (l ^ n)) W') (y : W'),
      t y = P (E.symm t) y := fun g t y => by rw [← hE', E.apply_symm_apply]
  let toS : ReciprocityTheory.Gal.Z1 τ →+ (↥(GK K) → W) :=
    AddMonoidHom.mk' (fun z g => E.symm (z.1 (φ g))) (fun z z' => by funext g; simp)
  have toS_apply : ∀ z g, toS z g = E.symm (z.1 (φ g)) := fun _ _ => rfl
  let A : AddSubgroup (ReciprocityTheory.Gal.Z1 τ) := S.comap toS
  have lift : ∀ s : ↥(GK K) → W, (IsLocallyConstant s ∧ ∀ g h, s (g * h) = s g + a g (s h)) →
      ∃ z : ReciprocityTheory.Gal.Z1 τ, toS z = s := by
    intro s hs
    refine ⟨⟨fun g => E (s (φ.symm g)), ((hs.1.comp E).continuous).comp hφ.2, fun g h => ?_⟩,
      funext fun g => ?_⟩
    · have := hEq (φ.symm g) (s (φ.symm h))
      rw [MulEquiv.apply_symm_apply] at this
      change E (s (φ.symm (g * h))) = E (s (φ.symm g)) + τ g (E (s (φ.symm h)))
      rw [map_mul, hs.2, map_add, this]
    · rw [toS_apply, AddEquiv.symm_apply_eq]
      change E (s (φ.symm (φ g))) = _
      rw [MulEquiv.symm_apply_apply]
  obtain ⟨zc, hcz⟩ := lift c hc
  have hBA : ∀ z : ReciprocityTheory.Gal.Z1 τ, z.1 ∈ ReciprocityTheory.Gal.B1 τ → z ∈ A := by
    intro z hz
    obtain ⟨t, ht⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 hz
    change toS z ∈ S
    have : toS z = fun g => a g (E.symm t) - E.symm t := by
      funext g
      rw [toS_apply, ht, AddEquiv.symm_apply_eq, map_sub, hEq, AddEquiv.apply_symm_apply]
    rw [this]
    exact hBS _
  have key : ∀ (x : ReciprocityTheory.Gal.Z1 τ) (y : ReciprocityTheory.Gal.Z1 (rho.comp (MonoidHom.id _))),
      ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id _) (hrho.comp' continuous_id)
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = 0 ↔
      ∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h,
        (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = P (toS x g) (a' g (y.1 (φ h))) := by
    intro x y
    constructor
    · intro h0
      obtain ⟨f, hf, hd⟩ := (ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
      refine ⟨fun g => f (φ g), (IsLocallyConstant.iff_continuous _).2 (hf.comp hφ.1), fun g h => ?_⟩
      have h2 := congrFun hd (φ g, φ h)
      have h3 : ((ψ (φ g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * f (φ h) - f (φ g * φ h) + f (φ g) =
          (x.1 (φ g)) (rho (φ g) (y.1 (φ h))) := h2
      rw [hψ, ← map_mul, hrho_apply, MulEquiv.symm_apply_apply, ev (φ g)] at h3
      exact h3
    · rintro ⟨f, hf, hd⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ((ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem _ _).2
        ⟨fun g => f (φ.symm g), hf.continuous.comp hφ.2, funext fun p => ?_⟩)
      obtain ⟨g, h⟩ := p
      have h3 := hd (φ.symm g) (φ.symm h)
      rw [← hψ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← map_mul] at h3
      change ((ψ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * f (φ.symm h) - f (φ.symm (g * h)) + f (φ.symm g) =
          (x.1 g) (rho g (y.1 h))
      rw [ev g, hrho_apply]
      have := toS_apply x (φ.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [← this]
      exact h3
  have hmain : zc ∈ A := by
    refine mem_of_cup_flip ψ rho (hrho.comp' continuous_id) e hb.2 A hBA zc fun y hy => ?_
    induction y using Submodule.Quotient.induction_on with | H y =>
    have hc' : IsLocallyConstant (fun g => y.1 (φ g)) ∧
        ∀ g h, y.1 (φ (g * h)) = y.1 (φ g) + a' g (y.1 (φ h)) := by
      refine ⟨(IsLocallyConstant.iff_continuous _).2 (y.2.1.comp hφ.1), fun g h => ?_⟩
      have := y.2.2 (φ g) (φ h)
      rw [map_mul]
      refine this.trans ?_
      change _ + rho (φ g) _ = _
      rw [hrho_apply, MulEquiv.symm_apply_apply]
    have hz := H (fun g => y.1 (φ g)) hc' (fun s hs => ?_)
    · refine (key zc y).2 ?_
      rw [hcz]
      obtain ⟨f, hf, hd⟩ := hz
      exact ⟨f, hf, hd⟩
    · obtain ⟨zs, hzs⟩ := lift s (hS s hs)
      have hA : zs ∈ A := by
        change toS zs ∈ S
        rw [hzs]
        exact hs
      obtain ⟨f, hf, hd⟩ := (key zs y).1 (hy zs hA)
      rw [hzs] at hd
      exact ⟨f, hf, hd⟩
  have hmem : toS zc ∈ S := hmain
  rwa [hcz] at hmem

theorem dblAnnR : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), ∀ (n : ℕ) (χ : ↥(GK K) →* (ZMod (l ^ n))ˣ), 0 < n → (∀ g, ∃ u : ℤ_[l], (u : ℚ_[l]) = (((Lp.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧ PadicInt.toZModPow n u = (χ g : ZMod (l ^ n))) → ∀ (W : Type) [AddCommGroup W] [Finite W] (a : ↥(GK K) → W →+ W), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m, IsLocallyConstant fun g => a g m) → ∀ (W' : Type) [AddCommGroup W'] [Finite W'] (a' : ↥(GK K) → W' →+ W'), (∀ m, a' 1 m = m) → (∀ g h m, a' (g * h) m = a' g (a' h m)) → (∀ m, IsLocallyConstant fun g => a' g m) → ∀ P : W →+ W' →+ ZMod (l ^ n), (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (a g x) (a' g y) = (χ g : ZMod (l ^ n)) * P x y) → ∀ S : AddSubgroup (↥(GK K) → W'), (∀ m : W', (fun g => a' g m - m) ∈ S) → (∀ s ∈ S, (IsLocallyConstant s ∧ ∀ g h, s (g * h) = s g + a' g (s h))) → ∀ c' : ↥(GK K) → W', (IsLocallyConstant c' ∧ ∀ g h, c' (g * h) = c' g + a' g (c' h)) → (∀ c : ↥(GK K) → W, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)) → (∀ s ∈ S, (∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = P (c g) (a' g (s h)))) → (∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = P (c g) (a' g (c' h)))) → c' ∈ S := by
  intro hT l _ Lp K n χ hn hχ W _ _ a a1 amul alc W' _ _ a' a1' amul' alc' P hl hr hP S hcob hS c' hc' H
  have hP' : ∀ g x y, P (a g x) (a' g y) = ((χ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y := hP
  refine dblAnn hT l Lp K n χ hn hχ W' a' a1' amul' alc' W a a1 amul alc P.flip
    (fun y h => hr y fun x => h x) (fun x h => hl x fun y => h y)
    (fun g x y => hP g y x) S hcob hS c' hc' ?_
  intro c hc hs
  have hAll := H c hc fun s hsS =>
    GlobalTheory.CompanionTheory.LocDual.cup_flip_cob (fun g => ((χ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) a a' P hP' c s hc (hS s hsS) _ _
      (Or.inr ⟨rfl, rfl⟩) (hs s hsS)
  exact GlobalTheory.CompanionTheory.LocDual.cup_flip_cob (fun g => ((χ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) a a' P hP' c c' hc hc' _ _
    (Or.inl ⟨rfl, rfl⟩) hAll

open GlobalTheory.CompanionTheory.LocDual.TI in

theorem topInj : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l),
    TopInj (Lp.PD K) := by
  intro hT l _ Lp K LL _ _ _ O _ _ hO L1 hL1 ϖ hϖ r z hz hcob
  obtain ⟨-, hFin, -, ⟨e, hl, -⟩, -, hZ⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
  obtain ⟨⟨hD, hDVR, hFr⟩, -⟩ := hO
  haveI := hD
  haveI := hDVR
  haveI := hFr
  haveI := K.2
  haveI : CompactSpace ↥(GK K) :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  obtain ⟨F, ⟨hF, -⟩, hFz⟩ := hcob
  obtain ⟨s, hrs, hFs⟩ := exists_tor_range L1.T hF.range_finite hϖ hL1 r
  obtain ⟨χZ, hχZ, hχc, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l Lp
  have hlpos : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ hlpos⟩
  let χ : ↥(GK K) →* (ZMod (l ^ (s + 1)))ˣ :=
    (Units.map (PadicInt.toZModPow (s + 1) : ℤ_[l] →+* ZMod (l ^ (s + 1))).toMonoidHom).comp
      (χZ.comp (GK K).subtype)
  have hχv : ∀ g, (χ g : ZMod (l ^ (s + 1))) = PadicInt.toZModPow (s + 1) ((χZ (g : GQ l) : ℤ_[l]ˣ) : ℤ_[l]) :=
    fun _ => rfl
  have hχlc : IsLocallyConstant fun g => (χ g : ZMod (l ^ (s + 1))) :=
    (lc_toZModPow (s + 1)).comp_continuous
      (Units.continuous_val.comp (hχc.comp continuous_subtype_val))
  have hcyc : ∀ g : ↥(GK K), ((cycLL (Lp.PD K) LL g : LLˣ) : LL) =
      algebraMap ℚ_[l] LL (((χZ (g : GQ l) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [hχZ, ← Lp.PD_χ K g]
    rfl
  have hS : ∀ q ∈ tor L1.T ϖ s, (l ^ (s + 1)) • q = 0 := fun q hq => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hl
    rw [mem_tor] at hq
    have h1 : (l : O) ^ (s + 1) = (ϖ * c ^ (s + 1)) * ϖ ^ s := by rw [hc]; ring
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, h1, mul_smul, hq, smul_zero]
  have hact : ∀ g, ∀ q ∈ tor L1.T ϖ s, repD L1 g q = (χ g : ZMod (l ^ (s + 1))).val • q := fun g q hq => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L1.T q
    rw [hχv, ← mk_mul_int L1.T hZ (s + 1) _ x (hS _ hq), ← hcyc]
    rfl
  letI : Module (ZMod (l ^ (s + 1))) ↥(tor L1.T ϖ r) :=
    AddCommGroup.zmodModule fun m => Subtype.ext (hS _ (tor_mono L1.T hrs m.2))
  haveI := finite_tor L1.T hL1 hϖ hFin r
  obtain ⟨f, hf, hfM, hfe⟩ := descent (fun g => (repD L1 g).toAddMonoidHom)
    (fun g h q => by
      change repD L1 (g * h) q = repD L1 g (repD L1 h q)
      rw [map_mul, Module.End.mul_apply])
    χ hχlc (tor L1.T ϖ r) (tor L1.T ϖ s) (tor_mono L1.T hrs) hS hact F hF hFs
    (fun p => Submodule.Quotient.mk (z p)) (fun g h => congrFun hFz (g, h))
    (fun p => (mk_mem_tor L1.T).2 (hz p))
    (fun zz h1 h2 h3 => cobChar hT l Lp K (s + 1) χ (Nat.succ_pos s)
      (fun g => ⟨(χZ (g : GQ l) : ℤ_[l]ˣ), by rw [hχZ, ← Lp.PD_χ K g], rfl⟩) ↥(tor L1.T ϖ r) zz h1 h2 h3)
  choose x hx using fun g => Submodule.Quotient.mk_surjective L1.T (f g)
  refine ⟨x, fun g => (mk_mem_tor L1.T).1 (by rw [hx]; exact hfM g), ?_, fun p => ?_⟩
  · simpa only [hx] using hf
  · have h1 : (Submodule.Quotient.mk (ReciprocityTheory.Def.d1 (charRep (cycLL (Lp.PD K) LL)) x p) : LL ⧸ L1.T) =
        repD L1 p.1 (Submodule.Quotient.mk (x p.2)) - Submodule.Quotient.mk (x (p.1 * p.2)) +
          Submodule.Quotient.mk (x p.1) := rfl
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, h1, hx, hx, hx, sub_eq_zero]
    exact hfe p.1 p.2

end GlobalTheory.CompanionTheory.Hypotheses₂.BK
