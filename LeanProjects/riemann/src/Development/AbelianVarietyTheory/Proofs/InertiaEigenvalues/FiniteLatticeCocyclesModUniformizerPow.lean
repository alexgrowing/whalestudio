import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2LocalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CocycleModPow

theorem cocycles_finite (hT : Formalism.GaloisCohomology.LocalTateDualityK) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : ↥(GK K) → M →+ M) (h1 : ∀ m, a 1 m = m)
    (hmul : ∀ g h m, a (g * h) m = a g (a h m)) (hr : ∀ m : M, l ^ r • m = 0)
    (hlc : ∀ m, IsLocallyConstant fun g => a g m) :
    {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hr, smul_zero]
  have _ : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ (r + 1))) M) := ⟨AddCommGroup.zmodModule hr'⟩
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ (r + 1))) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have ha : ∀ (g : Formalism.GaloisCohomology.GK l K.1) (m : M), (rho g : M →ₗ[ZMod (l ^ (r + 1))] M) m = a (φ.symm g) m := fun _ _ => rfl
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  have hH := (GlobalTheory.T.finite_H1_H2_local hT l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho).1
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have hH1 : 0 < Nat.card (ReciprocityTheory.Gal.H1 rho) := Nat.card_pos
  have hM : 0 < Nat.card M := Nat.card_pos
  have hfin : Finite (ReciprocityTheory.Gal.Z1 rho) := by
    refine Nat.finite_of_card_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at hZ
    exact (Nat.mul_pos hH1 hM).ne hZ
  let E : ↥{c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} →
      ↥(ReciprocityTheory.Gal.Z1 rho) :=
    fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, c.2.2]⟩
  refine Set.finite_coe_iff.1 (Finite.of_injective E fun c c' h => Subtype.ext (funext fun g => ?_))
  have := congrFun (congrArg Subtype.val h) (φ g)
  simpa only [E, φ.symm_apply_apply] using this

theorem dvd_and_finite (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (hO : GoodO (Qp := ℚ_[l]) LL O)
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    ϖ ^ n ∣ ((l : ℕ) : O) ^ n ∧ Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  obtain ⟨-, -, hfin, hcomp⟩ := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := hO
  have hnu : ¬ IsUnit ((l : ℕ) : O) := fun hu => by
    have htop : Ideal.span {((l : ℕ) : O)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
    have hH : IsHausdorff (Ideal.span {((l : ℕ) : O)}) O := hcomp.toIsHausdorff
    have h1 : (1 : O) = 0 := hH.haus 1 fun k => by
      rw [htop, SModEq.zero]
      simp [Ideal.top_pow]
    exact one_ne_zero h1
  have hdvd : ϖ ∣ ((l : ℕ) : O) := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hnu
  have hd : ϖ ^ n ∣ ((l : ℕ) : O) ^ n := pow_dvd_pow_of_dvd hdvd n
  refine ⟨hd, ?_⟩
  have := hfin n
  exact Finite.of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.2 hd))

theorem finite_Z1Q : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)), (quotientCocycles LA _ hI : Set (↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))).Finite := by
  intro hT l _ K LL _ _ _ O _ _ hO A LA ϖ hϖ n hI
  obtain ⟨hd, hfin⟩ := dvd_and_finite l LL O hO ϖ hϖ n
  have hring : IsTopologicalRing LL := hO.2.2.2.1
  have hopen : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hO.2.2.2.2 LA.T LA.fg LA.span
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := hO
  have hTfin : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg
  have hQ : Finite (↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) := by
    have : Module.Finite (O ⧸ Ideal.span {ϖ ^ n})
        (↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) :=
      Module.Finite.of_restrictScalars_finite O _ _
    exact Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})
  have hmem : ∀ t : ↥LA.T, ϖ ^ n • t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) := fun t =>
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hc : algebraMap O LL (ϖ ^ n) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact pow_ne_zero _ hϖ.ne_zero
  haveI := IsModuleTopology.topologicalAddGroup LL A.V
  refine cocycles_finite hT l K n _ (fun g => (actQ LA _ hI g).toAddMonoidHom) ?_ ?_ ?_ ?_
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (actT LA 1 x) = _
      congr 1
      apply Subtype.ext
      change A.ρ 1 x = x
      simp
  · intro g h m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (actT LA (g * h) x) =
        Submodule.Quotient.mk (actT LA g (actT LA h x))
      congr 1
      apply Subtype.ext
      change A.ρ (g * h) x = A.ρ g (A.ρ h x)
      simp
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨b, hb⟩ := hd
      rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Nat.cast_pow, hb, mul_smul]
      exact hmem _
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g₀
      have hcont : Continuous fun g : ↥(GK K) =>
          (algebraMap O LL (ϖ ^ n))⁻¹ • (A.ρ g x - A.ρ g₀ x) :=
        ((A.cont x).sub continuous_const).const_smul _
      have hev := (hopen.preimage hcont).mem_nhds (x := g₀) (by simp)
      filter_upwards [hev] with g hg
      change Submodule.Quotient.mk (actT LA g x) = Submodule.Quotient.mk (actT LA g₀ x)
      rw [Submodule.Quotient.eq]
      convert hmem ⟨_, hg⟩ using 1
      apply Subtype.ext
      change A.ρ g x - A.ρ g₀ x = ϖ ^ n • ((algebraMap O LL (ϖ ^ n))⁻¹ • (A.ρ g x - A.ρ g₀ x))
      rw [← algebraMap_smul LL (ϖ ^ n), smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.CocycleModPow
