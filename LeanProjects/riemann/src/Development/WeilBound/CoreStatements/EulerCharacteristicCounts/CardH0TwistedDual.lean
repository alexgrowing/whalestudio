import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem card_H0_twisted_dual (N : ℕ) [NeZero N] (G G' : Type) [Group G] [TopologicalSpace G] [Group G']
    (φ : G' ≃* G)
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] (χ : G →* (ZMod N)ˣ)
    (rho : Representation (ZMod N) G M) (a : G' → M →+ M) (ha : ∀ g m, rho g m = a (φ.symm g) m)
    (W' : Type) [AddCommGroup W'] [Finite W'] (a' : G' → W' →+ W') (P : M →+ W' →+ ZMod N)
    (hl : ∀ x, (∀ y, P x y = 0) → x = 0) (hr : ∀ y, (∀ x, P x y = 0) → y = 0)
    (he : ∀ g x y, P (a g x) (a' g y) = (χ (φ g) : ZMod N) * P x y) :
    Nat.card (ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))) =
      Nat.card {y : W' // ∀ g, a' g y = y} := by
  let F : W' → ReciprocityTheory.Gal.TDual (ZMod N) M := fun y =>
    ReciprocityTheory.Gal.TDual.mk (AddMonoidHom.toZModLinearMap N (P.flip y))
  have hF : ∀ y x, F y x = P x y := fun _ _ => rfl
  have hinj : Function.Injective F := fun y y' h => by
    refine sub_eq_zero.1 (hr _ fun x => ?_)
    rw [map_sub, ← hF, ← hF, h, sub_self]
  have hT := GlobalTheory.CocycleCount.card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  have hTc : Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) ≤ Nat.card M := hT.2
  have hfin : Finite (W' →+ ZMod N) := DFunLike.finite _
  have hM : Nat.card M ≤ Nat.card (W' →+ ZMod N) :=
    Nat.card_le_card_of_injective P ((injective_iff_map_eq_zero P).2 fun x hx =>
      hl x fun y => by rw [hx, AddMonoidHom.zero_apply])
  have hbij : Function.Bijective F :=
    hinj.bijective_of_nat_card_le (hTc.trans (hM.trans (GlobalTheory.natCard_addMonoidHom_zmod_le N W')))
  have hact : ∀ g y, ReciprocityTheory.Gal.twDual χ rho (φ g) (F y) = F (a' g y) := fun g y => by
    refine DFunLike.ext _ _ fun x => ?_
    have h1 : a g (rho (φ g)⁻¹ x) = x := by
      have := ha (φ g) (rho (φ g)⁻¹ x)
      rw [φ.symm_apply_apply] at this
      rw [← this, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [ReciprocityTheory.Gal.twDual_apply, hF, hF, ← he, h1]
  symm
  refine Nat.card_congr ((Equiv.ofBijective F hbij).subtypeEquiv fun y => ?_)
  rw [ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
  constructor
  · intro h g
    obtain ⟨g, rfl⟩ := φ.surjective g
    exact (hact g y).trans (congrArg F (h g))
  · intro h g
    exact hinj ((hact g y).symm.trans (h (φ g)))

theorem count_eq (N : ℕ) [NeZero N] (G G' : Type) [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (hrho : ReciprocityTheory.Gal.ContAction rho)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (a : G' → M →+ M) (ha : ∀ g m, rho g m = a (φ.symm g) m) :
    Nat.card {c : G' → M // IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} =
      Nat.card (ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))) *
        Nat.card M ^ (d + 1) := by
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := (GlobalTheory.CocycleCount.card_linear_le N M).1
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  let E2 : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have h2 : Nat.card (ReciprocityTheory.Gal.H2 rho) = Nat.card A :=
    (Nat.card_congr E2).trans (GlobalTheory.ZModDual.card_dual_eq N A)
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have h0 : 0 < Nat.card (ReciprocityTheory.Gal.H0 rho) := Nat.card_pos
  have hZ' : Nat.card (ReciprocityTheory.Gal.Z1 rho) =
      Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ (d + 1) := by
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [hZ, hEu]
    ring
  let E : {c : G' → M // IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} ≃
      ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, c.2.2]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        (IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun g h => by
          have := c.2.2 (φ g) (φ h)
          rw [ha, φ.symm_apply_apply, ← map_mul] at this
          exact this⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  rw [Nat.card_congr E, hZ', h2]

section Count

variable {G LL O V : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}

omit [TopologicalSpace G] in
theorem coc_actQ_mul (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g h : G)
    (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) t) = Submodule.Quotient.mk (actT L g (actT L h t))
  congr 1
  refine Subtype.ext ?_
  change ρ (g * h) (t : V) = ρ g (ρ h (t : V))
  simp

theorem card_H1Q_mul (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (hlc : ∀ m, IsLocallyConstant fun g => actQ L I hI g m) :
    Nat.card (QuotientCohomology L I hI) * Nat.card (↥L.T ⧸ I) =
      Nat.card ↥(quotientCocycles L I hI) * Nat.card {x : ↥L.T ⧸ I // ∀ g, actQ L I hI g x = x} := by
  let d0 : (↥L.T ⧸ I) →ₗ[O] (G → ↥L.T ⧸ I) := LinearMap.pi fun g => actQ L I hI g - LinearMap.id
  have hd0 : ∀ m g, d0 m g = actQ L I hI g m - m := fun _ _ => rfl
  have hle : BQ L I hI ≤ quotientCocycles L I hI := by
    rintro _ ⟨m, rfl⟩
    refine ⟨(hlc m).comp (fun x => x - m), fun g h => ?_⟩
    change d0 m (g * h) = d0 m g + actQ L I hI g (d0 m h)
    simp only [hd0, coc_actQ_mul, map_sub]
    abel
  have h1 := Submodule.card_eq_card_quotient_mul_card ((BQ L I hI).comap (quotientCocycles L I hI).subtype)
  have h2 : Nat.card ((BQ L I hI).comap (quotientCocycles L I hI).subtype) = Nat.card (BQ L I hI) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hk : Nat.card (LinearMap.ker d0) = Nat.card {x : ↥L.T ⧸ I // ∀ g, actQ L I hI g x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun m => by
      rw [LinearMap.mem_ker, funext_iff]
      simp only [hd0, Pi.zero_apply, sub_eq_zero])
  have h3 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker d0)
  have h4 : Nat.card ((↥L.T ⧸ I) ⧸ LinearMap.ker d0) = Nat.card (BQ L I hI) :=
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv
  rw [h4, hk] at h3
  rw [h1, h2, h3]
  ring

end Count

theorem cocycles : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (n : ℕ), 0 < n → ∀ (W : Type) [AddCommGroup W] [Finite W] (a : ↥(GK K) → W →+ W), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m, IsLocallyConstant fun g => a g m) → (∀ m : W, l ^ n • m = 0) → ∀ (W' : Type) [AddCommGroup W'] [Finite W'] (a' : ↥(GK K) → W' →+ W'), (∀ m, a' 1 m = m) → (∀ g h m, a' (g * h) m = a' g (a' h m)) → ∀ P : W →+ W' →+ ZMod (l ^ n), (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (a g x) (a' g y) = (Formalism.GaloisCohomology.cycK l K.1 n (K.1.fixingSubgroupEquiv g) : ZMod (l ^ n)) * P x y) → Nat.card {c : ↥(GK K) → W // IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} = Nat.card {y : W' // ∀ g, a' g y = y} * Nat.card W ^ (finrank ℚ_[l] ↥K.1 + 1) := by
  intro hT hE l _ K n hn M _ _ a h1 hmul hlc hr W' _ _ a' _ _ P hl hrt he
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have _ : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ n)) M := AddCommGroup.zmodModule hr
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hT l K.1 hK n M rho hn hrho
  have hEu := hE l K.1 hK n M rho hn hrho
  rw [count_eq _ _ _ φ hφ M _ rho hrho e hb _ hEu a fun _ _ => rfl,
    card_H0_twisted_dual _ _ _ φ M _ rho a (fun _ _ => rfl) W' a' P hl hrt he]

theorem h1count : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I), Finite (↥LA.T ⧸ I) → (∀ m, IsLocallyConstant fun g => actQ LA I hI g m) → Nat.card (QuotientCohomology LA I hI) * Nat.card (↥LA.T ⧸ I) = Nat.card ↥(quotientCocycles LA I hI) * Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} :=
  fun _ _ _ _ _ _ _ _ _ _ _ LA I hI _ hlc => card_H1Q_mul LA I hI hlc

end PositivityTheory.LocalTateOrthogonality.Bk
