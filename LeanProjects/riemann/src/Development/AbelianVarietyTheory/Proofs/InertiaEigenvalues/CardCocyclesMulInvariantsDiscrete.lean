import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardAddMonoidHomZmodLe
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.CocycleCount

theorem card_linear_le (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] [Module (ZMod N) A]
    [Finite A] : Finite (A →ₗ[ZMod N] ZMod N) ∧ Nat.card (A →ₗ[ZMod N] ZMod N) ≤ Nat.card A := by
  have h1 : Finite (A →ₗ[ZMod N] ZMod N) := DFunLike.finite _
  have h2 : Finite (A →+ ZMod N) := DFunLike.finite _
  refine ⟨h1, le_trans ?_ (GlobalTheory.natCard_addMonoidHom_zmod_le N A)⟩
  exact Nat.card_le_card_of_injective (fun f => f.toAddMonoidHom) LinearMap.toAddMonoidHom_injective

theorem card_H2_le (N : ℕ) [NeZero N] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) :
    Finite (ReciprocityTheory.Gal.H2 rho) ∧ Nat.card (ReciprocityTheory.Gal.H2 rho) ≤ Nat.card M := by
  have hT := card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  have hTc : Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) ≤ Nat.card M := hT.2
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  have hA := card_linear_le N A
  have hAc : Nat.card A ≤ Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  let E : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have := hA.1
  refine ⟨Finite.of_equiv _ E.symm, ?_⟩
  rw [Nat.card_congr E]
  exact hA.2.trans (hAc.trans hTc)

theorem card_cocycles_mul_invariants_discrete (R : Type) [CommRing R] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R G M) (hrho : ReciprocityTheory.Gal.ContAction rho) :
    Nat.card (ReciprocityTheory.Gal.Z1 rho) * Nat.card (ReciprocityTheory.Gal.H0 rho) =
      Nat.card (ReciprocityTheory.Gal.H1 rho) * Nat.card M := by
  have hle : ReciprocityTheory.Gal.B1 rho ≤ ReciprocityTheory.Gal.Z1 rho := by
    rintro _ ⟨m, rfl⟩
    refine ⟨?_, fun g h => ?_⟩
    · exact (hrho.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · simp only [ReciprocityTheory.Gal.amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype)
  have h2 : Nat.card ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype) =
      Nat.card (ReciprocityTheory.Gal.B1 rho) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hk : LinearMap.ker (ReciprocityTheory.Gal.d0 rho) = ReciprocityTheory.Gal.H0 rho := by
    ext m
    rw [LinearMap.mem_ker, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp only [ReciprocityTheory.Gal.amitsur_d0_apply, Pi.zero_apply, sub_eq_zero]
  have h3 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (ReciprocityTheory.Gal.d0 rho))
  have h4 : Nat.card (M ⧸ LinearMap.ker (ReciprocityTheory.Gal.d0 rho)) = Nat.card (ReciprocityTheory.Gal.B1 rho) :=
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv
  rw [h4, hk] at h3
  rw [h1, h2, h3]
  ring

def repOfAction (N : ℕ) {G M : Type} [Monoid G] [AddCommGroup M] [Module (ZMod N) M]
    (a : G → M →+ M) (h1 : ∀ m, a 1 m = m) (hmul : ∀ g h m, a (g * h) m = a g (a h m)) :
    Representation (ZMod N) G M where
  toFun g := AddMonoidHom.toZModLinearMap N (a g)
  map_one' := LinearMap.ext h1
  map_mul' g h := LinearMap.ext (hmul g h)

theorem count_of_euler (N : ℕ) [NeZero N] (G G' : Type) [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (hrho : ReciprocityTheory.Gal.ContAction rho)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (a : G' → M →+ M) (ha : ∀ g m, rho g m = a (φ.symm g) m) :
    {c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (d + 2) := by
  obtain ⟨hf2, hc2⟩ := card_H2_le _ _ M _ rho e hb
  have hZ := card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have h0 : 0 < Nat.card (ReciprocityTheory.Gal.H0 rho) := Nat.card_pos
  have h2 : 0 < Nat.card (ReciprocityTheory.Gal.H2 rho) := Nat.card_pos
  have hM : 0 < Nat.card M := Nat.card_pos
  have hZ' : Nat.card (ReciprocityTheory.Gal.Z1 rho) =
      Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ (d + 1) := by
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [hZ, hEu]
    ring
  let E : ↥{c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} ≃
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
  have hfin : Finite (ReciprocityTheory.Gal.Z1 rho) :=
    Nat.finite_of_card_ne_zero (by rw [hZ']; positivity)
  refine ⟨Set.finite_coe_iff.1 (Finite.of_equiv _ E.symm), ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr E, hZ', pow_succ' _ (_ + 1)]
  exact Nat.mul_le_mul_right _ hc2

theorem cocycles_finite_ncard_le :
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : ↥(GK K) → M →+ M), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, l ^ r • m = 0) → (∀ m, IsLocallyConstant fun g => a g m) → {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧ {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤ Nat.card M ^ (Module.finrank ℚ_[l] ↥K.1 + 2) := by
  intro hT hE l _ K r M _ _ a h1 hmul hr hlc
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hr, smul_zero]
  have _ : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr'
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ (r + 1))) (Formalism.GaloisCohomology.GK l K.1) M :=
    repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hT l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho
  have hEu := hE l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho
  exact count_of_euler _ _ _ φ hφ M _ rho hrho e hb _ hEu a fun _ _ => rfl

end GlobalTheory.CocycleCount
