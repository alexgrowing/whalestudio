import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GaloisTransport

section Generic

variable {R G' G Q M : Type} [CommRing R] [Group G'] [TopologicalSpace G'] [Group G]
  [TopologicalSpace G] [AddCommGroup Q] [Module R Q] {N : ℕ} [AddCommGroup M] [Module (ZMod N) M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem card_H1_transport (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (act : G' → Q → Q) (Z B : Submodule R (G' → Q))
    (hZ : ∀ c, c ∈ Z ↔ IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + act g (c h))
    (hB : ∀ c, c ∈ B ↔ ∃ t, ∀ g, c g = act g t - t)
    (e : Q ≃+ M) (rho : Representation (ZMod N) G M)
    (hr : ∀ g x, rho g (e x) = e (act (φ.symm g) x)) :
    Nat.card (↥Z ⧸ B.comap Z.subtype) = Nat.card (ReciprocityTheory.Gal.H1 rho) := by
  have hr' : ∀ g x, rho (φ g) (e x) = e (act g x) := fun g x => by
    rw [hr, MulEquiv.symm_apply_apply]
  let F : (G' → Q) → (G → M) := fun c g => e (c (φ.symm g))
  have hF : ∀ c g, F c (φ g) = e (c g) := fun c g => by simp only [F, MulEquiv.symm_apply_apply]
  have hFB : ∀ c, c ∈ B ↔ F c ∈ ReciprocityTheory.Gal.B1 rho := by
    intro c
    rw [hB, ReciprocityTheory.Gal.mem_coboundaries1]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨e t, fun g => ?_⟩
      simp only [F, ht, map_sub, hr]
    · rintro ⟨m, hm⟩
      refine ⟨e.symm m, fun g => ?_⟩
      have h1 := hm (φ g)
      rw [hF] at h1
      apply e.injective
      rw [h1, map_sub, ← hr', e.apply_symm_apply]
  have hZf : ∀ c : ↥Z, F c.1 ∈ ReciprocityTheory.Gal.Z1 rho := fun c => by
    obtain ⟨hc1, hc2⟩ := (hZ c.1).1 c.2
    refine ⟨((hc1.comp_continuous hφ.2).comp e).continuous, fun g h => ?_⟩
    simp only [F, map_mul, hc2, map_add, hr]
  have hZb : ∀ f : ↥(ReciprocityTheory.Gal.Z1 rho), (fun g => e.symm (f.1 (φ g))) ∈ Z := fun f => by
    obtain ⟨hf1, hf2⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).1 f.2
    refine (hZ _).2 ⟨((IsLocallyConstant.iff_continuous _).2 (hf1.comp hφ.1)).comp e.symm,
      fun g h => ?_⟩
    apply e.injective
    have h2 := hr' g (e.symm (f.1 (φ h)))
    rw [e.apply_symm_apply] at h2
    simp only [map_mul, hf2, map_add, AddEquiv.apply_symm_apply, h2]
  let E : ↥Z ≃ ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨F c.1, hZf c⟩
      invFun := fun f => ⟨fun g => e.symm (f.1 (φ g)), hZb f⟩
      left_inv := fun c => Subtype.ext (funext fun g => by
        show e.symm (F c.1 (φ g)) = c.1 g
        rw [hF, e.symm_apply_apply])
      right_inv := fun f => Subtype.ext (funext fun g => by
        show e (e.symm (f.1 (φ (φ.symm g)))) = f.1 g
        rw [e.apply_symm_apply, MulEquiv.apply_symm_apply]) }
  have hEsub : ∀ a b : ↥Z, ((E a - E b : ↥(ReciprocityTheory.Gal.Z1 rho)) : G → M) = F ((a - b : ↥Z) : G' → Q) :=
    fun a b => funext fun g => by
      show e (a.1 (φ.symm g)) - e (b.1 (φ.symm g)) = e (a.1 (φ.symm g) - b.1 (φ.symm g))
      rw [map_sub]
  refine Nat.card_congr (Quotient.congr E fun a b => ?_)
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap,
    Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_subtype, hEsub, hFB]

theorem card_H0_transport (φ : G' ≃* G) (act : G' → Q → Q)
    (e : Q ≃+ M) (rho : Representation (ZMod N) G M)
    (hr : ∀ g x, rho g (e x) = e (act (φ.symm g) x)) :
    Nat.card {x : Q // ∀ g, act g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  have hr' : ∀ g x, rho (φ g) (e x) = e (act g x) := fun g x => by
    rw [hr, MulEquiv.symm_apply_apply]
  refine Nat.card_congr
    { toFun := fun x => ⟨e x.1, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => by rw [hr, x.2]⟩
      invFun := fun m => ⟨e.symm m.1, fun g => by
        apply e.injective
        rw [← hr', e.apply_symm_apply]
        exact (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 m.2 (φ g)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun m => Subtype.ext (e.apply_symm_apply m.1) }

end Generic

theorem card_H1_H0_transport : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I) (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (e : (↥LA.T ⧸ I) ≃+ M) (rho : Representation (ZMod N) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA I hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → Nat.card (QuotientCohomology LA I hI) = Nat.card (ReciprocityTheory.Gal.H1 rho) ∧ Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  intro l _ K LL _ _ _ O _ _ A LA I hI N M _ _ _ _ e rho hrho
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hφ := GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1
  refine ⟨card_H1_transport _ hφ (fun g x => actQ LA I hI g x) (quotientCocycles LA I hI) (BQ LA I hI)
    (fun c => Iff.rfl) (fun c => ?_) e rho hrho,
    card_H0_transport _ (fun g x => actQ LA I hI g x) e rho hrho⟩
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun g => (congrFun ht g).symm⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, funext fun g => (ht g).symm⟩

end GlobalTheory.GaloisTransport
