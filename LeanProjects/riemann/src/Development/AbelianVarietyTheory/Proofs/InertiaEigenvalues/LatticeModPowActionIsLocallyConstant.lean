import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Pointwise

namespace GlobalTheory.InertiaEigenvalues

theorem actQ_pow_isLocallyConstant : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), IsLocallyConstant fun g : G => actQ LA _ hI g x := by
  intro l _ G _ _ LL _ _ _ O _ _ hG A LA r hI x
  obtain ⟨_, _, _, hTR, hO⟩ := hG
  haveI := hTR
  haveI : CharZero LL := charZero_of_injective_algebraMap (algebraMap ℚ_[l] LL).injective
  haveI := IsModuleTopology.topologicalAddGroup LL A.V
  set c : LL := ((l : ℕ) : LL) ^ r with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hT : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hO LA.T LA.fg LA.span
  have hcT : IsOpen (c • (LA.T : Set A.V)) := hT.smul₀ hc0
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [IsLocallyConstant.iff_exists_open]
  intro g0
  refine ⟨(fun g => A.ρ g t - A.ρ g0 t) ⁻¹' (c • (LA.T : Set A.V)),
    hcT.preimage ((A.cont _).sub continuous_const), ?_, ?_⟩
  · show A.ρ g0 t - A.ρ g0 t ∈ c • (LA.T : Set A.V)
    rw [sub_self]
    exact ⟨0, LA.T.zero_mem, smul_zero c⟩
  · intro g hg
    obtain ⟨w, hw, hwe⟩ := hg
    simp only [actQ, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨⟨w, hw⟩, Submodule.mem_top, ?_⟩
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_sub, actT, LinearMap.restrict_coe_apply,
      LinearMap.coe_restrictScalars]
    rw [← algebraMap_smul LL ((l : O) ^ r) w, map_pow, map_natCast]
    exact hwe

end GlobalTheory.InertiaEigenvalues
