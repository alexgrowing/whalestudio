import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomicStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevel

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def ioL (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) :
    (↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) →ₗ[O] (V ⧸ L.T) :=
  (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T).liftQ
    (L.T.mkQ ∘ₗ (((algebraMap O LL ϖ)⁻¹ ^ r • (LinearMap.id : V →ₗ[LL] V)).restrictScalars O) ∘ₗ
      L.T.subtype) (by
    intro x hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.coe_smul,
      LinearMap.coe_restrictScalars, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [← algebraMap_smul LL (ϖ ^ r) (y : V), smul_smul, map_pow, ← mul_pow]
    rcases eq_or_ne (algebraMap O LL ϖ) 0 with h | h
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simpa using y.2
      · rw [h, inv_zero, zero_mul, zero_pow hr.ne', zero_smul]; exact L.T.zero_mem
    · rw [inv_mul_cancel₀ h, one_pow, one_smul]; exact y.2)

theorem ioL_mk (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (y : ↥L.T) :
    ioL L ϖ r (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r • (y : V)) := rfl

variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def cupQ (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O)
    (r : ℕ) (c : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (c' : G → ↥L'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L'.T)) (x : G × G) : LL :=
  (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (c x.1)) (ρ' x.1 (Formalism.MainNotions.LocalSituation.liftQ L' _ (c' x.2)))

end GlobalTheory.BKFinLevel
