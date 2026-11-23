import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoLMk
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKTorsionRed

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {ρ : Representation LL G V}

theorem coboundary_mem_blochKato_cocycles (m : V) (hm : Continuous fun g => ρ g m) : (fun g => ρ g m - m) ∈ finiteCocycles PD ρ := by
  refine ⟨⟨?_, fun g h => ?_⟩, m ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · simp_rw [sub_eq_add_neg]
    exact hm.add continuous_const
  · simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  · simp [actVB, sub_tmul]

def latticeCoboundaryCocycle (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (x : ↥L.T) : ↥(latticeCocycles L) :=
  ⟨fun g => ρ g x - x, Submodule.mem_inf.2 ⟨(coboundary_mem_blochKato_cocycles PD (x : V) (hρ x)).1,
    Submodule.mem_pi.2 fun g _ => L.T.sub_mem (L.stable g x x.2) x.2⟩⟩

theorem lattice_reduction_coboundary_mem_cocycles (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (I : Submodule O ↥L.T)
    (hI : StableSub L I) (x : ↥L.T) :
    redT L I (latticeCoboundaryCocycle PD L hρ x) = LinearMap.pi (fun g => actQ L I hI g - LinearMap.id) (I.mkQ x) := by
  funext g
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Submodule.mkQ_apply, actQ,
    Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub]
  rfl

theorem mem_HfQ_iff (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (I : Submodule O ↥L.T)
    (hI : StableSub L I) (c : G → ↥L.T ⧸ I) :
    c ∈ HfQ PD L I hI ↔ ∃ a : ↥(latticeCocycles L), (a : G → V) ∈ finiteCocycles PD ρ ∧ c = redT L I a := by
  constructor
  · intro h
    obtain ⟨_, ⟨a0, ha0, rfl⟩, _, ⟨xb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xb
    refine ⟨a0 + latticeCoboundaryCocycle PD L hρ x, (finiteCocycles PD ρ).add_mem ha0.2 (coboundary_mem_blochKato_cocycles PD (x : V) (hρ x)), ?_⟩
    rw [map_add, lattice_reduction_coboundary_mem_cocycles PD L hρ I hI x]
    rfl
  · rintro ⟨a, ha, rfl⟩
    exact Submodule.mem_sup_left ⟨a, ⟨a.2, ha⟩, rfl⟩

theorem mem_HfQ_iff_red : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ HfQ (P.PD K) LA _ hI ↔ ∃ a : ↥(latticeCocycles LA), (a : ↥(GK K) → A.V) ∈ finiteCocycles (P.PD K) A.ρ ∧ c = redT LA _ a := by
  intro l _ P K LL _ _ _ O _ _ _hO A LA ϖ r hI c
  exact mem_HfQ_iff (P.PD K) LA A.cont _ hI c

end GlobalTheory.BKTorsionRed
