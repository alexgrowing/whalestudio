import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoLMk
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevelKer

theorem mk_eq_of_smul {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (π : LL) (hπ : π ≠ 0)
    (hpr : ∀ v : V, π ^ r • v = ϖ ^ r • v) (u v w : V) (hu : u ∈ L.T) (hv : v ∈ L.T)
    (hvw : π⁻¹ ^ r • u - w ∈ L.T) (hyw : v = π ^ r • w) :
    (Submodule.Quotient.mk (⟨v, hv⟩ : ↥L.T) : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) =
      Submodule.Quotient.mk ⟨u, hu⟩ := by
  rw [Submodule.Quotient.eq]
  have ht : (⟨v, hv⟩ : ↥L.T) - ⟨u, hu⟩ = ϖ ^ r • (-(⟨_, hvw⟩ : ↥L.T)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_neg]
    rw [← hpr, smul_neg, smul_sub, smul_smul, ← mul_pow, mul_inv_cancel₀ hπ, one_pow, one_smul, hyw]
    abel
  rw [ht]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem hfQ_of_ioL_mem_HfD : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ HfD (P.PD K) LA → c ∈ HfQ (P.PD K) LA _ hI := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ hϖ r hI c hc
  obtain ⟨π, hπdef⟩ : ∃ π : LL, π = algebraMap O LL ϖ := ⟨_, rfl⟩
  have hπ : π ≠ 0 := by
    obtain ⟨⟨hDom, hDVR, hFr⟩, -, -, -, -⟩ := hO
    haveI := hDom; haveI := hDVR; haveI := hFr
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective O LL (by rw [← hπdef, h, map_zero]))
  clear hO

  obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨xq, rfl⟩, hsum⟩ := Submodule.mem_sup.1 hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xq
  obtain ⟨w, hwdef⟩ : ∃ w : ↥(GK K) → A.V, w = z + fun g => A.ρ g x - x := ⟨_, rfl⟩
  have hcob : (fun g => A.ρ g x - x) ∈ finiteCocycles (P.PD K) A.ρ := by
    refine ⟨⟨?_, fun g h => ?_⟩, x ⊗ₜ[ℚ_[l]] (1 : _), fun g => ?_⟩
    · simp_rw [sub_eq_add_neg]
      exact (A.cont x).add continuous_const
    · simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
    · simp [actVB, sub_tmul]
  have hw : w ∈ finiteCocycles (P.PD K) A.ρ := hwdef ▸ (finiteCocycles (P.PD K) A.ρ).add_mem hz hcob

  choose ch hch using fun g => Submodule.Quotient.mk_surjective _ (c g)

  have hpt : ∀ g, (π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) - w g ∈ LA.T := by
    intro g
    have key : GlobalTheory.BKFinLevel.ioL LA ϖ r (c g) = Submodule.Quotient.mk (p := LA.T) (w g) :=
      by rw [← congrFun hsum g, hwdef]; rfl
    have h2 : (Submodule.Quotient.mk (π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) : A.V ⧸ LA.T) =
        Submodule.Quotient.mk (w g) :=
      hπdef ▸ (GlobalTheory.BKFinLevel.ioL_mk LA ϖ r (ch g)).symm.trans ((congrArg _ (hch g)).trans key)
    exact (Submodule.Quotient.eq _).1 h2
  obtain ⟨y, hydef⟩ : ∃ y : ↥(GK K) → A.V, y = fun g => π ^ r • w g := ⟨_, rfl⟩
  have hyf : y ∈ finiteCocycles (P.PD K) A.ρ := by
    have h := (finiteCocycles (P.PD K) A.ρ).smul_mem (π ^ r) hw
    subst hydef; exact h
  have hpr : ∀ v : A.V, π ^ r • v = ϖ ^ r • v := fun v => by
    rw [hπdef, ← map_pow, algebraMap_smul]
  have hyT : ∀ g, y g ∈ LA.T := by
    intro g
    have : y g = ((ch g : ↥LA.T) : A.V) - ϖ ^ r • ((π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) - w g) := by
      rw [← hpr, smul_sub, smul_smul, ← mul_pow, mul_inv_cancel₀ hπ, one_pow, one_smul]
      simp [hydef]
    rw [this]
    exact LA.T.sub_mem (ch g).2 (LA.T.smul_mem _ (hpt g))
  have hyZ : y ∈ latticeCocycles LA := ⟨hyf.1, fun g _ => hyT g⟩
  refine Submodule.mem_sup_left ⟨⟨y, hyZ⟩, ⟨hyZ, hyf⟩, ?_⟩
  funext g
  have e : (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) ⟨y, hyZ⟩) g =
      Submodule.Quotient.mk (⟨y g, hyT g⟩ : ↥LA.T) := rfl
  rw [e, ← hch g]
  exact mk_eq_of_smul LA ϖ r π hπ hpr _ _ (w g) (ch g).2 (hyT g) (hpt g) (by rw [hydef])

end GlobalTheory.BKFinLevelKer
