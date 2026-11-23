import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.CrysInteg

theorem mem_of_semiBC {A B M N Q : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup Q] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (g : N →+ Q) (H : AddSubgroup Q) (hg : ∀ (r : B) (x : M), g (r • u x) ∈ H) (y : N) : g y ∈ H := by
  have hspan : y ∈ Submodule.span B (Set.range u) := by
    have h1 : (Submodule.span B (Set.range u)).mkQ = 0 := h.hom_ext fun x => by
      rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩
    have := LinearMap.congr_fun h1 y
    rwa [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have key : ∀ z ∈ Submodule.span B (Set.range u), ∀ r : B, g (r • z) ∈ H := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      exact fun r => hg r x
    | zero =>
      intro r
      rw [smul_zero, map_zero]
      exact H.zero_mem
    | add z w _ _ hz hw =>
      intro r
      rw [smul_add, map_add]
      exact add_mem (hz r) (hw r)
    | smul s z _ hz =>
      intro r
      rw [smul_smul]
      exact hz _
  have := key y hspan 1
  rwa [one_smul] at this

def divSub {R σ ι : Type} [CommRing R] (S : Subring R) (τ : σ) (i : ι) (k : ℕ) :
    AddSubgroup (σ → ι → R⟦X⟧) where
  carrier := {v | (k.factorial : R) * coeff k (v τ i) ∈ S}
  add_mem' {v w} hv hw := by
    change (k.factorial : R) * coeff k (v τ i + w τ i) ∈ S
    rw [map_add, mul_add]
    exact add_mem hv hw
  zero_mem' := by
    change (k.factorial : R) * coeff k (0 : R⟦X⟧) ∈ S
    rw [map_zero, mul_zero]
    exact zero_mem _
  neg_mem' {v} hv := by
    change (k.factorial : R) * coeff k (-(v τ i)) ∈ S
    rw [map_neg, mul_neg]
    exact neg_mem hv

theorem factorial_mul_coeff_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ x, c x ∈ P.M) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (J τ y) ∈ S O K e) → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → ∀ y τ i (k : ℕ), (k.factorial : K⟦X⟧) * coeff k (lam y τ i) ∈ S O K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c hc PP p J hJ lam hsm htr y τ i k
  refine mem_of_semiBC (EE.tr_bc p) lam (divSub (S O K e).toSubring τ i k) (fun r x => ?_) y
  change (k.factorial : K⟦X⟧) * coeff k (lam (r • EE.tr p x) τ i) ∈ S O K e
  rw [hsm, htr, PowerSeries.coeff_mul_C, ← mul_assoc]
  exact mul_mem (hJ τ r k) (A_le_S l e (frob_mem_A l (mem_tot.1 (hc x) (τ - 1) i)))

end GlobalTheory.BKGal.CrysInteg
