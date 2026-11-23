import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.TateNat

theorem free_inj : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (a : O) (f : G → O), Continuous f → (∀ g h : G, d1 (twist ε O) f (g, h) = a * φ (c (g, h))) → a = 0 := by
  intro p _ O _ _ _ _ _ _ G _ _ χ c hgen φ ε hεφ ϖ hϖ hp hopen a f hf hd
  have key : ∀ n : ℕ, a ∈ (powSub (M := O) ϖ n : Submodule O O) := by
    intro n
    set N : Submodule O O := powSub (M := O) ϖ n with hN
    letI : Module ℤ_[p] (O ⧸ N) := Module.compHom (O ⧸ N) φ
    have hs : ∀ (t : ℤ_[p]) (x : O), t • (Submodule.Quotient.mk x : O ⧸ N) =
        Submodule.Quotient.mk (φ t * x) := fun t x => by
      show (φ t) • (Submodule.Quotient.mk x : O ⧸ N) = _
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
    haveI : Finite (O ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N.toAddSubgroup (hopen n)
    have hM : ∀ m : O ⧸ N, (p : ℤ_[p]) ^ n • m = 0 := by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [hs, Submodule.Quotient.mk_eq_zero, map_pow, map_natCast]
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
        obtain ⟨u, hu⟩ := hp
        refine mem_powSub.2 ⟨u ^ n * x, ?_⟩
        rw [hu, smul_eq_mul, mul_pow]
        ring
    have hlc : IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : O ⧸ N)) := by
      intro s
      have ho : IsOpen ((Submodule.Quotient.mk : O → O ⧸ N) ⁻¹' s) := by
        rw [isOpen_iff_forall_mem_open]
        intro x hx
        refine ⟨(fun y => y - x) ⁻¹' (N : Set O), fun y hy => ?_,
          (hopen n).preimage (continuous_id.sub continuous_const), ?_⟩
        · have e : (Submodule.Quotient.mk y : O ⧸ N) = Submodule.Quotient.mk x :=
            (Submodule.Quotient.eq N).2 hy
          show (Submodule.Quotient.mk y : O ⧸ N) ∈ s
          rw [e]
          exact hx
        · show x - x ∈ N
          rw [sub_self]
          exact N.zero_mem
      exact ho.preimage hf
    have h3 := ((hgen n) (O ⧸ N) hM).2.2 (Submodule.Quotient.mk a)
      (fun g => Submodule.Quotient.mk (f g)) hlc fun q => by
        obtain ⟨g, h⟩ := q
        have e := hd g h
        simp only [d1_apply] at e
        change (ε g : O) • f h - f (g * h) + f g = a * φ (c (g, h)) at e
        rw [smul_eq_mul, hεφ] at e
        simp only [GlobalTheory.TateTop.cob, hs]
        rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
        congr 1
        linear_combination -e
    exact (Submodule.Quotient.mk_eq_zero N).1 h3
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal O)
    (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hmem : a ∈ ⨅ i, (IsLocalRing.maximalIdeal O) ^ i := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨y, hy⟩ := mem_powSub.1 (key i)
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hy, smul_eq_mul]
    exact dvd_mul_right _ _
  rw [hbot] at hmem
  exact (Submodule.mem_bot O).1 hmem

end GlobalTheory.TateNat
