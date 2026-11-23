import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory.Cartier

namespace GlobalTheory.DenominatorExistenceLemmas

variable {M W : Scheme.{0}}

theorem finite_app (f : M ⟶ W) [IsProper f] [IsLocallyNoetherian W] {L : ReciprocityTheory.ChartRestriction.G.Semi.LB M}
    (hL : IsAmpleLB L) {V : W.Opens} (hV : IsAffineOpen V) : (f.app V).hom.Finite := by
  obtain ⟨_, hfa⟩ := GlobalTheory.ProperFinite.isFiniteQC_pushforward f hL (structureModule M)
  exact hfa V hV

variable [IsIntegral M] [IsIntegral W]

omit [IsIntegral W] in

theorem gen_mem_preimage (f : M ⟶ W) [IsDominant f] {U : W.Opens} {y : W} (hy : y ∈ U) :
    genericPoint M ∈ f ⁻¹ᵁ U := by
  obtain ⟨m, hm⟩ := f.denseRange.exists_mem_open U.isOpen ⟨y, hy⟩
  exact gen_mem (U := f ⁻¹ᵁ U) (x := m) hm

omit [IsIntegral W] in

theorem fnOf_map {U V : M.Opens} (e : V ≤ U) (h : genericPoint M ∈ V) (a : Γ(M, U)) :
    fnOf V h (M.presheaf.map (homOfLE e).op a) = fnOf U (e h) a := by
  exact fnOf_resG e h a

theorem exists_denominator {V : W.Opens} (hV : IsAffineOpen V) (hg : genericPoint W ∈ V) {ι : Type} [Finite ι]
    (c : ι → W.functionField) :
    ∃ d : Γ(W, V), fnOf V hg d ≠ 0 ∧ ∀ i, ∃ a : Γ(W, V), fnOf V hg a = fnOf V hg d * c i := by
  have : Nonempty V := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen W V hV
  obtain ⟨⟨d, hd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Γ(W, V)) c
  refine ⟨d, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd, fun i => ?_⟩
  obtain ⟨a, ha⟩ := hdc i
  refine ⟨a, ?_⟩
  rw [Algebra.smul_def] at ha
  exact ha

theorem exists_denominator_all (f : M ⟶ W) [IsDominant f] {V : W.Opens} (hV : IsAffineOpen V)
    (hg : genericPoint W ∈ V) (hg' : genericPoint M ∈ f ⁻¹ᵁ V) (hf : (f.app V).hom.Finite) {r : ℕ}
    (co : Fin r → M.functionField →+ W.functionField)
    (hco : ∀ j c x, co j (functionFieldMap f c * x) = c * co j x) :
    ∃ d : Γ(W, V), fnOf V hg d ≠ 0 ∧ ∀ j (b : Γ(M, f ⁻¹ᵁ V)), ∃ a : Γ(W, V),
      fnOf V hg a = fnOf V hg d * co j (fnOf (f ⁻¹ᵁ V) hg' b) := by
  let := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(W, V) Γ(M, f ⁻¹ᵁ V) := hf
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Γ(W, V)) (M := Γ(M, f ⁻¹ᵁ V))
  obtain ⟨d, hd0, hd⟩ := exists_denominator hV hg
    (fun p : Fin r × Fin n => co p.1 (fnOf (f ⁻¹ᵁ V) hg' (s p.2)))
  refine ⟨d, hd0, fun j b => ?_⟩
  have hb : b ∈ Submodule.span Γ(W, V) (Set.range s) := hs ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact hd (j, k)
  | zero => exact ⟨0, by simp only [map_zero, mul_zero]⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hx'
    exact ⟨a + a', by rw [map_add, map_add, map_add, ha, ha', mul_add]⟩
  | smul t x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨t * a, ?_⟩
    have ht : fnOf (f ⁻¹ᵁ V) hg' (t • x) = functionFieldMap f (fnOf V hg t) * fnOf (f ⁻¹ᵁ V) hg' x := by
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra]
      congr 1
      exact GlobalTheory.Cartier.DomPull.fnOf_app f hg' t
    rw [ht, hco, map_mul, ha]
    ring

theorem exists_pow_mul_eq (f : M ⟶ W) [IsDominant f] [QuasiCompact f] [QuasiSeparatedSpace M] {V : W.Opens}
    (hV : IsAffineOpen V) (hg : genericPoint W ∈ V) (hg' : genericPoint M ∈ f ⁻¹ᵁ V) {y : W} (hy : y ∈ V)
    {V' : W.Opens} (hy' : y ∈ V') (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) :
    ∃ (u : W.functionField) (b : Γ(M, f ⁻¹ᵁ V)), UnitAt y u ∧
      fnOf (f ⁻¹ᵁ V) hg' b = functionFieldMap f u * fnOf (f ⁻¹ᵁ V') h z := by
  obtain ⟨g, hgV', hyg⟩ := hV.exists_basicOpen_le ⟨y, hy'⟩ hy
  have hle : M.basicOpen (f.app V g) ≤ f ⁻¹ᵁ V' := by
    rw [← Scheme.preimage_basicOpen]
    exact fun x hx => hgV' hx
  have hgb : genericPoint M ∈ M.basicOpen (f.app V g) := by
    rw [← Scheme.preimage_basicOpen]
    exact gen_mem_preimage f hyg
  obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated M (f ⁻¹ᵁ V)
    (f.isCompact_preimage hV.isCompact) (IsQuasiSeparated.of_quasiSeparatedSpace _) (f.app V g) (M.presheaf.map (homOfLE hle).op z)
  have e0 : M.basicOpen (f.app V g) ≤ f ⁻¹ᵁ V := M.basicOpen_le _
  have h1 : fnOf _ hgb (M.presheaf.map (homOfLE e0).op b) =
      fnOf _ hgb (M.presheaf.map (homOfLE e0).op (f.app V g)) ^ n *
        fnOf _ hgb (M.presheaf.map (homOfLE hle).op z) := by
    rw [← map_pow, ← map_mul]
    exact congrArg _ hb
  rw [fnOf_map, fnOf_map, fnOf_map] at h1
  refine ⟨fnOf V hg g ^ n, b, ?_, ?_⟩
  · have hu : UnitAt y (fnOf V hg g) := (unitAt_fnOf_iff hy hg g).2 hyg
    clear h1 hb
    induction n with
    | zero => simpa using unitAt_one y
    | succ n ih => rw [pow_succ]; exact ih.mul hu
  · rw [map_pow, ← GlobalTheory.Cartier.DomPull.fnOf_app f hg' g]
    exact h1

omit [IsIntegral M] [IsIntegral W] in

theorem exists_local_denominator (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    [IsProper f] [IsLocallyNoetherian W] (L : ReciprocityTheory.ChartRestriction.G.Semi.LB M) (hL : IsAmpleLB L) {r : ℕ}
    (co : Fin r → M.functionField →+ W.functionField)
    (hco : ∀ j c x, co j (functionFieldMap f c * x) = c * co j x) (y : W) :
    ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧
      ∀ y' ∈ V, ∀ V' : W.Opens, y' ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r),
        RegAt y' (fnOf V (gen_mem hy) d * co j (fnOf (f ⁻¹ᵁ V') h z)) := by
  obtain ⟨V, hVa, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian f
  have : TopologicalSpace.NoetherianSpace M := GlobalTheory.IsAmpleLB.noetherianSpace hL
  have hg' : genericPoint M ∈ f ⁻¹ᵁ V := gen_mem_preimage f hyV
  obtain ⟨d, hd0, hd⟩ := exists_denominator_all f hVa (gen_mem hyV) hg' (finite_app f hL hVa) co hco
  refine ⟨V, hyV, d, hd0, fun y' hy'V V' hy'V' h z j => ?_⟩
  obtain ⟨u, b, hu, hb⟩ := exists_pow_mul_eq f hVa (gen_mem hyV) hg' hy'V hy'V' h z
  obtain ⟨a, ha⟩ := hd j b
  have hz : fnOf (f ⁻¹ᵁ V') h z = functionFieldMap f u⁻¹ * fnOf (f ⁻¹ᵁ V) hg' b := by
    rw [hb, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu.ne_zero, map_one, one_mul]
  rw [hz, hco, mul_left_comm (fnOf V (gen_mem hyV) d), ← ha]
  exact hu.inv.regAt.mul (regAt_fnOf hy'V _ a)

end GlobalTheory.DenominatorExistenceLemmas
