import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleSeqOfFiniteNonempty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientTorsionBoundedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeCompactPowSmulNhdsBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCocycleLiftOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCocyclesQuotientPowSmulModuleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCocycleCupNotCoboundaryFiniteLevelStatement

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem int_iso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : ReciprocityTheory.ChartRestriction.T2.IntIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO hF i D hD hinv x hx
  haveI := hD.t2'
  haveI : IsGalois K (PadicAlgCl p) := inferInstance
  haveI : CompactSpace (Formalism.GaloisCohomology.GK p K) := inferInstance
  haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  induction x using Submodule.Quotient.induction_on with
  | H c => ?_
  by_contra hx0
  have hcB : (c : G → VT ⧸ D.T) ∉ B1 D.ρA := fun h => hx0 ((Submodule.Quotient.mk_eq_zero _).2 h)
  obtain ⟨r, hr⟩ := GlobalTheory.T.continuous_quotient_torsion_bounded D.T hD.lat hD.openT ϖ hϖ (c : G → VT ⧸ D.T) c.2.1
  have hcyc : ∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧
      ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n} := by
    intro g n ζ hζ
    obtain ⟨a, h1, h2⟩ := hD.cyc (i g) n ζ hζ
    have e : (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) (i g) = D.ε g := by
      change D.ε (i.symm (i g)) = D.ε g
      exact congrArg D.ε (i.symm_apply_apply g)
    rw [e] at h2
    exact ⟨a, h1, h2⟩
  obtain ⟨hcpt, hopen, hbasis⟩ := GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis D hO.compact hF.emb hD.lat hD.perf hD.t2' ϖ hϖ
  haveI := hcpt
  let X : ℕ → Type := fun k => G → ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k)
  let Y : ∀ k, Set (X k) := fun k => {z | z ∈ Z1 (quotRep D.ρTl' ϖ (r + k)) ∧
    cupMod D (c : G → VT ⧸ D.T) ϖ (r + k) z ∉ B2 (twist D.ε (KO O))}
  have hle : ∀ k, r + k ≤ r + (k + 1) := fun k => by omega
  let f : ∀ k, X (k + 1) → X k := fun k z g =>
    Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (z g)
  have hfin : ∀ k, (Y k).Finite := fun k =>
    (GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen hT hK hO.p_mem i D.ρTl' (sub_contAction D.contT' _ D.stT') ϖ hϖ hopen (r + k)).subset
      (fun z hz => hz.1)
  have hne : ∀ k, (Y k).Nonempty := fun k => by
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.T.exists_cocycle_cup_not_coboundary_finiteLevel hT hK hO.ring hO.compact hO.t2 hO.adic hO.p_mem hO.p_ne hF.emb i D
      hcyc hD.lat hD.perf hD.contT hD.openT hD.t2 hD.t2' hD.cs hD.cs' ϖ hϖ c.1 c.2 hcB r hr (r + k)
      (by omega)
    exact ⟨z, hz, hz'⟩
  have hmap : ∀ k, ∀ z ∈ Y (k + 1), f k z ∈ Y k := by
    rintro k z ⟨hz, hnc⟩
    refine ⟨factor_mem_cocycles_pow_quot D.ρTl' ϖ (hle k) hz, ?_⟩
    have e := cupMod_factor D hr (Nat.le_add_right r k) (hle k) z
    show cupMod D (c : G → VT ⧸ D.T) ϖ (r + k)
      (fun g => Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (z g)) ∉ _
    rw [e]
    exact hnc
  obtain ⟨s, hs⟩ := GlobalTheory.exists_compatible_seq_of_finite_nonempty X f Y hfin hne hmap
  let w : ℕ → G → ↥D.T' := fun k g => qlift (s k g)
  have hwZ : ∀ k, (fun g => (Submodule.Quotient.mk (w k g) :
      ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k))) ∈ Z1 (quotRep D.ρTl' ϖ (r + k)) := by
    intro k
    have e : (fun g => (Submodule.Quotient.mk (w k g) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k))) =
        s k := funext fun g => mk_qlift _
    rw [e]
    exact (hs k).1.1
  have hstep : ∀ k g, w (k + 1) g - w k g ∈ powSub (M := ↥D.T') ϖ (r + k) := by
    intro k g
    apply (Submodule.Quotient.eq _).1
    have e1 : (Submodule.Quotient.mk (w (k + 1) g) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k)) =
        f k (s (k + 1)) g := by
      show _ = Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (s (k + 1) g)
      conv_rhs => rw [← mk_qlift (s (k + 1) g)]
      rfl
    rw [e1, (hs k).2]
    exact (mk_qlift (s k g)).symm
  obtain ⟨e, he, hew⟩ := GlobalTheory.T.exists_continuous_cocycle_lift_of_compatible' D.ρTl' ϖ r hopen hbasis w hwZ hstep
  have h1 := hx (Submodule.Quotient.mk ⟨e, he⟩)
  have h2 : ((cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩) : G × G → KO O) ∈ B2 (twist D.ε (KO O)) := by
    have h3 : D.inv (Submodule.Quotient.mk (cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩)) = D.inv 0 := by
      rw [map_zero]
      exact h1
    have h6 := (Submodule.Quotient.mk_eq_zero _).1 (hinv h3)
    exact h6
  apply (hs 0).1.2
  have h4 : cupMod D (c : G → VT ⧸ D.T) ϖ (r + 0) (s 0) = ((cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩) : G × G → KO O) := by
    funext q
    refine pairKO_eq_of_sub_mem D (hr q.1) ?_
    rw [← map_sub]
    refine powSub_stable _ ϖ r q.1 _ ?_
    have h5 := hew 0 q.2
    rw [← neg_sub]
    exact Submodule.neg_mem _ h5
  rw [h4]
  exact h2

end GlobalTheory.LocDualInt
