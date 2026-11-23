import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatumStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.LieHodgeTate

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → (∀ x : G.dual.Lie, (∀ t, x (hodgeTate G t) = 0) → x = 0) ∧ (∀ x : G.dual.Lie, ∃ y : latt G, ∀ t, WittVector.fontaineTheta O p (y.1 t) = x (hodgeTate G t)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  obtain ⟨D, e, fil, lie, hal, -⟩ := hG
  have hprim : IsPrimitiveRoot (root ε).untilt p := by
    have := hε 1
    simpa [zeta] using this
  obtain ⟨-, hle, -, hfil, -, -⟩ := HodgeTateBound.bound p C v O hv ε hprim ℤ_[p] G.height D
  obtain ⟨-, -, -, hsurj, hν, -, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hprim
  have hsingle : ∀ i, toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
    intro i
    funext j
    simp only [toO, LinearEquiv.apply_symm_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · let φ : (Fin G.height → O) →ₗ[O] O :=
      x ∘ₗ fil.symm.toLinearMap ∘ₗ (LinearMap.codRestrict D.Fil D.al fun u => hle ⟨u, rfl⟩)
    have hφ : φ = 0 := by
      apply (Pi.basisFun O (Fin G.height)).ext
      intro i
      rw [Pi.basisFun_apply, LinearMap.zero_apply, ← hsingle i]
      have h1 : (⟨D.al (toO e (e.symm (Pi.single i 1))), hle ⟨_, rfl⟩⟩ : D.Fil) =
          fil (hodgeTate G (e.symm (Pi.single i 1))) := Subtype.ext (hal _)
      change x (fil.symm ⟨D.al _, _⟩) = 0
      rw [h1, LinearEquiv.symm_apply_apply]
      exact hx _
    ext w
    obtain ⟨u, hu⟩ := hfil _ (fil w).2
    have h1 : WittVector.fontaineTheta O p (nu ε) • fil w = ⟨D.al u, hle ⟨u, rfl⟩⟩ :=
      Subtype.ext hu.symm
    have h2 : WittVector.fontaineTheta O p (nu ε) * x w = 0 := by
      rw [← smul_eq_mul, ← map_smul, ← fil.symm_apply_apply (WittVector.fontaineTheta O p (nu ε) • w),
        map_smul fil, h1]
      exact LinearMap.congr_fun hφ u
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hν
    · simpa using h
  · haveI : ValuationRing O := ValuationRing.of_integers v hv
    haveI : Module.Free O ((Fin G.height → O) ⧸ LinearMap.ker D.bb) := by
      haveI : Module.Free O (LinearMap.range D.bb) :=
        GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing O _
      exact Module.Free.of_equiv (D.bb.quotKerEquivRange).symm
    haveI : Module.Free O ((Fin G.height → O) ⧸ D.Fil) := by
      change Module.Free O ((Fin G.height → O) ⧸ LinearMap.ker D.bb); infer_instance
    obtain ⟨N', hN'⟩ := GlobalTheory.exists_isCompl_of_projective_quotient D.Fil
    let ρ : (Fin G.height → O) →ₗ[O] O :=
      x ∘ₗ fil.symm.toLinearMap ∘ₗ D.Fil.projectionOnto N' hN'
    choose r hr using fun i => hsurj (ρ (Pi.single i 1))
    obtain ⟨L, hL⟩ := GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum p C v O hv ε hε G G.height D e fil hal
    refine ⟨L r, fun t => ?_⟩
    rw [hL]
    have hρ : ∀ w, ρ w = ∑ i, WittVector.fontaineTheta O p (r i) * w i := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ ρ w]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr, smul_eq_mul, mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hθ : WittVector.fontaineTheta O p (r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i))) =
        ρ (D.al (toO e t)) := by
      rw [hρ, dotProduct, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, RingHom.map_mulVec]
      rfl
    rw [hθ]
    have h3 : D.Fil.projectionOnto N' hN' (D.al (toO e t)) = fil (hodgeTate G t) := by
      rw [show D.al (toO e t) = ((fil (hodgeTate G t) : D.Fil) : Fin _ → O) from hal t,
        Submodule.projectionOnto_apply_left]
    change x (fil.symm (D.Fil.projectionOnto N' hN' (D.al (toO e t)))) = _
    rw [h3, LinearEquiv.symm_apply_apply]

end GlobalTheory.LieHodgeTate
