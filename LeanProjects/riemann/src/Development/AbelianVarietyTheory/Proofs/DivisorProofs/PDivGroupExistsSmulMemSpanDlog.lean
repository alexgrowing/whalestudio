import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers

set_option autoImplicit false

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem lie_eq_zero_of_dlog {p : ℕ} [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O)
    {ε : PreTilt O p} {hε : IsPrimitiveSystem ε} {G : PDivGroup p O} (hD : HasDatum hε G)
    (x : G.Lie) (hx : ∀ χ, x (dlog G χ) = 0) : x = 0 := by
  haveI : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩
  obtain ⟨D, e, fil, lie, -, hb⟩ := hD
  have hG : Function.Surjective (G.pairing O).flip := (G.pairing_flip_bijective C).2
  have h0 : bQuot D (lie.symm x) = 0 :=
    GlobalTheory.DetInv.HTKer.pairingO_inj (hε := hε) hG e _ _ fun χ => by
      rw [hb, hx]; simp [pairingO]
  obtain ⟨m, hm⟩ := D.Fil.mkQ_surjective (lie.symm x)
  have h1 : D.bb m = 0 := by
    rw [← hm] at h0; exact h0
  have h2 : lie.symm x = 0 := by
    rw [← hm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact h1
  simpa using congrArg lie h2

theorem exists_smul_mem_span_dlog : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → ∃ c : O, c ≠ 0 ∧ ∀ w : G.omega, c • w ∈ Submodule.span O (Set.range (dlog G)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hD
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O G.omega := (GlobalTheory.PDiv.omega_finite_projective p C v O hv G).1
  set S := Submodule.span O (Set.range (dlog G)) with hS
  let T := Submodule.torsion O (G.omega ⧸ S)
  let π : G.omega →ₗ[O] (G.omega ⧸ S) ⧸ T := T.mkQ ∘ₗ S.mkQ
  have hπ : Function.Surjective π := T.mkQ_surjective.comp S.mkQ_surjective
  haveI : Module.Flat O ((G.omega ⧸ S) ⧸ T) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    exact Submodule.QuotientTorsion.torsion_eq_bot
  haveI : Module.Free O ((G.omega ⧸ S) ⧸ T) := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O ((G.omega ⧸ S) ⧸ T)
  have hcoord : ∀ i, b.coord i ∘ₗ π = 0 := fun i =>
    lie_eq_zero_of_dlog C hv hD _ fun χ => by
      change b.coord i (T.mkQ (S.mkQ (dlog G χ))) = 0
      have hs : S.mkQ (dlog G χ) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact Submodule.subset_span ⟨χ, rfl⟩
      rw [hs, map_zero, map_zero]
  have hzero : ∀ q : (G.omega ⧸ S) ⧸ T, q = 0 := fun q => by
    obtain ⟨w, rfl⟩ := hπ q
    refine b.ext_elem fun i => ?_
    have := LinearMap.congr_fun (hcoord i) w
    simpa using this
  have htor : Module.IsTorsion O (G.omega ⧸ S) := fun q => by
    have := hzero (T.mkQ q)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion_iff] at this
    exact this
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htor
  refine ⟨c, nonZeroDivisors.ne_zero hc0, fun w => ?_⟩
  have := Submodule.mem_annihilator.1 hc (S.mkQ w) Submodule.mem_top
  rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

end GlobalTheory.PDivLat
