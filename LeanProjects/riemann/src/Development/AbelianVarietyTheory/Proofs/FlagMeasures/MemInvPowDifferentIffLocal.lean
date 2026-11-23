import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

namespace GlobalTheory.DiffLoc

theorem ddS_ne (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

theorem mem_ddPow_neg_iff : ∀ (D : D7) (Z : LocDat D) (n : ℕ), n ≤ D.R.rS → ∀ y : D.host.E,
    y ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ p : PlF D, (D.s.atP p).ιE y * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ n ∈ (Z.M p).L.O := by
  intro D Z n hn y
  let a : Fin (D.R.rS + 1) := ⟨D.R.rS - n, by omega⟩
  have he : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = n := by
    show ((D.R.rS : ℤ) - ((D.R.rS - n : ℕ) : ℤ)) = n
    rw [Nat.cast_sub hn]; ring
  have hspan : ∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
      ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)) =
      Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
    intro p
    have h := locDiffC_holds D Z p a
    rw [he] at h
    exact h
  have hf : ∀ p : PlF D, frFac Z.δ p a * btT Z p ^ n = 1 := by
    intro p
    rw [bt_frFac_eq Z p a]
    have hk : D.R.rS - a.val = n := by show D.R.rS - (D.R.rS - n) = n; omega
    rw [hk]
    set U := (bt_T_unit Z p).unit
    have hU : (U : (D.s.atP p).Ep) = btT Z p := IsUnit.unit_spec _
    rw [← hU, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  have hinv : ∀ z : D.host.E, z ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ d ∈ ddS D ^ n, z * d ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z
    rw [zpow_neg, zpow_natCast, FractionalIdeal.mem_inv_iff (pow_ne_zero n (ddS_ne D))]
  constructor
  · intro hy p
    have hm : (D.s.atP p).ιE y ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
      rw [← hspan p]; exact Submodule.subset_span ⟨y, hy, rfl⟩
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hm
    change (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O
    rw [← ho, Subring.smul_def, smul_eq_mul, mul_assoc, hf p, mul_one]
    exact o.2
  · intro h
    rw [hinv]
    intro d hd
    rw [FractionalIdeal.mem_one_iff]
    have hloc : ∀ p : PlF D, (D.s.atP p).ιE (y * d) ∈ (Z.M p).L.O := by
      intro p
      have hmem : ∀ x ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
          ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)),
          (D.s.atP p).ιE d * x ∈ (Z.M p).L.O := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨z, hz, rfl⟩ := hx
          obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((hinv z).1 hz d hd)
          rw [← map_mul, mul_comm, ← ho]
          exact bt_iota_int Z p o
        | zero => rw [mul_zero]; exact Subring.zero_mem _
        | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
        | smul o x _ hx => rw [Subring.smul_def, smul_eq_mul, mul_left_comm]; exact mul_mem o.2 hx
      have hdf : (D.s.atP p).ιE d * frFac Z.δ p a ∈ (Z.M p).L.O :=
        hmem _ (by rw [hspan p]; exact Submodule.subset_span (Set.mem_singleton _))
      have hyp : (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O := h p
      have e : (D.s.atP p).ιE (y * d) =
          ((D.s.atP p).ιE y * btT Z p ^ n) * ((D.s.atP p).ιE d * frFac Z.δ p a) := by
        calc (D.s.atP p).ιE (y * d) = (D.s.atP p).ιE y * (D.s.atP p).ιE d * (frFac Z.δ p a * btT Z p ^ n) := by
              rw [hf p, mul_one, map_mul]
          _ = _ := by ring
      rw [e]
      exact mul_mem hyp hdf
    obtain ⟨o, ho⟩ := ((GlobalTheory.HL.PlacesInt.integers_local (placesOf Z)).1 (y * d)).1 hloc
    exact ⟨o, ho⟩

end GlobalTheory.DiffLoc
