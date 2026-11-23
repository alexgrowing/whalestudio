import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot

noncomputable section

open Ideal CategoryTheory Opposite

namespace GlobalTheory

open PDivGroup Sandwich Dieudonne

theorem omega_eq_zero_of_smul_eq_zero : GlobalTheory.Published.PrismaticDieudonneHodge → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) (c : O) (w : G.omega), c ≠ 0 → c • w = 0 → w = 0 := by
  intro h p _ C _ _ _ v O _ _ hv _ _ G c w hc hcw
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  obtain ⟨ε, hε⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) C v O hv
  obtain ⟨M, D, φ, r, ι, π, -, hM, -, -, hr, -, hex, -⟩ := h p C v O hv ε hε
  haveI := (hM G).1
  haveI := (hM G).2.1
  obtain ⟨h1, -, -⟩ := free_of_reduction (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv)
    (ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε) (r G) (hr G).1 fun m => ((hr G).2 m).1
  haveI := h1
  apply (hex G).1
  rw [map_zero]
  have h2 : c • ι G w = 0 := by rw [← map_smul, hcw, map_zero]
  exact (smul_eq_zero.1 h2).resolve_left hc

end GlobalTheory
