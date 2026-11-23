import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnramOfFixedIwahori

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

theorem psPlain : PsPlain := by
  intro F _ _ w σ ψ hψ hs hl
  have key : ∀ x : (w.adicCompletion F)ˣ, ((absPow (w.adicCompletion F) 1 x : ℂˣ) : ℂ) =
      ((normV w : ℕ) : ℂ) ^ (-ord (w.adicCompletion F) x) := fun x => by
    obtain ⟨h1, h2, -⟩ := (GlobalTheory.CompletionNorm.norm_nabs_valuation F w).1 x
    rw [val_absPow, Complex.cpow_one, ← h1, h2]
    push_cast
    rfl
  refine ⟨GlobalTheory.RoadU.chars ψ hψ, ?_, ?_, ?_⟩
  · exact (GlobalTheory.IwahoriSupport.hasSupport_chars σ.irred ψ hψ hs).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · intro y hy z hz h
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at h
    refine hl i j ⟨fun x hx => ?_, ?_⟩
    · have h3 := ((GlobalTheory.CompletionNorm.norm_nabs_valuation F w).1 x).2.2
      have h0 : ord (w.adicCompletion F) x = 0 := by
        have h4 : WithZero.exp (-ord (w.adicCompletion F) x) = WithZero.exp (0 : ℤ) :=
          h3.symm.trans (Eq.trans hx WithZero.exp_zero.symm)
        have := WithZero.exp_injective h4
        omega
      have h5 : absPow (w.adicCompletion F) 1 x = 1 := Units.ext (by rw [key, h0]; simp)
      rw [h, MonoidHom.mul_apply, h5, mul_one]
    · have h1 := (GlobalTheory.CompletionNorm.norm_nabs_valuation F w).1 (atFin w (unif w))
      have h2 : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
        unif_spec w
      have h0 : ord (w.adicCompletion F) (atFin w (unif w)) = 1 := by
        have := WithZero.exp_injective (h1.2.2.symm.trans h2)
        omega
      have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
        intro e
        have e' : ((normV w : ℕ) : ℝ) = 0 := by exact_mod_cast e
        have h6 := h1.2.1
        rw [h0, e'] at h6
        have h7 : ‖((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F)‖ ≠ 0 :=
          norm_ne_zero_iff.2 (Units.ne_zero _)
        exact h7 (by simpa using h6)
      rw [h, MonoidHom.mul_apply, Units.val_mul, key, h0, mul_assoc, zpow_neg_one, inv_mul_cancel₀ hq, mul_one]

end UpperTheory.V.Z.Win.Birth

end
