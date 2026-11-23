import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsM (D : D7) (T : Core D) (h : LawsM T) : GamAt T := by
  intro j hj σ hσ k γ hst hc
  obtain ⟨hgood, hA, -, -, -, -, hrest⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr : 0 < D.R.r := (hrest j hj).2.1
  have hpins := h.pins
  unfold Formalism.L2.Pj.Par.Pins at hpins
  have hlev := hpins.2.1
  unfold Formalism.L2.Pj.Par.PinLevel at hlev
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hlev.1
  have h3 : 3 ≤ T.Q.l.M := by
    obtain ⟨p, hlt, hp⟩ := Nat.exists_infinite_primes (T.Q.l.M + 1)
    have h0 : T.Q.l.M.factorization p = 0 := Nat.factorization_eq_zero_of_lt (by omega)
    have := hgood p hp
    simpa [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt, h0] using this
  have hU := (Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 (h.unf j hj σ hσ)
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ :=
    GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ _ _ _ hU hA hr k γ hst hc
  obtain ⟨th, hrk, hth, hD⟩ := h.dictU j hj σ hσ
  have hc' : ∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x =
        ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) • y := by
    rw [← hM]; exact hc
  have hu1 : u = 1 :=
    GlobalTheory.PrincCore.root_eq_one (T.V j σ) hrk hr (T.U j σ).X (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hth hD
      (h.muUnit j hj σ hσ) (D.host.g 0 * D.host.g 1) (hM ▸ h3) (h.levelK j hj σ hσ) k γ γ' hγ' hc' u n hn hu he
  have hγγ : γ' = γ := by
    ext a b
    have := congrFun (congrFun he a) b
    simpa [hu1] using this
  exact hγγ ▸ hγ'

theorem gamAt_of_lawsJ : ∀ (D : D7) (T : CoreJ D), LawsJ T → GamAt T.toCore := by
  intro D T h
  exact gamAt_of_lawsM D T.toCore h.toLawsM

end GlobalTheory.RunIn
