import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem absNorm_halfDifferent_dvd_discr (D : D7) :
    Ideal.absNorm D.host.𝔟 ∣ (NumberField.discr D.host.E).natAbs := by
  have ht : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
      (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)
  have hdvd : D.host.𝔟 ∣ differentIdeal ℤ (𝓞 D.host.E) := by
    rw [ht, D.host.𝔟_spec.1, mul_assoc]
    exact dvd_mul_right _ _
  have h1 := map_dvd Ideal.absNorm hdvd
  rwa [NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)] at h1

theorem exists_dataX_discr_absNorm : FactPrincipalDatum → ∀ (D : D7) (T : Core D) (h : LawsCore T), GlobalTheory.RunIn.GamAt T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧ Xx.NA = (discr D.host.E).natAbs ∧ Xx.NC = Ideal.absNorm D.host.ccK ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} := by
  intro _ D T h hG j hj σ hσ k
  obtain ⟨Xx, h1, h2, h3, -⟩ :=
    GlobalTheory.LatticeData.exists_dataX_of_hasPrinc D T h j hj σ hσ (hG j hj σ hσ) k
  refine ⟨{ Xx with
    NA := (NumberField.discr D.host.E).natAbs
    NC := Ideal.absNorm D.host.ccK
    NA_pos := Int.natAbs_pos.2 (NumberField.discr_ne_zero D.host.E)
    NC_pos := Nat.pos_of_ne_zero fun e => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    NA_sub := fun x hx => ?_
    NC_sub := fun x hx => ?_ }, h1, h2, rfl, rfl, h3⟩
  · rw [h3] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hv
      obtain ⟨z, hz⟩ := GlobalTheory.LatticeData.absNorm_mul_mem_one D ha
      obtain ⟨c, hc⟩ := absNorm_halfDifferent_dvd_discr D
      have e : (((NumberField.discr D.host.E).natAbs : ℕ) : D.host.E) * a =
          algebraMap (𝓞 D.host.E) D.host.E ((c : 𝓞 D.host.E) * z) := by
        rw [hc, map_mul, map_natCast, hz, Nat.cast_mul]; ring
      rw [smul_smul, e, algebraMap_smul]
      exact Xx.L'.smul_mem _ hu
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact Xx.L'.smul_mem c hv
  · rw [h3]
    exact Submodule.subset_span ⟨_, GlobalTheory.LatticeData.absNorm_ccK_mem D, x, hx, rfl⟩

end GlobalTheory.ArcCM
