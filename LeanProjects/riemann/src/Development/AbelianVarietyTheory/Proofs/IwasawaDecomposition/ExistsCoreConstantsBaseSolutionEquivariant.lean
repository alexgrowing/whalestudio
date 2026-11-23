import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffField
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeoConst

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem phiAt_eq (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ) (f : T.R ((i : ℕ) + 1)) :
    phiAt T i σ hV c f = adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) σ))
      (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) c)
      (rdU (T.U ((i : ℕ) + 1) σ) f) := by
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W),
      castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) c) (rdU (T.U ((i : ℕ) + 1) σ) f)) =
      adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) c)
        (rdU (T.U ((i : ℕ) + 1) σ) f) := by
    intro W hV
    subst hV
    rfl
  exact key _ hV

theorem eqAt_base (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (hL : R.toLevCh.Is A.μ0) (hT : TieIn T R κ v₀) (i : Fin D.R.m) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (h : O.EquivAt (κ i) cc) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) :
    EqAt T R κ O T.σ₀ hV cc := by
  intro g k hk f hf
  obtain ⟨h1, h2⟩ := h g k hk f hf
  obtain ⟨y, hy⟩ := GlobalTheory.ChiDetValues.chiC_mem_coeff T R κ v₀ hL hT i g
  have hy' : D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) =
      ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) := by
    rw [hy, chiC, Units.coe_prod]
  refine ⟨h1, y, hy', fun x => ?_⟩
  have e : T.σ₀ y = D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) :=
    (RingHom.congr_fun (res_embLL T hT.alg hT.laws.pins.2.2.1) y).symm
  rw [phiAt_eq, phiAt_eq, e, hy']
  exact h2 x

set_option maxHeartbeats 1000000 in

theorem exists_constants : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (cc : ∀ i : Fin D.R.m, (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → (∀ i, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (cc i) 1) → ∃ cE, (∀ i : Fin D.R.m, cE ((i : ℕ) + 1) T.σ₀ = cc i) ∧ TieIn (setCE T cE) R κ v₀ ∧ (∀ i, OMPins (setCE T cE) R κ v₀ O i) ∧ Fired (setCE T cE) R κ v₀ O (fun _ => 1) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O cc hL hT hpb hP hO
  have H : ∀ (n : ℕ) (σ : T.Q.c.F →+* ℂ), ∃ c : (T.U (n + 1) σ).Comp → ℂ, CUnit c ∧ ∀ hn : n < D.R.m,
      (σ = T.σ₀ → HEq c (cc ⟨n, hn⟩)) ∧ (GoodEmb T.Q.c σ → ∀ hV : T.V (n + 1) σ = Wc D ⟨n, hn⟩,
        EqAt T R κ (O ⟨n, hn⟩) σ hV c) := by
    intro n σ
    by_cases hn : n < D.R.m
    · by_cases hσ : σ = T.σ₀
      · subst hσ
        exact ⟨cc ⟨n, hn⟩, (hO ⟨n, hn⟩).2.1.2.2.2.1, fun _ => ⟨fun _ => HEq.rfl, fun _ hV =>
          eqAt_base T R κ v₀ hL hT ⟨n, hn⟩ (O ⟨n, hn⟩) (cc ⟨n, hn⟩) (hO ⟨n, hn⟩).1 hV⟩⟩
      · by_cases hg : GoodEmb T.Q.c σ ∧ T.V (n + 1) σ = Wc D ⟨n, hn⟩
        · obtain ⟨c, hc, hE⟩ := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R κ v₀ O hL hT hpb hP ⟨n, hn⟩ σ hg.1 hg.2
          exact ⟨c, hc, fun _ => ⟨fun h => absurd h hσ, fun _ _ => hE⟩⟩
        · exact ⟨fun _ => 1, fun _ => norm_one, fun _ => ⟨fun h => absurd h hσ, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩⟩
    · exact ⟨fun _ => 1, fun _ => norm_one, fun h => absurd h hn⟩
  choose c hc hc' using H
  have h0 : ∀ i : Fin D.R.m, c i T.σ₀ = cc i := fun i => eq_of_heq ((hc' i T.σ₀ i.2).1 rfl)
  refine ⟨fun j => Nat.casesOn (motive := fun j => ∀ σ : T.Q.c.F →+* ℂ, (T.U j σ).Comp → ℂ) j (fun _ _ => 1) c, h0, ?_,
    hP, fun i => ?_, fun i σ hσ hV => (hc' i σ i.2).2 hσ hV⟩
  · refine ⟨{ toLawsM := hT.laws.toLawsM, cUnit := ?_, muVal := hT.laws.muVal, muConj := hT.laws.muConj,
              intAll := hT.laws.intAll, modelW := hT.laws.modelW, familyUniformisationBasePointOrthogonal := hT.laws.familyUniformisationBasePointOrthogonal, kfHalf := hT.laws.kfHalf,
              adPin := hT.laws.adPin }, hT.alg, hT.kap, hT.hv₀, hT.chiR, hT.x0⟩
    intro j _ σ _
    cases j with
    | zero => exact fun _ => norm_one
    | succ n => exact hc n σ
  · have h := hO i
    rw [← h0 i] at h
    exact h

end GlobalTheory.RealGeoConst
