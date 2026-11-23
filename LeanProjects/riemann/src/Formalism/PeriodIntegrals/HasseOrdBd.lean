import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

def PI.HasseOrdBd : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (T : ℕ),
    PublishedIntClos → Q.InCurve → Q.InTie S → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    ∀ (f : B.Cusp j (addL wF wL T)) (β : Idx D j G.N →₀ ℕ), (β.sum fun _ n => n) ≤ a0 D j T - 1 →
    ∀ (hx : hasse X la G.w β (frac X la G.w T (emb X la G.N (X.inc _ f))) ∈ HK X la G.w wF) (ζ : PtsG G la),
      (ep (unifO X la G.N) ζ : EReal) *
          (X.vAt la (Q.y ζ) (X.inc _ f) - (T : EReal) * X.depth S.sW wL la (Q.y ζ)) ≤
        toE (Q.ordA ζ (toA0K X la G.w wF ⟨hasse X la G.w β (frac X la G.w T (emb X la G.N (X.inc _ f))), hx⟩))
