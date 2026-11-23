import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaTripleBaseDataCharactersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseTripleSpacesOfSeesawStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodRationalSchroedingerModelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateUnitaryAdelicIsoMapHaarFundamentalDomaiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicVectorsCorrespondSchrodingerThetaMapStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRepOrientedPairRationalSchrodingerStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

theorem GlobalTheory.SquareAgree.exists_isOver : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
      IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∃ (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
      (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
      IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' := by
  intro D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hωA hωB
  obtain ⟨p, q, hs, hz1, hz2⟩ := hT.sig
  have hev := hT.even
  have hrk := hT.rank
  let e : Fin X.rank ≃ Fin (W.rank + W₁.rank) := finCongr hT.rank
  obtain ⟨Bs, Xc, hψ, hα, hβ, hB, hXc, hemb, hκ⟩ := GlobalTheory.T.exists_thetaTriple_baseData_characters D ψ W W₁ X α β hT ωA hωA
  obtain ⟨V, V', Ws, hJV, hJV', hJW, hV, hV', hWs, hcart⟩ := GlobalTheory.T.exists_placewise_triple_spaces_of_seesaw D W W₁ X A A₁ B α β hT p q hs e Bs hB hemb
  obtain ⟨cA, hcA⟩ := GlobalTheory.T.exists_addEquiv_symplecticCoords_orientedModel D W X e (-1) (by norm_num)
  obtain ⟨cB, hcB⟩ := GlobalTheory.T.exists_addEquiv_symplecticCoords_orientedModel D W₁ X e 1 one_ne_zero
  obtain ⟨hμ1, hd1⟩ := GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_fundamentalDomain D W 1 hJV one_ne_zero ν 𝓕 hν
  obtain ⟨hμ2, hd2⟩ := GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_fundamentalDomain D W₁ (-1) hJV' (by norm_num) ν₁ 𝓕₁ hν₁
  obtain ⟨M, hMμ, hMd, hM⟩ := GlobalTheory.T.exists_good_rational_schroedingerModel D Bs hB V Ws _ _ _ _ hV hWs _ _ hμ1 hd1
  obtain ⟨M', hMμ', hMd', hM'⟩ := GlobalTheory.T.exists_good_rational_schroedingerModel D Bs hB V' Ws _ _ _ _ hV' hWs _ _ hμ2 hd2
  have hJt : V.J = (if true then 1 else -1 : D.host.E) • W.gram := by simpa using hJV
  have hJf : V'.J = (if false then 1 else -1 : D.host.E) • W₁.gram := by simpa using hJV'
  have hct : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ V.θ w = (if true then 1 else -1 : ℂ) • A.cart τ ∧
      Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ) := fun w => by
    obtain ⟨τ, h1, h2, -, h4⟩ := hcart w
    exact ⟨τ, h1, by simpa using h2, h4⟩
  have hcf : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ V'.θ w = (if false then 1 else -1 : ℂ) • A₁.cart τ ∧
      Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ) := fun w => by
    obtain ⟨τ, h1, -, h3, h4⟩ := hcart w
    exact ⟨τ, h1, by simpa using h3, h4⟩
  have hcA' : ∀ u, cA u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if true then -1 else 1 : D.host.E) • W.gram)) :
      Matrix (Fin X.rank) (Fin W.rank) (AE D)) := fun u => by simpa using hcA u
  have hcB' : ∀ u, cB u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if false then -1 else 1 : D.host.E) • W₁.gram)) :
      Matrix (Fin X.rank) (Fin W₁.rank) (AE D)) := fun u => by simpa using hcB u
  obtain ⟨hA1, hA2⟩ := GlobalTheory.T.algebraicVectors_correspond_schrodinger_thetaMap D ψ θ hθ true W X A B e Bs hB hψ V Ws _ _ _ _ hJt hJW hV hWs hct M hM cA hcA'
  obtain ⟨hB1, hB2⟩ := GlobalTheory.T.algebraicVectors_correspond_schrodinger_thetaMap D ψ θ hθ false W₁ X A₁ B e Bs hB hψ V' Ws _ _ _ _ hJf hJW hV' hWs hcf M' hM' cB hcB'
  obtain ⟨om, hom, hwA⟩ := GlobalTheory.T.exists_weilRep_orientedPair_rationalSchrodinger D ψ θ hθ true W X A B e Bs hB hψ V Ws _ _ _ _ hJt hJW hV hWs hct M hM cA hcA' β (β / α) ωA hωA
  obtain ⟨om', hom', hwB⟩ := GlobalTheory.T.exists_weilRep_orientedPair_rationalSchrodinger D ψ θ hθ false W₁ X A₁ B e Bs hB hψ V' Ws _ _ _ _ hJf hJW hV' hWs hcf M' hM' cB hcB' α (α / β) ωB hωB
  let Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank := ⟨p, q, V, V', Ws, M, M'⟩
  refine ⟨e, Bs, Γ, Xc, om, om', cA, cB, ?_, ?_⟩
  · exact
      { psi := hψ
        alpha := hα
        beta := hβ
        JW := hJV
        JW₁ := hJV'
        JX := hJW
        measW := hMμ
        domW := hMd
        measW₁ := hMμ'
        domW₁ := hMd'
        weilA := hwA
        weilB := hwB
        algA := hA1
        algA' := hA2
        algB := hB1
        algB' := hB2 }
  · refine ⟨hB, ?_, hXc, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hev
      exact
        { lt := by omega
          even := ⟨k, by omega⟩
          kappa := hκ
          eBig := by show 2 * (p + q) + 1 < (W.rank - W₁.rank) / 2; omega
          aBig := hz2
          hV := hV
          hV' := hV'
          hW := hWs
          hM := hM
          hM' := hM' }
    · show M.IsWeil Bs.ψ Xc.β (Xc.β / Xc.α) om
      rw [hα, hβ]; exact hom
    · show M'.IsWeil Bs.ψ Xc.α (Xc.α / Xc.β) om'
      rw [hα, hβ]; exact hom'

end
