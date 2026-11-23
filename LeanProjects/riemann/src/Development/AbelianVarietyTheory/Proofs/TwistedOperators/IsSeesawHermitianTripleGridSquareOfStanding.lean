import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvesterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareTripleFinitePlacesOfOrientedRoutesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num)

namespace GlobalTheory.SquareTripleForm

variable {D : D7}

theorem hasSignature_add {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b : ℕ} (h : Formalism.UG.HasSignature J a b) :
    a + b = n := by
  obtain ⟨e, -⟩ := h
  simpa using (Fintype.card_congr e).symm

theorem isTriple_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m),
    SquareStanding G t → ∀ M : Vol G, M.Is t →
      GlobalTheory.SquareComm.IsTriple (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) := by
  intro D T L sc G μ₀ hL W t i j hS M hM
  obtain ⟨e, Bs, Γ, X, om, om', hX, hY, -⟩ := GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j hS M hM
  have hi := i.2
  have hj := j.2
  have nv : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.node (.grid a b)).IsV (rankV D a b) ((D.R.m - b) / 2) :=
    fun a b ha hb => node_isV G hL (X := .grid a b) ⟨ha, hb⟩
  have rW : (G.V (.grid (↑i + 1) (↑j + 1))).rank = rankV D (↑i + 1) (↑j + 1) := (nv _ _ (by omega) (by omega)).rank
  have rW₁ : (G.V (.grid ↑i ↑j)).rank = rankV D ↑i ↑j := (nv _ _ (by omega) (by omega)).rank
  have rV : (G.V (.grid ↑i (↑j + 1))).rank = rankV D ↑i (↑j + 1) := (nv _ _ (by omega) (by omega)).rank
  have rV₁ : (G.V (.grid (↑i + 1) ↑j)).rank = rankV D (↑i + 1) ↑j := (nv _ _ (by omega) (by omega)).rank
  have hrank : (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).rank =
      (G.V (.grid (↑i + 1) (↑j + 1))).rank + (G.V (.grid ↑i ↑j)).rank := by
    show (G.V (.grid ↑i (↑j + 1))).rank + (G.V (.grid (↑i + 1) ↑j)).rank = _
    rw [rW, rW₁, rV, rV₁]; simp only [rankV]; ring
  obtain ⟨hχ, hχ0⟩ := GlobalTheory.SquareChars.chi_hecke_res G hL i
  have hμ := GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j
  have hμ0 := GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j
  have hη := GlobalTheory.SquareChars.isHeckeChar_pow' hL.eta.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  have hη1 := GlobalTheory.SquareChars.resEta_pow' (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  obtain ⟨p1, p2⟩ := GlobalTheory.SquareChars.rank_parity G hL i j
  refine ⟨GlobalTheory.SquareChars.isHeckeChar_mul' hμ hη, GlobalTheory.SquareChars.isHeckeChar_mul' hχ hη,
    resEta_parity (resEta_mul hμ0 hη1) (by rw [zero_add]; exact p2),
    resEta_parity (resEta_mul hχ0 hη1) (by rw [zero_add]; exact p1), hrank, ?_, ?_, ?_, ?_⟩
  · rw [hrank]; exact hY.geo.even
  · have sgn : ∀ a b (ha : a ≤ D.R.m) (hb : b ≤ D.R.m) τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid a b)) τ)
        ((G.V (.grid a b)).rank - (D.R.m - b) / 2) ((D.R.m - b) / 2) := by
      intro a b ha hb τ
      have s := (nv a b ha hb).sigOK (tauE D τ)
      rw [(nv a b ha hb).sig, ← (nv a b ha hb).rank] at s
      exact s
    have sgnN : ∀ a b (ha : a ≤ D.R.m) (hb : b ≤ D.R.m) τ, Formalism.UG.HasSignature (gramAt D (negSp (G.V (.grid a b))) τ)
        ((D.R.m - b) / 2) ((G.V (.grid a b)).rank - (D.R.m - b) / 2) := by
      intro a b ha hb τ
      have s := GlobalTheory.GridWeil.sigOK_neg (nv a b ha hb).sigOK (tauE D τ)
      have e : (negSp (G.V (.grid a b))).sig (tauE D τ) = ((G.V (.grid a b)).sig (tauE D τ)).swap := rfl
      rw [e, (nv a b ha hb).sig, ← (nv a b ha hb).rank] at s
      exact s
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    obtain ⟨τ₀, hτ₀, -⟩ := hX.cart w
    have tW : Formalism.UG.HasSignature (gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ₀)
        ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p := by
      refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
      have hs := hY.geo.hV.sig w
      rw [hX.JW, one_smul] at hs
      have hmap : (G.V (.grid (↑i + 1) (↑j + 1))).gram.map (Bs.emb w).1 = (gramAt D _ τ₀).map (starRingEnd ℂ) := by
        ext a b; simp [gramAt, hτ₀]
      rw [hmap] at hs
      exact hs
    have tW₁ : Formalism.UG.HasSignature (gramAt D (negSp (G.V (.grid ↑i ↑j))) τ₀) Γ.q
        ((G.V (.grid ↑i ↑j)).rank - Γ.q) := by
      refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
      have hs := hY.geo.hV'.sig w
      rw [hX.JW₁] at hs
      have hmap : ((-1 : D.host.E) • (G.V (.grid ↑i ↑j)).gram).map (Bs.emb w).1 =
          (gramAt D (negSp (G.V (.grid ↑i ↑j))) τ₀).map (starRingEnd ℂ) := by
        ext a b; simp [gramAt, hτ₀, HSpace.gram]
      rw [hmap] at hs
      exact hs
    have hp : Γ.p = (D.R.m - (↑j + 1)) / 2 := by
      have r1 := sgn (↑i + 1) (↑j + 1) (by omega) (by omega) τ₀
      have c1 := hasSignature_add r1
      have c2 := hasSignature_add tW
      have u := GlobalTheory.T.hasSignature_fst_unique_sylvester tW r1
      omega
    have hq : Γ.q = (D.R.m - ↑j) / 2 := GlobalTheory.T.hasSignature_fst_unique_sylvester tW₁ (sgnN ↑i ↑j (by omega) (by omega) τ₀)
    have h1 := hY.geo.eBig
    have h2 := hY.geo.aBig
    have h3 := hY.geo.lt
    dsimp only [spW, spW₁] at h1 h2 h3
    refine ⟨(D.R.m - (↑j + 1)) / 2, (D.R.m - ↑j) / 2, fun τ => ⟨sgn _ _ (by omega) (by omega) τ,
      sgn _ _ (by omega) (by omega) τ, ?_⟩, by rw [← hp, ← hq]; omega, by rw [← hp, ← hq]; exact h2⟩
    have sV := sgn ↑i (↑j + 1) (by omega) (by omega) τ
    have sV₁ := sgn (↑i + 1) ↑j (by omega) (by omega) τ
    have cV := hasSignature_add sV
    have cV₁ := hasSignature_add sV₁
    have s := GlobalTheory.Doubling.sigOK_hsum (nv ↑i (↑j + 1) (by omega) (by omega)).sigOK
      (nv (↑i + 1) ↑j (by omega) (by omega)).sigOK (tauE D τ)
    have e : (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).sig (tauE D τ) =
        (G.V (.grid ↑i (↑j + 1))).sig (tauE D τ) + (G.V (.grid (↑i + 1) ↑j)).sig (tauE D τ) := rfl
    rw [e, (nv ↑i (↑j + 1) (by omega) (by omega)).sig, (nv (↑i + 1) ↑j (by omega) (by omega)).sig] at s
    simp only [Prod.fst_add, Prod.snd_add] at s
    have e3 : (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).rank -
        ((D.R.m - (↑j + 1)) / 2 + (D.R.m - ↑j) / 2) =
        rankV D ↑i (↑j + 1) - (D.R.m - (↑j + 1)) / 2 + (rankV D (↑i + 1) ↑j - (D.R.m - ↑j) / 2) := by
      show (G.V (.grid ↑i (↑j + 1))).rank + (G.V (.grid (↑i + 1) ↑j)).rank - _ = _
      omega
    rw [e3]
    exact s
  · intro τ
    refine ⟨_, _, GlobalTheory.SquareExps.alpha_exp (G := G) hL t ↑i ↑j j.2 τ, GlobalTheory.SquareExps.beta_exp (G := G) hL ↑i ↑j i.2 τ, ?_⟩
    have key := GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre sc.cGap τ ↑i ↑j i.2 j.2
    rw [hrank, rW, rW₁]
    push_cast at key ⊢
    linarith
  · exact GlobalTheory.T.squareTriple_finitePlaces_of_orientedRoutes hL W t i j hS M hM e Bs Γ X om om' hX hY

end GlobalTheory.SquareTripleForm
