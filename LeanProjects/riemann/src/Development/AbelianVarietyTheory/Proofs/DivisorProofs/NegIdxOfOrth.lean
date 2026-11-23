import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopTie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridNodeSignatureSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSumSelfDualExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeIndexAdditive

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower.TopExists

section Sum

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Doubling GlobalTheory.AdelicU Matrix

theorem negIdx_of_orth {D : D7} {V₁ V₂ WW : HSp D} {p q : ℕ} (hr : V₁.rank + V₂.rank = WW.rank)
    (ι₁ : V₁.V →ₗ[D.host.E] WW.V) (ι₂ : V₂.V →ₗ[D.host.E] WW.V) (e₁ : Formalism.BasicNotions.HSpace.IsIsomEmb V₁ WW ι₁)
    (e₂ : Formalism.BasicNotions.HSpace.IsIsomEmb V₂ WW ι₂) (ho : ∀ x y, WW.hD (ι₁ x) (ι₂ y) = 0) (h1 : NegIdx V₁ p)
    (h2 : NegIdx V₂ q) : NegIdx WW (p + q) := by
  intro τ
  have c1 := (Formalism.UG.P.sig_data _ _ _ (h1 τ)).1
  have c2 := (Formalism.UG.P.sig_data _ _ _ (h2 τ)).1
  simp only [Fintype.card_fin] at c1 c2
  let v : Fin V₁.rank ⊕ Fin V₂.rank → WW.V :=
    Sum.elim (fun i => ι₁ (V₁.frame i)) (fun j => ι₂ (V₂.frame j))
  have hv : (Matrix.of fun k l => WW.hT (v k) (v l)) = fromBlocks V₁.gram 0 0 V₂.gram := by
    ext (i | i) (j | j)
    · simp only [v, HSpace.gram, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, Sum.elim_inl]; exact e₁ _ _
    · have h := WW.herm.eq (ι₂ (V₂.frame j)) (ι₁ (V₁.frame i))
      have h0 : WW.hT (ι₂ (V₂.frame j)) (ι₁ (V₁.frame i)) = 0 := ho _ _
      rw [h0, map_zero] at h
      simp [v, ← h]
    · simp only [v, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply]
      exact ho (V₁.frame j) (V₂.frame i)
    · simp only [v, HSpace.gram, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, Sum.elim_inr]; exact e₂ _ _
  have key := (GlobalTheory.SumSig.gram_family WW v).symm.trans hv
  set C := Matrix.of fun i k => WW.frame.repr (v k) i
  have hst : Function.Semiconj (tauE D τ) star star := fun a => D.sp.cm.cmUnram.2.1 _ a
  have hmap : (C.map (tauE D τ))ᴴ * gramAt D WW τ * C.map (tauE D τ) =
      fromBlocks (gramAt D V₁ τ) 0 0 (gramAt D V₂ τ) := by
    have := congrArg (fun M => M.map (tauE D τ)) key
    simp only [Matrix.map_mul, Matrix.conjTranspose_map _ hst, Matrix.fromBlocks_map, map_zero] at this
    simpa [gramAt] using this
  have hF := GlobalTheory.FrameComplement.hasSignature_fromBlocks (h1 τ) (h2 τ)
  obtain ⟨-, Q0, hQ0⟩ := Formalism.UG.P.sig_data _ _ _ hF
  have e : WW.rank - (p + q) = (V₁.rank - p) + (V₂.rank - q) := by omega
  rw [e]
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp; omega) (C.map (tauE D τ) * Q0) ?_
  calc (C.map (tauE D τ) * Q0)ᴴ * gramAt D WW τ * (C.map (tauE D τ) * Q0)
        = Q0ᴴ * ((C.map (tauE D τ))ᴴ * gramAt D WW τ * C.map (tauE D τ)) * Q0 := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hmap, hQ0]

end Sum

section Idem

open Formalism.IndefR.Lev in

theorem idem_exists {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}
    (hL : Lc.Is μ₀) (W : G.Weil) (t : T) : ∃ e : AE D, IsIdemSum e (locPl G t) := by
  classical
  obtain ⟨e0, he0, -⟩ := W.cosVec_is
  have hW := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he0
  have hQ := hL.Q_pl t
  have key : ∀ P ∈ Lc.Q t, ∀ P' ∈ G.pl.W0, (IsConjPl P P' ∨ IsConjPl P' P) → P ∈ G.pl.W0 := by
    intro P hPQ P' hP' hc
    have hu : P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
      rcases hc with hc | hc
      · exact GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
      · exact (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).symm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP'
    rw [G.pl.under_w hv] at hu
    rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
    · exact absurd hu (G.pl.levelPlace_ne_basePlace t P hPQ)
    · rw [G.pl.w_Q t P hPQ (hu ▸ h1), hu]
      exact Finset.mem_image_of_mem _ hv
  have hnc : ∀ P ∈ locPl G t, ∀ P' ∈ locPl G t, ¬ IsConjPl P P' := by
    intro P hP1 P' hP2 hc
    simp only [locPl, Finset.mem_union] at hP1 hP2
    rcases hP1 with h1 | h1 <;> rcases hP2 with h2 | h2
    · exact hW P h1 P' h2 hc
    · exact hW P h1 P' (key P' h2 P h1 (Or.inr hc)) hc
    · exact hW P (key P h1 P' h2 (Or.inl hc)) P' h2 hc
    · exact (hQ P h1).2 P' h2 hc
  let es : Formalism.L2.DIV.Pl D.host.E → AE D := fun PP =>
    if h : ¬ IsConjPl PP PP then (Formalism.IndefR.Fin.idem_exists_at PP h).choose else 0
  have hes : ∀ PP ∈ locPl G t, Formalism.L2.NTheta.IsIdemAt (es PP) PP := by
    intro PP hPP
    have h := hnc PP hPP PP hPP
    simp only [es, dif_pos h]
    exact (Formalism.IndefR.Fin.idem_exists_at PP h).choose_spec.1
  refine ⟨∑ PP ∈ locPl G t, es PP, ⟨es, hes, rfl⟩, ?_⟩
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun PP hPP => Finset.sum_eq_zero fun PP' hPP' => ?_
  exact Formalism.IndefR.Fin.idem_orth_conj (hnc PP hPP PP hPP) (hes PP hPP) (hes PP' hPP') (hnc PP hPP PP' hPP')

end Idem

section Chars

open GlobalTheory.HeckeCharsOfSquare

theorem chars {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}
    (hL : Lc.Is μ₀) (W : G.Weil) (i j : Fin D.R.m) (t : T) :
    IsHeckeChar D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧
    IsHeckeChar D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
    IsHeckeChar D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧
    IsHeckeChar D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) / (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))) ∧
    ResEta D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (rankV D i j) ∧
    ResEta D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (rankV D (i + 1) (j + 1)) ∧
    ResEta D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))
      (rankV D (i + 1) (j + 1) + rankV D i j) ∧
    ResEta D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) / (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)))
      (rankV D (i + 1) (j + 1) + rankV D i j) := by
  have ht : Odd D.R.t := D.R.t_odd
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  have hs : Odd (sLen D) := hr.add_even (by decide : Even 6)
  have hi := i.2
  have hj := j.2
  have rk : ∀ a b : ℕ, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b := fun a b ha hb =>
    (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hth : ResEta D (Lc.mu t (j + 1)) 0 ∧ ResEta D Lc.eta 1 := by
    have hW := W.om_is (.mu t i j) (show Node.InRange D.R.m (.grid i (j + 1)) from ⟨by omega, by omega⟩)
    have hS := hW.resS
    have hT := hW.resT
    have e1 : (G.pS (.mu t i j)).rank = rankV D i j := rk _ _ (by omega) (by omega)
    have e2 : (G.pT (.mu t i j)).rank = rankV D i (j + 1) := rk _ _ (by omega) (by omega)
    rw [GridData.chrS, e1] at hS
    rw [GridData.chrT, e2] at hT
    refine GlobalTheory.HeckeCharsOfSquare.resEta_of_att hS hT ?_
    have e3 : rankV D i (j + 1) = rankV D i j + D.R.t := by simp only [rankV]; ring
    rw [e3, ← add_assoc]
    exact Even.add_odd ⟨_, rfl⟩ ht
  have hdn : ResEta D (G.ch.chi (D.R.m - i)) 0 := by
    have hW := W.om_is (.chi i (j + 1)) (show Node.InRange D.R.m (.grid (i + 1) (j + 1)) from ⟨by omega, by omega⟩)
    have hS := hW.resS
    have hT := hW.resT
    have e1 : (G.pS (.chi i (j + 1))).rank = rankV D (i + 1) (j + 1) := rk _ _ (by omega) (by omega)
    have e2 : (G.pT (.chi i (j + 1))).rank = rankV D i (j + 1) := rk _ _ (by omega) (by omega)
    rw [GridData.chrS, e1] at hS
    rw [GridData.chrT, e2] at hT
    refine (GlobalTheory.HeckeCharsOfSquare.resEta_of_att hS hT ?_).1
    have e3 : rankV D (i + 1) (j + 1) = rankV D i (j + 1) + sLen D := by simp only [rankV]; ring
    rw [e3, add_comm, ← add_assoc]
    exact Even.add_odd ⟨_, rfl⟩ hs
  have hη : IsHeckeChar D Lc.eta := hL.eta.1
  have hμ : IsHeckeChar D (Lc.mu t (j + 1)) := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul (hL.mu0 j).1 (hL.xi t).1
  have hχ : IsHeckeChar D (G.ch.chi (D.R.m - i)) := (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)).1
  have hα := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul hμ (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_pow hη (rankV D i j % 2))
  have hβ := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul hχ (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_pow hη (rankV D i j % 2))
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hs
  have rα : ResEta D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (rankV D i j) :=
    GlobalTheory.HeckeCharsOfSquare.resEta_of_mod (GlobalTheory.HeckeCharsOfSquare.resEta_mul hth.1 (GlobalTheory.HeckeCharsOfSquare.resEta_pow hth.2 (rankV D i j % 2))) (by omega)
  have rβ : ResEta D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (rankV D (i + 1) (j + 1)) :=
    GlobalTheory.HeckeCharsOfSquare.resEta_of_mod (GlobalTheory.HeckeCharsOfSquare.resEta_mul hdn (GlobalTheory.HeckeCharsOfSquare.resEta_pow hth.2 (rankV D i j % 2))) (by omega)
  refine ⟨hα, hβ, GlobalTheory.HeckeCharsOfSquare.isHeckeChar_div hα hβ, GlobalTheory.HeckeCharsOfSquare.isHeckeChar_div hβ hα, rα, rβ, ?_, GlobalTheory.HeckeCharsOfSquare.resEta_div rβ rα⟩
  exact GlobalTheory.HeckeCharsOfSquare.resEta_of_mod (GlobalTheory.HeckeCharsOfSquare.resEta_div rα rβ) (by omega)

end Chars

end GlobalTheory.SqTower.TopExists

end
