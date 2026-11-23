import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section
namespace GlobalTheory.BottomPairData
variable {D : D7}

theorem sig_of_gram_one {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 ∧ (V.sig τ).1 = V.rank := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  have hq : (V.sig τ).2 = 0 := by
    by_contra hq
    let k : Fin (V.sig τ).2 := ⟨0, Nat.pos_of_ne_zero hq⟩
    have hk := congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
      Complex.one_re] at hk
    have : 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re := by
      rw [Matrix.mul_apply, Complex.re_sum]
      exact Finset.sum_nonneg fun l _ => by
        rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
    linarith
  refine ⟨hq, ?_⟩
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum, hq] at this
  omega

open GlobalTheory.Grid (neg neg_gram) in

def negFrame (A : HSp D) : CptF (neg A) := fun τ r c =>
  Sum.elim (fun _ => (0 : ℂ)) (fun k => if (k : ℕ) = (c : ℕ) then 1 else 0) r

open GlobalTheory.Grid (neg) in
theorem negFrame_inl (A : HSp D) (τ : D.what₂.Tau) (a : Fin ((neg A).sig (tauE D τ)).1) (c : Fin (neg A).rank) :
    negFrame A τ (Sum.inl a) c = 0 := rfl

open GlobalTheory.Grid (neg) in
theorem negFrame_inr (A : HSp D) (τ : D.what₂.Tau) (k : Fin ((neg A).sig (tauE D τ)).2) (c : Fin (neg A).rank) :
    negFrame A τ (Sum.inr k) c = if (k : ℕ) = (c : ℕ) then 1 else 0 := rfl

open GlobalTheory.Grid (neg neg_gram) in
theorem jpq_mul_negFrame (A : HSp D) (τ : D.what₂.Tau) :
    Formalism.UG.Jpq ((neg A).sig (tauE D τ)).1 ((neg A).sig (tauE D τ)).2 * negFrame A τ = -negFrame A τ := by
  ext r c
  rcases r with a | b
  · rw [Matrix.neg_apply, show negFrame A τ (Sum.inl a) c = 0 from rfl, neg_zero, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun x _ => by
      rcases x with x | x
      · rw [show negFrame A τ (Sum.inl x) c = 0 from rfl, mul_zero]
      · simp [Formalism.UG.Jpq]
  · simp only [Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      negFrame_inl, negFrame_inr, mul_zero, Finset.sum_const_zero, Matrix.neg_apply, Matrix.zero_apply, zero_mul, zero_add,
      Matrix.one_apply, neg_mul, ite_mul, one_mul, Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

open GlobalTheory.Grid (neg neg_gram) in
theorem negFrame_conj_mul (A : HSp D) (hg : A.gram = 1) (hA : A.SigOK) (τ : D.what₂.Tau) :
    (negFrame A τ)ᴴ * negFrame A τ = 1 := by
  obtain ⟨hq, hp⟩ := sig_of_gram_one hg hA (tauE D τ)
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  have e1 : ∀ x, star (negFrame A τ (Sum.inl x) a) * negFrame A τ (Sum.inl x) b = 0 := fun x => by
    rw [show negFrame A τ (Sum.inl x) a = 0 from rfl, star_zero, zero_mul]
  have e2 : ∀ x : Fin ((neg A).sig (tauE D τ)).2, star (negFrame A τ (Sum.inr x) a) * negFrame A τ (Sum.inr x) b =
      if (x : ℕ) = a ∧ (x : ℕ) = b then 1 else 0 := fun x => by
    rw [negFrame_inr, negFrame_inr]
    by_cases h1 : (x : ℕ) = a <;> by_cases h2 : (x : ℕ) = b <;> simp [h1, h2]
  rw [Finset.sum_eq_zero fun x _ => e1 x, zero_add, Finset.sum_congr rfl fun x _ => e2 x]
  have hk : (a : ℕ) < ((neg A).sig (tauE D τ)).2 := by
    show (a : ℕ) < (A.sig (tauE D τ)).1
    rw [hp]; exact a.2
  rw [Finset.sum_eq_single ⟨a, hk⟩]
  · by_cases h : a = b
    · simp [h]
    · rw [if_neg h, if_neg]; rintro ⟨-, h2⟩; exact h (Fin.ext h2)
  · intro x _ hx; rw [if_neg]; rintro ⟨h1, -⟩; exact hx (Fin.ext h1)
  · simp

open GlobalTheory.Grid (neg neg_gram) in
theorem gramAt_neg_of_gram_one {A : HSp D} (hg : A.gram = 1) (τ : D.what₂.Tau) : gramAt D (neg A) τ = -1 := by
  ext a b
  simp only [gramAt, neg_gram, hg, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp

open GlobalTheory.Grid (neg neg_gram sigOK_sgn isCartanInv_sgn) in

theorem exists_pair {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S}
    (h : X.Is ψ θ α β νH S) (hstd : X.rA.IsStd) (hA : A.SigOK) (h1 : 1 ≤ A.rank) (h1' : 1 ≤ A'.rank) (t : T) :
    ∃ (cA : CptF (neg A)) (a : GL (Fin (neg A).rank) (AE D)) (ν : Measure (WO (neg A) WW)) (𝓕 : Set (WO (neg A) WW)),
      Pair ψ θ (neg A) WW (β t) (β t / α t) (fun τ => -X.rA.s τ) X.rW.s A'.rank cA a ((X.ω t).toSgn true) ν 𝓕 := by
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (neg A) WW
  have hg := hstd.1
  have hgn : ∀ τ, gramAt D (neg A) τ = -1 := gramAt_neg_of_gram_one hg
  have hs : ∀ τ, X.rA.s τ = 1 := fun τ => (hstd.2.2 τ).1
  refine ⟨negFrame A, 1, ν, 𝓕, ⟨⟨h1, h1', ?_, h.isVac.2.inf, sigOK_sgn true hA, fun τ => ?_,
    fun τ => isCartanInv_sgn true _ τ (h.rigA.2.2 τ).1, fun τ => (h.rigW.2.2 τ).1, fun τ => ?_⟩, ?_, fun τ => ?_, h.weil t, hν⟩⟩
  · exact h.rank.symm
  · rw [Matrix.mul_assoc, jpq_mul_negFrame, Matrix.mul_neg, negFrame_conj_mul A hg hA, hgn]
  · show negFrame A τ * -X.rA.s τ = _
    rw [hs, jpq_mul_negFrame, Matrix.mul_neg, Matrix.mul_one]
  · intro w
    refine ⟨fun _ => false, ?_⟩
    simp only [JR, neg_gram, hg]
    ext i j
    simp [Formalism.UG.cT, Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  · rw [hgn, hs]
    simp [compAt]

open GlobalTheory.Grid (neg) in

theorem one_le_bot (i j : Fin D.R.m) : 1 ≤ botBig D i j ∧ 1 ≤ botSmall D i j := by
  obtain ⟨u, hu⟩ := D.R.t_odd
  have h2 : D.R.m ≤ D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hr : Odd D.R.r := by
    have := GlobalTheory.ChiGrid.odd_sLen D
    simp only [GlobalTheory.ChiGrid.sLen] at this
    exact (Nat.odd_add.1 this).2 (by decide)
  obtain ⟨w, hw⟩ := hr
  have hi := i.2
  have hj := j.2
  simp only [botBig, botSmall, rankV, GlobalTheory.ChiGrid.sLen]
  constructor <;> omega

end GlobalTheory.BottomPairData

open GlobalTheory.BottomPairData in

theorem GlobalTheory.BottomPairData.pair_data : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T, ∃ (cA : CptF (GlobalTheory.Grid.neg A)) (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW)), Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j) (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) (fun τ => -X.rA.s τ) X.rW.s A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X hX hA t
  have hb := one_le_bot (D := D) i j
  exact exists_pair X (GlobalTheory.BottomIPData.isBottomTri_is hX) hX.std hA (hX.rank ▸ hb.1) (hX.rank' ▸ hb.2) t

end
