import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.MkTauEmbInjective
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.CovTop.WtRead

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [mul_self_nonneg H.rt0.re]

theorem exists_of_places (D : D7) (τ : D.host.E →+* ℂ) :
    ∃ t, DV.tauEmb D t = τ ∨ conjEmb (DV.tauEmb D t) = τ := by
  have hb : Function.Bijective fun t => InfinitePlace.mk (DV.tauEmb D t) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨Formalism.L2.Geo.Rec.StarEmbeddingNorm.mk_tauEmb_injective D, (Formalism.L2.Geo.Rec.StarEmbeddingNorm.card_places D).symm⟩
  obtain ⟨t, ht⟩ := hb.2 (InfinitePlace.mk τ)
  refine ⟨t, ?_⟩
  rcases InfinitePlace.mk_eq_iff.1 ht with h | h
  · exact Or.inl h
  · right
    rw [← h]
    ext x
    simp [conjEmb, ComplexEmbedding.conjugate_coe_eq]

theorem tauEmb_bijective (D : D7) (Q : Par D) (hQ : Q.PinHost) :
    Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hQ.2.2.2 t⟩ : Psi Q.H)) := by
  refine ⟨fun s t h => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val h), fun τ => ?_⟩
  obtain ⟨t, h | h⟩ := exists_of_places D τ.1
  · exact ⟨t, Subtype.ext h⟩
  · exfalso
    have h1 : conjEmb (DV.tauEmb D t) (Q.H.rt : D.host.E) = (starRingEnd ℂ) Q.H.rt0 := by
      simp only [conjEmb, RingHom.coe_comp, Function.comp_apply, hQ.2.2.2 t]
    exact conj_cmHostRoot_ne_self Q.H (h1.symm.trans ((congrArg (fun σ : D.host.E →+* ℂ => σ (Q.H.rt : D.host.E)) h).trans τ.2))

def tauPsi (D : D7) (Q : Par D) (hQ : Q.PinHost) : D.what₂.Tau ≃ Psi Q.H :=
  Equiv.ofBijective _ (tauEmb_bijective D Q hQ)

@[simp] theorem tauPsi_val (D : D7) (Q : Par D) (hQ : Q.PinHost) (t : D.what₂.Tau) :
    (tauPsi D Q hQ t).1 = DV.tauEmb D t := rfl

theorem sigW_add (D : D7) (i : Fin D.R.m) :
    (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
  have := i.2
  unfold Ranks.sigW Ranks.r
  simp only
  omega

theorem laOf_big (D : D7) (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (t : D.what₂.Tau) (τ : Psi T.Q.H) (hτ : τ.1 = DV.tauEmb D t)
    (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)) (a : Fin (D.R.sigW ((i : ℕ) + 1)).1)
    (ha : (a : ℕ) = k) :
    laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n τ k = (κ.aP t a : ℤ) + ((κ.n / 2 : ℕ) : ℤ) := by
  have hD := hT.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hk : (k : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p := by have := hD.1; have := a.2; omega
  simp only [laOf, weightOf, if_pos hk, hτ]
  rw [GlobalTheory.WeightExponents.wtA_tauEmb hT.pins.1, Formalism.L2.Pj.ext0, dif_pos (by omega)]
  have : (⟨(k : ℕ), by omega⟩ : Fin (D.R.sigW ((i : ℕ) + 1)).1) = a := Fin.ext ha.symm
  rw [this]

theorem laOf_small (D : D7) (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (t : D.what₂.Tau) (τ : Psi T.Q.H) (hτ : τ.1 = DV.tauEmb D t)
    (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)) (a : Fin (D.R.sigW ((i : ℕ) + 1)).2)
    (ha : (a : ℕ) + k + 1 = D.R.r) :
    laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n τ k = -(κ.aM t a : ℤ) - ((κ.n / 2 : ℕ) : ℤ) := by
  have hD := hT.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hs := sigW_add D i
  have hp := hD.1
  have hq := hD.2.1
  have hk : ¬ (k : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p := by omega
  simp only [laOf, weightOf, if_neg hk, hτ]
  rw [GlobalTheory.Shares.WtDic.wtA_conj, Formalism.L2.Pj.ext0, dif_pos (by omega)]
  have : (⟨(T.Q.Dw ((i : ℕ) + 1)).q - 1 - ((k : ℕ) - (T.Q.Dw ((i : ℕ) + 1)).p), by omega⟩ :
      Fin (D.R.sigW ((i : ℕ) + 1)).2) = a := Fin.ext (by simp only; omega)
  rw [this]

theorem main : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 ∧ (T.Q.Dw ((i : ℕ) + 1)).q = (D.R.sigW ((i : ℕ) + 1)).2 ∧ Nat.card (Psi T.Q.H) = D.R.f ∧ dimFlag (T.Q.Dw ((i : ℕ) + 1)) = D.R.f * D.R.r.choose 2 ∧ Dom (wtA κ) κ.n ∧ ∃ e : D.what₂.Tau ≃ Psi T.Q.H, (∀ t, (e t).1 = DV.tauEmb D t) ∧ ∀ t (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)), (∀ a : Fin (D.R.sigW ((i : ℕ) + 1)).1, (a : ℕ) = k → laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n (e t) k = (κ.aP t a : ℤ) + ((κ.n / 2 : ℕ) : ℤ)) ∧ (∀ a : Fin (D.R.sigW ((i : ℕ) + 1)).2, (a : ℕ) + k + 1 = D.R.r → |laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n (e t) k + (κ.aM t a : ℤ)| ≤ (κ.n : ℤ)) := by
  intro D T hT i κ
  have hP := hT.pins
  have hD := hP.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hs := sigW_add D i
  have hcard : Fintype.card (Psi T.Q.H) = D.R.f :=
    (Fintype.card_congr (tauPsi D T.Q hP.1)).symm.trans (Formalism.MainNotions.Lnk.card_Tau D)
  refine ⟨hD.1, hD.2.1, ?_, ?_, Formalism.L2.Pj.dom_wtA κ, tauPsi D T.Q hP.1, fun t => rfl, fun t k => ⟨?_, ?_⟩⟩
  · rw [Nat.card_eq_fintype_card, hcard]
  · rw [dimFlag, Formalism.DegreeFormula.dimFl, hcard, hD.1, hD.2.1, hs, Nat.choose_two_right]
  · exact fun a ha => laOf_big D T hT i κ t _ rfl k a ha
  · intro a ha
    rw [laOf_small D T hT i κ t _ rfl k a ha]
    have h0 : (0 : ℤ) ≤ ((κ.n / 2 : ℕ) : ℤ) := Int.natCast_nonneg _
    have h1 : ((κ.n / 2 : ℕ) : ℤ) ≤ (κ.n : ℤ) := by exact_mod_cast Nat.div_le_self _ _
    rw [show -(κ.aM t a : ℤ) - ((κ.n / 2 : ℕ) : ℤ) + (κ.aM t a : ℤ) = -((κ.n / 2 : ℕ) : ℤ) by ring, abs_neg,
      abs_of_nonneg h0]
    exact h1

end GlobalTheory.CovTop.WtRead

end
