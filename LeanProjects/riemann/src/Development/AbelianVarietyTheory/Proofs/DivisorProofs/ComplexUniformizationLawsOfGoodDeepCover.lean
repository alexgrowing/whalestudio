import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinitionStatement
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.W0EqOfRtEq
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtMain

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop

namespace GlobalTheory.LawsDeep

theorem goodAt_of_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l l₂ : Level H) (b : ℕ) (hM : l₂.M = l.M * b) (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) (p : ℕ) (hp : p.Prime) :
    l₂.GoodAt p := by
  rw [GlobalTheory.HostProbe.goodAt_iff l₂ hp]
  intro k hk
  have hdvd : l.M ∣ p ^ k := ⟨b, by rw [← hk]; exact hM⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact (GlobalTheory.HostProbe.goodAt_iff l hp).1 (hl p hp) i hi

theorem levLaws (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (hT : LawsJ T) (hj : InR D j)
    (hG : Y.Good e o) : GlobalTheory.LevGeo.Laws D j Y.d.Xo₂ Y.d.c₂ Y.U Y.dict where
  inR := hj
  host := (GlobalTheory.LevGeo.laws_core D T j hT hj).host
  dat := (GlobalTheory.LevGeo.laws_core D T j hT hj).dat
  levA := hG.lev.2
  unf := hG.unf
  chiTriv := hG.chiTriv
  dictU := by
    intro σ hσ
    obtain ⟨th, hr, hth, hd⟩ := hG.dictU σ hσ
    refine ⟨Y.Kf, th, hr, ?_, hth, hd, hG.unit σ hσ⟩
    have h₁ := hG.lev.1
    unfold DeltaDat.IsLev at h₁
    have h₂ := hT.toLawsM.pins.2.1
    unfold Par.PinLevel at h₂
    rw [h₁.2.1, h₂.1]
    exact hG.levelK
  modelW := hG.modelW

theorem laws_deep : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ),
    LawsJ T → InR D j → Y.Good e o → Laws Y.U (xiR D) := by
  intro D T j Y e o hT hj hG
  have hM : Y.d.l₂.M = T.Q.l.M * Y.d.pd := by
    have h₁ := hG.lev.1
    unfold DeltaDat.IsLev at h₁
    exact h₁.2.1
  have hgood : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := fun p hp =>
    goodAt_of_mul T.Q.l Y.d.l₂ Y.d.pd hM (GlobalTheory.RecDict.level_good_and_sign D T.Q hT.toLawsM.pins).1 p hp
  exact (GlobalTheory.T.moduliLaws_of_principalLevel_fieldOfDefinition D j T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ Y.U Y.dict
    (levLaws D T j Y e o hT hj hG) hG.geo hgood).1

end GlobalTheory.LawsDeep
