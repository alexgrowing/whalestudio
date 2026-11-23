import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PackK

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

set_option maxHeartbeats 4000000 in
theorem perK (hAV : ActVal) (hBO : BlockOperatorsProductAdjoint) (hCM : ConvMulSt) (hFin : FinSt) (hReal : RealiseSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E)
    (W₁ : Submodule ℂ (Kinf E B.a → ℂ)) (W₂ : Submodule ℂ (Kinf E B.b → ℂ))
    (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (c₁ : IsCompact (K₁ : Set (GL (Fin B.a) (Af E))))
    (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E)))) (c₂ : IsCompact (K₂ : Set (GL (Fin B.b) (Af E))))
    (hP : PackAt E B.a B.b B.Ma B.Mb W₁ W₂)
    (Γ : Type) [Countable Γ] (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (bump : ℝ → ℝ) (cK : ℂ)
    (der : InfinitePlace E → Bool → ℕ → Γ × Γ) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (jX : ℕ) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ)
    (hok : ∀ x, (g x).Ok) (htX : tX.Ok) (hXe : X = tX.op) (hjX : ∀ χa' χb', tX.val χa' χb' = t₀.val χa' χb' ^ jX)
    (ha₀ : g a₀ = Sum.inr t₀) (hbump : IsBump bump t₀.T)
    (hka0 : ∀ v, IsKer B.μa (B.Ma v) [] bump (t₀.ka v)) (hkb0 : ∀ v, IsKer B.μb (B.Mb v) [] bump (t₀.kb v))
    (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (hderA : ∀ v s m, 1 ≤ m → 0 < B.a → ∃ ta : PT B, g (der v s m).1 = Sum.inr ta ∧
      ArchType t₀ ta ∧ ta.kb = t₀.kb ∧ IsKer B.μa (B.Ma v) [(s, m)] bump (ta.ka v) ∧ (∀ v', v' ≠ v → ta.ka v' = t₀.ka v'))
    (hderB : ∀ v s m, 1 ≤ m → 0 < B.b → ∃ tb : PT B, g (der v s m).2 = Sum.inr tb ∧
      ArchType t₀ tb ∧ tb.ka = t₀.ka ∧ IsKer B.μb (B.Mb v) [(s, m)] bump (tb.kb v) ∧ (∀ v', v' ≠ v → tb.kb v' = t₀.kb v'))
    (hcomm : ∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op))
    (hXc : ∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) (hXs : IsSelfAdjoint X)
    (hχn : ∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) (hχ0 : χ (genE g X a₀) ≠ 0) :
    PerKOut B W₁ W₂ K₁ K₂ g a₀ t₀ der X tX jX χ := by
  haveI := B.ha
  haveI := B.hb
  haveI := B.hν
  haveI : BorelSpace (G B.a) := ⟨rfl⟩
  haveI : BorelSpace (G B.b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  have okOf : ∀ y (t : PT B), g y = Sum.inr t → t.Ok := fun y t hy => by
    have := hok y; rw [hy] at this; exact this
  have ht₀ : t₀.Ok := okOf a₀ t₀ ha₀
  obtain ⟨M, sk, f, hsg, hsX, hk⟩ := hReal E B Γ g a₀ t₀ X tX χ hok htX hXe ha₀ hcomm hXc hXs hχn hχ0
  have hc : ∀ k, sk k (genE g X a₀) ≠ 0 := fun k => (hk k).1
  have hcont : ∀ k i, Continuous (f k i) := fun k => (hk k).2.1
  have hne : ∀ k, f k ≠ 0 := fun k => (hk k).2.2.1
  have heq0 : ∀ k, PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ (f k) = sk k (genE g X a₀) • f k := fun k => (hk k).2.2.2.2.2.1
  have hAt : ∀ k y (t : PT B), g y = Sum.inr t → PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ (f k) = sk k (genE g X y) • f k := by
    intro k y t hy
    have htok := okOf y t hy
    have e := hCM E B.a B.b B.D B.I t.Φ t₀.Φ (hBO E B t t htok htok).1 (hBO E B t₀ t₀ ht₀ ht₀).1 (f k) (hcont k)
    rw [(hk k).2.2.2.2.2.2.1 y t hy, heq0 k, conv_smul] at e
    have e2 : sk k (genE g X a₀) • PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ (f k) =
        sk k (genE g X a₀) • (sk k (genE g X y) • f k) := by
      rw [← e, smul_smul, mul_comm]
    exact smul_right_injective _ (hc k) e2
  have hAX : ∀ k, PositivityTheory.Rg.BcB.E.conv B.D.μ tX.Φ (f k) = sk k (XE g X) • f k := by
    intro k
    have e := hCM E B.a B.b B.D B.I tX.Φ t₀.Φ (hBO E B tX tX htX htX).1 (hBO E B t₀ t₀ ht₀ ht₀).1 (f k) (hcont k)
    rw [(hk k).2.2.2.2.2.2.2, heq0 k, conv_smul] at e
    have e2 : sk k (genE g X a₀) • PositivityTheory.Rg.BcB.E.conv B.D.μ tX.Φ (f k) =
        sk k (genE g X a₀) • (sk k (XE g X) • f k) := by
      rw [← e, smul_smul, mul_comm]
    exact smul_right_injective _ (hc k) e2
  have hPk := fun k => packK hBO B W₁ W₂ K₁ K₂ o₁ o₂ hP g t₀ bump cK der ht₀ hbump hka0 hkb0 hψ₀ hderA hderB M (f k)
    (sk k (genE g X a₀)) (fun y => sk k (genE g X y)) (hcont k) (hne k) (hk k).2.2.2.1 (hk k).2.2.2.2.1 (hc k) (heq0 k)
    (hAt k)
  choose χak χbk hgA hgB hEig hTy hS₁ hS₂ hAu₁ hAu₂ hI₁ hI₂ using hPk
  obtain ⟨hFinA, -⟩ := hFin E B K₁ K₂ o₁ c₁ o₂ c₂ cK t₀.ψ hcK hψ₀
  have hrinv : ∀ k, ∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f k i (x * finH u) = f k i x := by
    intro k i u hu x
    exact (hTy k i).1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  have hidk : ∀ k, convF B.ν t₀.ψ (f k) = f k := fun k => (hFinA _ (f k) (hrinv k)).1
  have hAVt : ∀ k (t : PT B), t.Ok → PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ (f k) =
      t.val (χak k) (χbk k) • convF B.ν t.ψ (f k) := by
    intro k t htok
    exact hAV E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t₀.ka t.ka t₀.kb t.kb t₀.va t.va t₀.vb t.vb t₀.T t.T t₀.ψ t.ψ
      (f k) (χak k) (χbk k) B.compat ht₀.ka ht₀.kb ht₀.ψ ⟨hcont k, _, hc k, heq0 k⟩ ⟨hS₁ k, hS₂ k⟩ (hEig k) htok.ka
      htok.kb htok.ψ
  have hv₀ : ∀ k, t₀.val (χak k) (χbk k) = sk k (genE g X a₀) := by
    intro k
    have e := hAVt k t₀ ht₀
    rw [hidk k, heq0 k] at e
    exact (smul_cancel (hne k) e).symm
  have hFinK : ∀ k y (t : PT B), g y = Sum.inr t → FinType t₀ t →
      convF B.ν t.ψ (f k) = (sk k (genE g X y) / sk k (genE g X a₀)) • f k := by
    intro k y t hy hft
    have htok := okOf y t hy
    have hv : t.val (χak k) (χbk k) = sk k (genE g X a₀) := by
      rw [← hv₀ k]; unfold PT.val; rw [hft.2.2.1, hft.2.2.2.1]
    have e := hAVt k t htok
    rw [hAt k y t hy, hv] at e
    refine smul_right_injective _ (hc k) ?_
    show sk k (genE g X a₀) • _ = sk k (genE g X a₀) • _
    rw [← e, smul_smul]
    congr 1
    field_simp [hc k]
  have hXK : ∀ k, convF B.ν tX.ψ (f k) = (sk k (XE g X) / sk k (genE g X a₀) ^ jX) • f k := by
    intro k
    have e := hAVt k tX htX
    rw [hAX k, hjX, hv₀ k] at e
    have hcj : sk k (genE g X a₀) ^ jX ≠ 0 := pow_ne_zero _ (hc k)
    refine smul_right_injective _ hcj ?_
    show sk k (genE g X a₀) ^ jX • _ = sk k (genE g X a₀) ^ jX • _
    rw [← e, smul_smul]
    congr 1
    field_simp [hcj]
  have hArchK : ∀ k y (t : PT B), g y = Sum.inr t → ArchType t₀ t → t.val (χak k) (χbk k) = sk k (genE g X y) := by
    intro k y t hy hat
    have e := hAVt k t (okOf y t hy)
    rw [hAt k y t hy, show t.ψ = t₀.ψ from hat, hidk k] at e
    exact (smul_cancel (hne k) e).symm
  have hlimA : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χak k v s) m) atTop
      (𝓝 (if 1 ≤ m ∧ 0 < B.a then χ (genE g X (der v s m).1) / χ (genE g X a₀) else if m = 0 then (B.a : ℂ) else 0)) := by
    intro v s m
    refine Tendsto.congr (fun k => (hgA k v s m).symm) ?_
    by_cases h : 1 ≤ m ∧ 0 < B.a
    · simp only [if_pos h]
      exact (hsg _).div (hsg a₀) hχ0
    · by_cases hm : m = 0
      · simp only [if_neg h, if_pos hm]
        refine tendsto_const_nhds.congr (fun k => ?_)
        field_simp [hc k]
      · simp only [if_neg h, if_neg hm, zero_div]
        exact tendsto_const_nhds
  have hlimB : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χbk k v s) m) atTop
      (𝓝 (if 1 ≤ m ∧ 0 < B.b then χ (genE g X (der v s m).2) / χ (genE g X a₀) else if m = 0 then (B.b : ℂ) else 0)) := by
    intro v s m
    refine Tendsto.congr (fun k => (hgB k v s m).symm) ?_
    by_cases h : 1 ≤ m ∧ 0 < B.b
    · simp only [if_pos h]
      exact (hsg _).div (hsg a₀) hχ0
    · by_cases hm : m = 0
      · simp only [if_neg h, if_pos hm]
        refine tendsto_const_nhds.congr (fun k => ?_)
        field_simp [hc k]
      · simp only [if_neg h, if_neg hm, zero_div]
        exact tendsto_const_nhds
  exact ⟨M, sk, f, χak, χbk, hsg, hsX, hlimA, hlimB, fun k => ⟨hc k, hcont k, hne k, (hk k).2.2.2.1,
    (hk k).2.2.2.2.1, hTy k, hS₁ k, hS₂ k, hAu₁ k, hAu₂ k, hI₁ k, hI₂ k, hFinK k, hXK k, hArchK k⟩⟩

end PositivityTheory.Rg.BcB.F.Rd.B

end
