import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbLem

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

set_option maxHeartbeats 4000000 in

theorem packK (hBO : BlockOperatorsProductAdjoint) {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E)
    (W₁ : Submodule ℂ (Kinf E B.a → ℂ)) (W₂ : Submodule ℂ (Kinf E B.b → ℂ))
    (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E))))
    (hP : PackAt E B.a B.b B.Ma B.Mb W₁ W₂)
    {Γ : Type} (g : Γ → BGen B) (t₀ : PT B) (bump : ℝ → ℝ) (cK : ℂ)
    (der : InfinitePlace E → Bool → ℕ → Γ × Γ) (ht₀ : t₀.Ok) (hbump : IsBump bump t₀.T)
    (hka0 : ∀ v, IsKer B.μa (B.Ma v) [] bump (t₀.ka v)) (hkb0 : ∀ v, IsKer B.μb (B.Mb v) [] bump (t₀.kb v))
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (hderA : ∀ v s m, 1 ≤ m → 0 < B.a → ∃ ta : PT B, g (der v s m).1 = Sum.inr ta ∧
      ArchType t₀ ta ∧ ta.kb = t₀.kb ∧ IsKer B.μa (B.Ma v) [(s, m)] bump (ta.ka v) ∧ (∀ v', v' ≠ v → ta.ka v' = t₀.ka v'))
    (hderB : ∀ v s m, 1 ≤ m → 0 < B.b → ∃ tb : PT B, g (der v s m).2 = Sum.inr tb ∧
      ArchType t₀ tb ∧ tb.ka = t₀.ka ∧ IsKer B.μb (B.Mb v) [(s, m)] bump (tb.kb v) ∧ (∀ v', v' ≠ v → tb.kb v' = t₀.kb v'))
    (M : ℕ) (f : B.I → H E B.a B.b → ℂ) (c : ℂ) (σ : Γ → ℂ) (hf : ∀ i, Continuous (f i)) (hf0 : f ≠ 0)
    (hLI : LeftInv f) (hW : WL2 B.D M f) (hc : c ≠ 0) (h0 : PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ f = c • f)
    (hAt : ∀ y (t : PT B), g y = Sum.inr t → PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ f = σ y • f) :
    ∃ (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b),
      (∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m =
        (if 1 ≤ m ∧ 0 < B.a then σ (der v s m).1 else if m = 0 then (B.a : ℂ) * c else 0) / c) ∧
      (∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m =
        (if 1 ≤ m ∧ 0 < B.b then σ (der v s m).2 else if m = 0 then (B.b : ℂ) * c else 0) / c) ∧
      EigAll χa χb f ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) ∧
      (∀ i m₂, ∃ φ : Sm E B.a, φ.1 = fun x => f i (x, m₂)) ∧ (∀ i m₁, ∃ φ : Sm E B.b, φ.1 = fun x => f i (m₁, x)) ∧
      (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
      (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
      ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ) := by
  haveI := B.ha
  haveI := B.hb
  haveI := B.hν
  haveI : BorelSpace (G B.a) := ⟨rfl⟩
  haveI : BorelSpace (G B.b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  choose ta hta using hderA
  choose tb htb using hderB
  let ka' : Bool → ℕ → Kers B.Ma := fun s m v =>
    if h : 1 ≤ m ∧ 0 < B.a then (ta v s m h.1 h.2).ka v else if m = 0 then (B.a : ℂ) • t₀.ka v else 0
  let kb' : Bool → ℕ → Kers B.Mb := fun s m v =>
    if h : 1 ≤ m ∧ 0 < B.b then (tb v s m h.1 h.2).kb v else if m = 0 then (B.b : ℂ) • t₀.kb v else 0
  let ca : InfinitePlace E → Bool → ℕ → ℂ := fun v s m =>
    if 1 ≤ m ∧ 0 < B.a then σ (der v s m).1 else if m = 0 then (B.a : ℂ) * c else 0
  let cb : InfinitePlace E → Bool → ℕ → ℂ := fun v s m =>
    if 1 ≤ m ∧ 0 < B.b then σ (der v s m).2 else if m = 0 then (B.b : ℂ) * c else 0
  have hkerA : ∀ s m v, IsKer B.μa (B.Ma v) [(s, m)] bump (ka' s m v) := by
    intro s m v
    by_cases h : 1 ≤ m ∧ 0 < B.a
    · have e1 : ka' s m v = (ta v s m h.1 h.2).ka v := dif_pos h
      rw [e1]; exact (hta v s m h.1 h.2).2.2.2.1
    · by_cases hm : m = 0
      · have e1 : ka' s m v = (B.a : ℂ) • t₀.ka v := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dif_neg h, if_pos hm]
        rw [e1, hm]; exact isKer_smul_rank _ _ _ _ s (hka0 v)
      · have e1 : ka' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dif_neg h, if_neg hm]
        have ha : B.a = 0 := by omega
        rw [e1]; exact isKer_zero_rank ha _ _ _ s m
  have hkerB : ∀ s m v, IsKer B.μb (B.Mb v) [(s, m)] bump (kb' s m v) := by
    intro s m v
    by_cases h : 1 ≤ m ∧ 0 < B.b
    · have e1 : kb' s m v = (tb v s m h.1 h.2).kb v := dif_pos h
      rw [e1]; exact (htb v s m h.1 h.2).2.2.2.1
    · by_cases hm : m = 0
      · have e1 : kb' s m v = (B.b : ℂ) • t₀.kb v := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dif_neg h, if_pos hm]
        rw [e1, hm]; exact isKer_smul_rank _ _ _ _ s (hkb0 v)
      · have e1 : kb' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dif_neg h, if_neg hm]
        have hb : B.b = 0 := by omega
        rw [e1]; exact isKer_zero_rank hb _ _ _ s m
  have hderA' : ∀ v s m, PositivityTheory.Rg.BcB.E.conv B.D.μ (tens (Function.update t₀.ka v (ka' s m v)) t₀.kb t₀.ψ) f =
      ca v s m • f := by
    intro v s m
    by_cases h : 1 ≤ m ∧ 0 < B.a
    · have e1 : ka' s m v = (ta v s m h.1 h.2).ka v := dif_pos h
      have e2 : ca v s m = σ (der v s m).1 := if_pos h
      obtain ⟨h1, h3, h4, -, h5⟩ := hta v s m h.1 h.2
      have hu : Function.update t₀.ka v ((ta v s m h.1 h.2).ka v) = (ta v s m h.1 h.2).ka := by
        funext v'
        by_cases hv : v' = v
        · subst hv; simp
        · rw [Function.update_of_ne hv]; exact (h5 v' hv).symm
      rw [e1, e2, hu, ← h4, ← show (ta v s m h.1 h.2).ψ = t₀.ψ from h3]
      exact hAt _ _ h1
    · by_cases hm : m = 0
      · have e1 : ka' s m v = (B.a : ℂ) • t₀.ka v := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dif_neg h, if_pos hm]
        have e2 : ca v s m = (B.a : ℂ) * c := by
          show (if 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [if_neg h, if_pos hm]
        rw [e1, e2, tens_update_smul, conv_smulM, show tens t₀.ka t₀.kb t₀.ψ = t₀.Φ from rfl, h0, smul_smul]
      · have e1 : ka' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dif_neg h, if_neg hm]
        have e2 : ca v s m = 0 := by
          show (if 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [if_neg h, if_neg hm]
        rw [e1, e2, tens_update_zero, conv_zeroM, zero_smul]
  have hderB' : ∀ v s m, PositivityTheory.Rg.BcB.E.conv B.D.μ (tens t₀.ka (Function.update t₀.kb v (kb' s m v)) t₀.ψ) f =
      cb v s m • f := by
    intro v s m
    by_cases h : 1 ≤ m ∧ 0 < B.b
    · have e1 : kb' s m v = (tb v s m h.1 h.2).kb v := dif_pos h
      have e2 : cb v s m = σ (der v s m).2 := if_pos h
      obtain ⟨h1, h3, h4, -, h5⟩ := htb v s m h.1 h.2
      have hu : Function.update t₀.kb v ((tb v s m h.1 h.2).kb v) = (tb v s m h.1 h.2).kb := by
        funext v'
        by_cases hv : v' = v
        · subst hv; simp
        · rw [Function.update_of_ne hv]; exact (h5 v' hv).symm
      rw [e1, e2, hu, ← h4, ← show (tb v s m h.1 h.2).ψ = t₀.ψ from h3]
      exact hAt _ _ h1
    · by_cases hm : m = 0
      · have e1 : kb' s m v = (B.b : ℂ) • t₀.kb v := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dif_neg h, if_pos hm]
        have e2 : cb v s m = (B.b : ℂ) * c := by
          show (if 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [if_neg h, if_pos hm]
        rw [e1, e2, tens_update_smul_b, conv_smulM, show tens t₀.ka t₀.kb t₀.ψ = t₀.Φ from rfl, h0, smul_smul]
      · have e1 : kb' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dif_neg h, if_neg hm]
        have e2 : cb v s m = 0 := by
          show (if 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [if_neg h, if_neg hm]
        rw [e1, e2, tens_update_zero_b, conv_zeroM, zero_smul]
  have hψl : ∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, t₀.ψ x y ((u₁, u₂) * h) = t₀.ψ x y h := by
    intro x y u₁ hu₁ u₂ hu₂ h
    have hu : ((u₁, u₂) : Hf E B.a B.b) ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) := Subgroup.mem_prod.2 ⟨hu₁, hu₂⟩
    rw [hψ₀, hψ₀]
    simp only [Subgroup.mul_mem_cancel_left _ hu]
  exact hP B.D B.μa B.μb B.ν B.κ t₀.ka t₀.kb t₀.va t₀.vb t₀.T t₀.ψ bump ka' kb' K₁ K₂ M
    f c ca cb B.compat ht₀.ka ht₀.kb ht₀.ψ hbump hka0 hkb0 hkerA hkerB o₁ o₂
    hψl hf hf0 hLI hW hc h0 hderA' hderB'

end PositivityTheory.Rg.BcB.F.Rd.B

end
