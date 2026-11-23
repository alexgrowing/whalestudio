import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E
open scoped ENNReal Pointwise

namespace PositivityTheory.Rg.BcB.E1

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem proper_ratH (h : RatProper) (C : Set (H E a b)) (hC : IsCompact C) : {γ : ratH E a b | (γ : H E a b) ∈ C}.Finite := by
  have h1 := (h E a).2.2 _ (hC.image continuous_fst)
  have h2 := (h E b).2.2 _ (hC.image continuous_snd)
  refine ((h1.prod h2).image ((ratGL E a).prodMap (ratGL E b)).rangeRestrict).subset ?_
  rintro ⟨_, γ, rfl⟩ hγ
  exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩

def ctx (h : RatProper) (D : Dom E a b) : Ctx :=
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.t2Space_GA E b
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E b
  haveI := (h E a).2.1
  haveI := (h E b).2.1
  haveI := D.haar.1
  haveI := D.haar.2.2.1
  haveI := D.haar.2.2.2
  { G := H E a b
    ms := borelH E a b
    bs := ⟨rfl⟩
    μ := D.μ
    haar := {}
    Γ := ratH E a b
    cn := (((ratGL E a).prodMap (ratGL E b)).rangeRestrict_surjective).countable
    proper := proper_ratH h
    F := D.F
    fd := D.fd }

theorem ctx_ker (h : RatProper) (D : Dom E a b) (φ : H E a b → ℂ) : ker (ctx h D).Γ φ = kerH φ := rfl

theorem ctx_isOp (h : RatProper) (D : Dom E a b) {ι : Type} [Fintype ι] (Φ : Matrix ι ι (H E a b → ℂ))
    (T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) : (ctx h D).IsOp Φ T ↔ IsROp D Φ T := Iff.rfl

theorem wt_eq (x : H E a b) : wt x = 1 + red x.1 + red x.2 := rfl

def th (x : H E a b) : H E a b := (thetaA E a x.1, thetaA E b x.2)

def CntPair : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ),
  (∀ (Ω : Set (H E a b)) x, cnt (ratH E a b) Ω (th x) = cnt (ratH E a b) (th '' Ω) x) ∧
  Continuous (th : H E a b → H E a b) ∧ ∀ (φ : H E a b → ℂ) x y, kerTw2 φ x y = kerH φ x (th y)

def WtCount : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (Ω : Set (H E a b)),
  IsCompact Ω → ∀ M : ℕ, 2 * (a + b) ≤ M →
    ∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * M : ℤ))) * cnt (ratH E a b) Ω x ∂D.ν ≠ ⊤

def CutCount : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (Ω : Set (H E a b)),
  IsCompact Ω → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
    ∫⁻ x, (cutSet E a τ ×ˢ cutSet E b τ).indicator (cnt (ratH E a b) Ω) x ∂D.ν ≤ ENNReal.ofReal (C * (1 + τ) ^ N)

def WtDiag : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (φ : H E a b → ℂ),
  IsTestH φ → ∀ M : ℕ, 2 * (a + b) ≤ M → ∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * M : ℤ))) * ‖kerH φ x x‖ₑ ∂D.ν < ⊤

def SB : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)) (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ),
  IsTestM Φ₁ → IsTestM Φ₂ → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → ∃ (C : ℝ) (N : ℕ), ∀ (τ : ℝ)
    (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E a b → ℂ)), 0 ≤ τ → IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) →
    ‖∫ x, chiT τ x.1 * chiT τ x.2 * kerTw2 (fun y => ∑ i, ∑ j, Φ i j y * M j i) x x ∂D.ν‖ ≤ C * (1 + τ) ^ N * ‖U‖

def ProdDom : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)]
  (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure] (F₁ : Set (GA E a))
  (F₂ : Set (GA E b)), IsFundamentalDomain (ratGL E a).range F₁ μ₁ → IsFundamentalDomain (ratGL E b).range F₂ μ₂ →
  ∃ D : Dom E a b, D.F = F₁ ×ˢ F₂ ∧ ∀ f : GA E a × GA E b → ℂ,
    ∫ x, f x ∂D.ν = @integral _ _ _ _ Prod.instMeasurableSpace ((μ₁.prod μ₂).restrict (F₁ ×ˢ F₂)) f

end PositivityTheory.Rg.BcB.E1

end
