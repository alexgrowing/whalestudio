import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
import Development.WeilBound.ThetaLifts.SphericalLattices.ThetaSubSup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianTransform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianIdentity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.relStable :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → Stable (opFin om v) (relFin om v) := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL g hg x hx
  obtain ⟨h, hh, hact⟩ := hg
  have h1X : (1 : UA σ X.J) ∈ UAt σ X ⇑(evFin F v) := by
    show At _ (mat (1 : UA σ X.J) - 1)
    intro u _
    rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, smul_zero]
  have h1W : (1 : UA σ W.J) ∈ UAt σ W ⇑(evFin F v) := by
    show At _ (mat (1 : UA σ W.J) - 1)
    intro u _
    rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]
  have hgx : ((g x : SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) = ω (1, h) (x : (Fin n × Fin d → Fv F v) → ℂ) :=
    (hL.acts 1 h1X h hh x x.2 _).1 (hact x)
  have key : augAt om v ≤ (augAt om v).comap (ω (1, h)) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g', hg', φ, hφ, φ₁, hφ₁, hA, rfl⟩
    have e1 : φ₁ = ω (g', 1) φ := (hL.acts g' hg' 1 h1W φ hφ φ₁).1 hA
    subst e1
    have m1 := hL.mul 1 h1X h hh g' hg' 1 h1W φ hφ
    have m2 := hL.mul g' hg' 1 h1W 1 h1X h hh φ hφ
    simp only [one_mul, mul_one] at m1 m2
    have hp : ω (1, h) φ ∈ SB (Fin n × Fin d → Fv F v) := hL.pres 1 h1X h hh φ hφ
    simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub]
    rw [← m1, m2]
    exact Submodule.subset_span ⟨g', hg', ω (1, h) φ, hp, ω (g', 1) (ω (1, h) φ),
      hL.pres g' hg' 1 h1W _ hp, (hL.acts g' hg' 1 h1W _ hp _).2 rfl, rfl⟩
  have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v := hx
  show ((g x : SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v
  rw [hgx]
  exact key hx'
