import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnalyticFrameOfAnalyticFibre
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormalisedPullbackMulNReadsThetaStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SymmetricLiftOddOrderActsAsTranslationStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfIntegralGeneratorTraceEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem reads_isUUOver_isVtOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (N : ℕ), Odd N → ∀ θ, A.Reads 1 y.s θ → (∀ a₁ a₂ : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a₁ = (2 : ℕ) • u) → (∃ u ∈ L, (N ^ 2 : ℕ) • a₂ = (2 : ℕ) • u) → ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (A.ex (pv X idx x a₁)) (A.ex (pv X idx x a₂)) F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a₂)) (fock X bas idx x 1 (pv X idx x ((N : E) • a₁)) θ) ((N : ℂ) • z))) ∧ ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) → ∀ (t : (ptO Xo y.x) ⟶ Xo.univ.t.G) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t' => t' = A.ex (pv X idx x a)) y.s t F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a)) θ ((N : ℂ) • z)) := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL N hN θ hθ
  have hpv : ∀ (n : ℕ) (a : Fin r → E), pv X idx x ((n : E) • a) = (n : ℂ) • pv X idx x a := by
    intro n a
    rw [(hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.1]
    funext j
    simp
  have hfk : ∀ (φ : (Fin g → ℂ) → ℂ) (a : Fin r → E),
      Dict.fock X bas idx x (N ^ 2) (pv X idx x a) (fun z => φ ((N : ℂ) • z)) =
        fun z => Dict.fock X bas idx x 1 (pv X idx x ((N : E) • a)) φ ((N : ℂ) • z) := by
    intro φ a
    rw [hpv]
    exact (fock_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx 1 φ).2.2.1 N _
  obtain ⟨Φ, he, -, hlat, -, -, hrd, hf⟩ := GlobalTheory.Dict.AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hχ : ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 := fun a ha =>
    (GlobalTheory.AnVal.chi_eq_sign E H Dw l Xo c y g _ e Φ a ha).1
  have htw : ∀ α₀ α s₁, α₀.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ →
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α
        (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd (ptO Xo y.x) Xo.univ.t.G).left) →
      IsTwistPull Xo.univ.t.G Xo.univ.t.PP.L (mulT Xo.univ.t.G (ptO Xo y.x) N)
        (snd (ptO Xo y.x) Xo.univ.t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α y.s s₁ →
      A.Reads ((N : ℤ) ^ 2) s₁ (fun z => θ ((N : ℂ) • z)) := by
    intro α₀ α s₁ hg hn hc ht
    exact (hrd _ _ _).1
      (GlobalTheory.T.normalisedPullbackMulN_reads_theta _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr N α₀ α y.s s₁ θ hg hn hc ht ((hrd _ _ _).2 hθ))
  have hsy : ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) →
      ∀ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x),
      SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (A.ex (pv X idx x a)) U →
      ∀ (s s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (φ : (Fin g → ℂ) → ℂ),
      IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) U s s' →
      A.Reads ((N : ℤ) ^ 2) s (fun z => φ ((N : ℂ) • z)) →
      A.Reads ((N : ℤ) ^ 2) s'
        (fun z => Dict.fock X bas idx x 1 (pv X idx x ((N : E) • a)) φ ((N : ℂ) • z)) := by
    rintro a ⟨u, hu, hau⟩ U hU s s' φ hA hs'
    have h2 : ((N ^ 2 : ℕ) : ℂ) • pv X idx x a = (2 : ℂ) • pv X idx x u := by
      have h3 := hpv 2 u
      rw [← hpv, Nat.cast_smul_eq_nsmul, hau, ← Nat.cast_smul_eq_nsmul E, h3]
      norm_num
    rw [← he] at hU
    have h4 := GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hχ ((N : ℤ) ^ 2) (N ^ 2) U
      (pv X idx x a) (pv X idx x u) s s' _ hN.pow ((hlat _).2 ⟨u, hu, rfl⟩) h2 hU hA ((hrd _ _ _).2 hs')
    have h5 := hf (N ^ 2) (pv X idx x a) (fun z => φ ((N : ℂ) • z))
    rw [Nat.cast_pow, hfk] at h5
    rw [h5] at h4
    exact (hrd _ _ _).1 h4
  refine ⟨?_, ?_⟩
  · rintro a₁ a₂ h₁ h₂ F ⟨α₀, α, s₁, s₂, U₁, U₂, hg, hn, hc, ht, hU₁, hA₁, hU₂, hA₂⟩
    exact hsy a₂ h₂ U₂ hU₂ s₂ F _ hA₂ (hsy a₁ h₁ U₁ hU₁ s₁ s₂ _ hA₁ (htw α₀ α s₁ hg hn hc ht))
  · rintro a h t F ⟨t', α₀, α, s₁, U, -, rfl, hg, hn, hc, ht, hU, hA⟩
    exact hsy a h U hU s₁ F _ hA (htw α₀ α s₁ hg hn hc ht)

end GlobalTheory.Dict
