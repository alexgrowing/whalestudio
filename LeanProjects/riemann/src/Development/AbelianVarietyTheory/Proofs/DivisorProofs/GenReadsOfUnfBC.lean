import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem genReads_of_unfBC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r g : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((U (σ'.comp (incF c c' hle))).X k).Λ)
    (idx : Fin g ≃ ((U (σ'.comp (incF c c' hle))).X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (x : ((U (σ'.comp (incF c c' hle))).X k).dom) (ϑ : (Fin g → ℂ) → ℂ)
    (h : GenReads (unfBC hle U σ') k bas idx e x ϑ) : GenReads (U (σ'.comp (incF c c' hle))) k bas idx e x ϑ := by
  obtain ⟨B, hB⟩ := h
  letI : Algebra c.F ℂ := (σ'.comp (incF c c' hle)).toAlgebra
  letI : Algebra c'.F ℂ := σ'.toAlgebra
  exact ⟨⟨B.ex, B.ex_add, B.ex_onto, B.ex_ker, B.ex_lin, B.hol, B.der, B.fr, B.fr_hol, B.fr_ne, B.fr_g, B.fr_0, B.χ,
    B.χ_norm, B.fr_per⟩, hB⟩

theorem CcIs.unfBC {D : D7} (θ : InfFam D) (V W : HSp D) {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ)
    (dict : GA D W → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D W → ℂ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ)
    (h : CcIs θ V W hr (U (σ'.comp (incF c c' hle))) dict mu x₀ om f₀ cc) :
    CcIs θ V W hr (Formalism.L2.Pj.unfBC hle U σ') dict mu x₀ om f₀ cc := by
  refine ⟨h.1, fun a γ hA hx' g bas idx e hs hi ϑ hϑ w hw => ?_⟩
  have hrel : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  have hi' : IdxIs c (σ'.comp (incF c c' hle)) ((U (σ'.comp (incF c c' hle))).X (dict a).1) idx e := by
    unfold IdxIs at hi ⊢
    rw [hrel] at hi
    exact hi
  exact h.2 a γ hA hx' g bas idx e hs hi' ϑ (genReads_of_unfBC hle U σ' _ bas idx e ⟨_, hx'⟩ ϑ hϑ) w hw

theorem ccIs_extend_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O _ cc h
  exact CcIs.unfBC _ _ _ _ O.hle (T.U ((i : ℕ) + 1)) (inC O.c') _ _ _ _ _ _ h

end GlobalTheory.AdTh
