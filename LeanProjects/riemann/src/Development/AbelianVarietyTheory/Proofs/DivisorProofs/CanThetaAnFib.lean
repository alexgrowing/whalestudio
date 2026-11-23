import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

set_option maxHeartbeats 1000000 in

theorem canTheta_anFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (Wt : UW U) (k : U.Comp) (bas : (Fin Wt.g ⊕ Fin Wt.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin Wt.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (Wt.e j).1) (Wt.e j).2) → (∀ j, rowType (U.X k) (idx j) = relab c σ (Wt.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → ∀ Pm : (Wt.F.Di (Wt.ik k)).La →+ (Fin Wt.g → ℂ), (∀ a j, Pm a j = perFr (U.X k) x.1 (Wt.φ k a : Fin r → E) (relab c σ (Wt.e j).1) (Wt.e j).2) → (∃ Hm θ, GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsCanTheta Wt.F (Wt.ik k) Pm (U.un k x) Hm θ) ∧ ∀ Hm θ, GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsCanTheta Wt.F (Wt.ik k) Pm (U.un k x) Hm θ → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx Wt.e x.1 (U.X k).Λ (unC U k x), A.Marked (Wt.mark k) ∧ A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ ∧ ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr W k bas idx hb hper hty x hx1 Pm' hPm'
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨-, -, -, -, -, hspan, hEF⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr W k
  obtain ⟨-, -, -, -, hsm, -, huniq, -⟩ := GlobalTheory.Dict.hx_laws E r (U.X k) W.g bas idx 0 hb (by simp) x.1 x.2
  obtain ⟨Pm, hPm, hP, hu, hder, hrest⟩ := W.pt k x
  obtain rfl : Pm' = Pm := AddMonoidHom.ext fun a => funext fun j => (hPm' a j).trans (hPm a j).symm
  obtain ⟨Hm, χl, fr, θ, Fd, hH, hpos, hIm, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrest hx1
  have hcan : GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsCanTheta W.F (W.ik k) Pm' (U.un k x) Hm θ :=
    ⟨hH, hpos, hIm, χl, fr, h1, h2, h3, h4, h5, h6⟩
  refine ⟨⟨Hm, θ, hcan⟩, fun Hm' θ' hcan' => ?_⟩
  obtain ⟨rfl, rfl⟩ : Hm = Hm' ∧ θ = θ' :=
    GlobalTheory.TwistFactorCompare.isCanTheta_unique (F := W.F) (k := W.ik k) (Pm := Pm') (y := U.un k x)
      ⟨hP, hu, hcan⟩ ⟨hP, hu, hcan'⟩
  obtain ⟨ex, hl, e1, e2, e3, e4, e5⟩ := exists_ex_transport W.F (W.ik k) Pm' hP (unC U k x).x hu
  have hpv : ∀ a, Pm' a = pv (U.X k) idx x.1 (W.emb k a) := fun a => by
    funext j
    rw [hPm, hper]
    rfl
  have hsurj : ∀ v ∈ (U.X k).Λ, ∃ a, W.emb k a = v := fun v hv =>
    ⟨(W.φ k).symm ⟨v, hv⟩, by simp [UW.emb]⟩
  have hmem : ∀ a, W.emb k a ∈ (U.X k).Λ := fun a => (W.φ k a).2
  have hrange : ∀ z, z ∈ Pm'.range ↔ ∃ v ∈ (U.X k).Λ, z = pv (U.X k) idx x.1 v := fun z => by
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, hmem a, hpv a⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj v hv
      exact ⟨a, hpv a⟩
  have hspan' : Submodule.span E ((U.X k).Λ : Set (Fin r → E)) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact hmem a
  have hhx : ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w := by
    refine (huniq _ hspan').2 Hm hH ?_
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hsurj u hu
    obtain ⟨b, rfl⟩ := hsurj v hv
    rw [← hpv, ← hpv, hIm, ← hEF]
    simp
  have hl' : (fun z => (ex z).left) = fun z => (W.F.ex (W.ik k) Pm' z).left := funext hl
  refine ⟨{ ex := ex
            ex_add := e1
            ex_onto := e2
            ex_ker := fun z => (e3 z).trans (hrange z)
            ex_lin := fun a z => by simp only [hty]; exact e4 a z
            hol := ?_
            der := fun ℓ => by rw [hl']; exact hder ℓ.1 ℓ.2
            fr := fr
            fr_hol := fun j => by simp only [hl]; exact h1 j
            fr_ne := fun j z => by rw [hl]; exact h2 j z
            fr_g := fun j j' z => by rw [hl]; exact h3 j j' z
            fr_0 := fun j => by rw [hl]; exact h4 j
            χ := fun v => χl (pv (U.X k) idx x.1 v)
            χ_norm := ?_
            fr_per := ?_ }, ?_, ?_, ⟨Pm'.range, Fd, hrange, h7, ?_⟩, hhx⟩
  · rw [hl']
    intro V f
    have := ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol W.F (W.ik k) Pm' hP V f
    simpa only [Set.mem_univ, true_and] using this
  · intro v hv
    obtain ⟨a, rfl⟩ := hsurj v hv
    rw [← hpv]
    obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1
      (Xo.univ.t.PP.isLB.cover.ge (Set.mem_univ ((ex 0).left (IsLocalRing.closedPoint ℂ))))
    exact (h5 a j 0).1
  · intro v hv j z
    obtain ⟨a, rfl⟩ := hsurj v hv
    rw [hl, ← hpv, ← hhx, ← hhx]
    exact (h5 a j z).2
  · intro a ha
    show levPt Xo (unC U k x).x a = ex _
    rw [e5 a ha, hsm, hpv]
    congr 1
    funext j
    simp [UW.mark]
  · intro j z pt
    show _ = (ex z).left → _ → ⊤ ≤ (ex z).left ⁻¹ᵁ _ → _ = θ z * fr j z ^ (1 : ℤ)
    rw [hl, zpow_one]
    exact h6 j z pt
  · simp only [← hhx]
    exact h8

end GlobalTheory.FrameEquiv
