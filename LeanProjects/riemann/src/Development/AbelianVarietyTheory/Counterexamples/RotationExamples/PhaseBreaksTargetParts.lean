import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature

namespace GlobalTheory.ConjLiftCounterexample

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
  {σ : D.what₂.LL →+* ℂ}

theorem inner_of_unitary {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (U : X ≃ₗᵢ[ℂ] X) (g : X → X)
    (hg : ∀ a b, ⟪g a, g b⟫_ℂ = ⟪a, b⟫_ℂ) {κ : ℂ} (hκ : ‖κ‖ = 1) {p p' q q' : X} (h : U p = κ • g q) (h' : U p' = κ • g q') :
    ⟪p, p'⟫_ℂ = ⟪q, q'⟫_ℂ := by
  have key : ⟪U p, U p'⟫_ℂ = ⟪κ • g q, κ • g q'⟫_ℂ := by rw [h, h']
  rw [LinearIsometryEquiv.inner_map_map, inner_smul_left, inner_smul_right, hg, ← mul_assoc,
    RCLike.conj_mul, hκ] at key
  simpa using key

set_option maxHeartbeats 2000000 in

theorem gram_of_conjAt {ph : ℂ} {c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W} (h : ConjAt R i σ ph c₀)
    {μ' η' : (AE D)ˣ →* Circle} {c : CoefA (Vc D i)} {c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W}
    {H : HMod (Bridge.Gf (Vc D i) → c.W)} {j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H} {th : H.H →ₗ[ℂ] (R.HW i σ).H}
    (hd : IsConjDatum R i σ c₀ μ' η' c c₁ H j th) {x x' : A.fam.amb.FL i A.μ0} {y y' : Fin (R.nW i) → D.what₂.LL}
    (hy : IsRatLift R i ph x y) (hy' : IsRatLift R i ph x' y') :
    @inner ℂ (R.HW i σ).H _ ((R.FW i).j σ y) ((R.FW i).j σ y') = @inner ℂ (R.HW i σ).H _ (th (j x)) (th (j x')) := by
  obtain ⟨-, -, u, U, z, ζ, -, -, hz, hall⟩ := h
  obtain ⟨-, κ, hκ, hlift⟩ := hall μ' η' c c₁ H j th hd
  exact inner_of_unitary U (fun w => R.gW i σ z w) hz.unitary hκ (hlift x y hy) (hlift x' y' hy')

end GlobalTheory.ConjLiftCounterexample

end
