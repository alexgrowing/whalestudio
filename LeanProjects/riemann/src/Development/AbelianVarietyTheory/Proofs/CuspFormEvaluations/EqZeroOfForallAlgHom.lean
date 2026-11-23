import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality

noncomputable section

namespace GlobalTheory.FiniteOrderRule

open Formalism.L2.Pj

theorem eq_zero_of_forall_algHom {K R Ω : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R]
    [Algebra.FiniteType K R] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (x : R)
    (h : ∀ φ : R →ₐ[K] Ω, φ x = 0) : x = 0 := by
  have hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hb : (⊥ : Ideal R).jacobson = ⊥ := hJ.out (Ideal.isRadical_bot)
  rw [← Ideal.mem_bot, ← hb, Ideal.jacobson, Ideal.mem_sInf]
  rintro J ⟨-, hM⟩
  letI := Ideal.Quotient.field J
  haveI : Module.Finite K (R ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ J)
  let ψ : (R ⧸ J) →ₐ[K] Ω := IsAlgClosed.lift
  have h0 := h (ψ.comp (Ideal.Quotient.mkₐ K J))
  have h1 : Ideal.Quotient.mk J x = 0 := by
    apply ψ.toRingHom.injective
    rw [map_zero]
    exact h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

theorem pow_eq_one_of_complex {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (hW : EvalWD pts mapR)
    (hB : ∀ (S : Type) [CommRing S] [Algebra K S] (T : Type) [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
      (y : pts S), ∃ z : pts T, mapR φ y z)
    (σ : K →+* ℂ) (f : Rules pts) (hf : IsNatural pts mapR f) (k : ℕ)
    (h : ∀ y : pts (CAt σ), evalAt pts mapR f y ^ k = 1) (p : TRing K) (y : pts p.R) : f p y ^ k = 1 := by
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  rw [← sub_eq_zero]
  letI : Algebra K ℂ := σ.toAlgebra
  refine eq_zero_of_forall_algHom (K := K) (Ω := ℂ) _ ?_
  intro φ
  let φ' : p.R →ₐ[K] CAt σ := φ
  obtain ⟨z, hz⟩ := hB p.R (CAt σ) φ' y
  have hT : FromTest pts mapR z := ⟨p, φ', y, hz⟩
  have h0 := h z
  unfold evalAt at h0
  rw [dif_pos hT, ← hW f hf (CAt σ) p _ φ' _ y _ z hz hT.choose_spec.choose_spec.choose_spec] at h0
  show φ' _ = 0
  rw [map_sub, map_pow, h0, map_one, sub_self]

theorem evalAt_pow_eq_one {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (f : Rules pts) (k : ℕ) (h : ∀ (p : TRing K) (y : pts p.R), f p y ^ k = 1)
    {S : Type} [CommRing S] [Algebra K S] (y : pts S) (hT : FromTest pts mapR y) :
    evalAt pts mapR f y ^ k = 1 := by
  unfold evalAt
  rw [dif_pos hT, ← map_pow, h, map_one]

end GlobalTheory.FiniteOrderRule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem GlobalTheory.FiniteOrderRule.unitC_of_cmp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cls : Type) [CommGroup Cls] [Finite Cls] (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false → UnitC d := by
  intro E _ _ _ H Dw l Xo c n d Cls _ _ δ gdet hC A y
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hk : Nat.card Cls ≠ 0 := Nat.card_pos.ne'
  have h1 := GlobalTheory.FiniteOrderRule.pow_eq_one_of_complex (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) (GlobalTheory.Frames.algebraic_laws hS E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw d.l₂ d.Xo₂ d.c₂ S T φ y)
    d.c₂.F.val.toRingHom d.cδ hC.1.1 (Nat.card Cls) (fun z => by
      have h2 := hC.2 z
      unfold evR at h2
      rw [h2, if_neg Bool.false_ne_true, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one,
        Units.val_one, map_one])
  have h3 := @GlobalTheory.FiniteOrderRule.evalAt_pow_eq_one d.c₂.F _ (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) d.cδ (Nat.card Cls) h1 ℂ _ A y
    (@GlobalTheory.Frames.allTest_of_secBaseChange hS E _ _ _ H Dw d.l₂ d.Xo₂ d.c₂ ℂ _ inferInstance A y)
  exact Complex.norm_eq_one_of_pow_eq_one h3 hk

end
