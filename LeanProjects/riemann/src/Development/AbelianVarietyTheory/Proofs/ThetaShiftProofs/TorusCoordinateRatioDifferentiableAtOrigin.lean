import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
open Filter Topology

namespace GlobalTheory.AbelianLetters

theorem exists_top_le_wchart {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Sp ℂ ⟶ X)) : ∃ j, ⊤ ≤ LB.wchart L φ j := by
  choose j hj using fun k => exists_chart hL (φ k (default : PrimeSpectrum ℂ))
  refine ⟨j, fun p _ => Set.mem_iInter.2 fun k => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hj k

theorem valAt'_unit_ne_zero {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U f.val ≠ 0 := by
  rw [HolHom.valAt'_eq_valR, HolHom.valR_eq _ _ h]
  exact (f.isUnit.map _).ne_zero

theorem IsRatio.differentiableAt_zero : ∀ [Algebra (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (s₀ : Out.GtPt D D.P.A), s₀.b = 𝟙 D.P.A ^ n → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n s₀ u → ∀ x, DifferentiableAt ℂ (u x) 0 := by
  intro _ D g n ex s₀ hb hadd hol hchi u hu x
  obtain ⟨j, hj⟩ := exists_top_le_wchart D.P.isLB (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • 0)).b x)
  have h1 : ∀ z, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j ↔
      ⊤ ≤ (show Sp ℂ ⟶ _ from (ex z).b.left) ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A (𝟙 D.P.A ^ 1) x) j := by
    intro z
    have := top_le_wchart_nsmul hadd (n := 1) rfl z x j
    rwa [Nat.cast_one, one_smul] at this
  have hS : {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j} ∈ 𝓝 ((n : ℂ) • (0 : Fin g → ℂ)) := by
    filter_upwards [(HolHom.holAt_of_isHolTo hol (Set.mem_univ ((n : ℂ) • (0 : Fin g → ℂ))) _ ((h1 _).1 hj)).1]
      with t ht using (h1 t).2 ht
  have hn : DifferentiableAt ℂ (fun z : Fin g → ℂ => (n : ℂ) • z) 0 := by fun_prop
  have hc : DifferentiableAt ℂ (fun z => chiVal (ex ((n : ℂ) • z)) x j) 0 :=
    ((hchi x j).differentiableAt hS).comp 0 hn
  have h0 := (top_le_wchart_nsmul hadd hb 0 x j).1 hj
  obtain ⟨hev, hd⟩ := HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) _ h0
  refine (hc.fun_mul ((hd ((s₀.s x).s j).val).fun_inv (valAt'_unit_ne_zero _ h0 _))).congr_of_eventuallyEq ?_
  filter_upwards [hev] with t ht
  exact (eq_mul_inv_iff_mul_eq₀ (valAt'_unit_ne_zero _ ht _)).2
    (hu x t j ((top_le_wchart_nsmul hadd hb t x j).2 ht)).symm

end GlobalTheory.AbelianLetters
