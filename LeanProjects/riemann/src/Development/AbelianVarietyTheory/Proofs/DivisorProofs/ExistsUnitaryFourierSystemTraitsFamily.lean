import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStalkNormalNoetherianFractionRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemLamOfExactClassSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourOfGaloisClassSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourRescaleApproximatedUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemIndexZeroCoefficientApproxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaTermsOfMulIndexZeroTermEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep

set_option maxHeartbeats 1000000 in

theorem exists_system_with_traits_and_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (M : Scheme.{0}) (_ : IsIntegral M) (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] ((n ^ j) ^ 2) (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty ∧ j₀ ≤ j ∧ IsCov C g z₁ ζ ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U ∧ IsMember ζ Φ Cm ξ y ρ e h := by
  intro E _ _ _ H Dw hpq l Xo c C φ V _ _ _ Cm hV ξ hξ n hn hodd j₀
  obtain ⟨j, X₁, π, z₁, ζ, hdom, U, Φ, y, ρ, e, h, c₀, hj, hcov, hU, hT, hM, hunit, hm1, hE, hCS⟩ :=
    GlobalTheory.T.exists_unitary_fourier_system_traits_chart E H Dw hpq l Xo c C φ V Cm hV ξ hξ n hn hodd (max j₀ 1)
  obtain ⟨-, -, hIC, -⟩ := GlobalTheory.T.modelStalk_normal_noetherian_fractionRing X₁ z₁
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hN : 3 ≤ (n ^ j) ^ 2 := by
    have h3 : 3 ≤ n := by
      rcases hodd with ⟨k, hk⟩
      have := hn.two_le
      omega
    have h2 : 3 ≤ n ^ j := le_trans h3 (Nat.le_self_pow (by omega) n)
    nlinarith
  have hLam : Φ.abelian₂ := GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) (by norm_num) hN hE
  have hFour : Φ.Four ((n ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_of_galois_class_sums (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hCS
  let v : ∀ y', (Φ.V y')ˣ := fun y' => (hunit y').unit⁻¹
  have happ : ∀ e' : ℕ, ∃ a : X₁.M.Z.presheaf.stalk z₁, ∀ y', Φ.ev y' a - ((v y')⁻¹ : (Φ.V y')ˣ) ∈
      (maximalIdeal (X₁.M.Z.presheaf.stalk z₁) ^ e').map (Φ.ev y') := by
    intro e'
    obtain ⟨a, ha⟩ := GlobalTheory.T.fourierTermSystem_indexZero_coefficient_approx (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hN hE hLam hFour
      (fun y₁ y₂ h₁ h₂ => (hm1 y₁ h₁).trans (hm1 y₂ h₂).symm) c₀ e'
    refine ⟨a, fun y' => ?_⟩
    simpa [v] using ha y'
  have hFour' : (Φ.rescale v).Four ((n ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_rescale_approximated_units (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hFour v happ
  have hLam' : (Φ.rescale v).abelian₂ := hLam
  refine ⟨j, X₁.M.Z, inferInstance, π, z₁, ζ, (Φ.rescale v).toVSys ((n ^ j) ^ 2) hLam' hFour', y, ρ, e, h, U, hU,
    le_trans (le_max_left _ _) hj, hcov, hT, ?_⟩
  obtain ⟨h1, h2, h3, h4, D, p, hT0⟩ := hM
  refine ⟨h1, h2, h3, h4, D, p, ?_⟩
  have h0 : Φ.term y (fun _ => e.symm 0) c₀ * ((v y : (Φ.V y)ˣ) : Φ.V y) = 1 := by
    have hz : (fun _ : Fin 1 => e.symm 0) = 0 := by
      funext a; simp
    rw [hz]
    simp [VPre.term, mono, qW, v]
  have := GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one (Φ.V y) D ((n ^ j) ^ 2) _ Φ.Q p.xe.symm
    (fun mu c => Φ.term y (fun _ => e.symm mu) c) (v y) c₀ hT0 h0
  refine cast (congrArg (fun T => GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) p.xe.symm T) ?_) this
  funext mu c
  show Φ.u y (fun _ => e.symm mu) c * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu) * ((v y : (Φ.V y)ˣ) : Φ.V y) =
    Φ.u y (fun _ => e.symm mu) c * ((v y : (Φ.V y)ˣ) : Φ.V y) * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu)
  exact mul_right_comm _ _ _

end GlobalTheory.USep
