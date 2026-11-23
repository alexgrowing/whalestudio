import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemTraitsChartThetaModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemLamOfExactClassSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourOfGaloisClassSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourRescaleApproximatedUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaTermsOfMulIndexZeroTermEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemIndexZeroCoefficientApproxStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Poinc.Sep.exists_chartMember_traitsR : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W ((l ^ j) ^ 2) (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ.pre ∧ IsChartMember X₁ z₁ Φ Q ξ t δ y ρ e h := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsym hnn hpos hmon ξ hξ l hl hln j₀
  obtain ⟨j, X₁, z₁, hdom, Φ, y, ρ, e, h, c₀, hj, hR, hC, hU, hM, hE, hCS⟩ :=
    GlobalTheory.T.exists_fourierTermSystem_traits_chart_thetaModel g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth V Q m t δ hrk ht hsym hnn hpos hmon ξ hξ l hl hln
      (max j₀ 1)
  obtain ⟨-, -, hIC, -⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hN : 3 ≤ (l ^ j) ^ 2 := by
    have h2 : 2 ≤ l ^ j := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
    nlinarith
  have hLam : Φ.abelian₂ := GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums ℤ id g 8 W _ Φ ((l ^ j) ^ 2) (by norm_num) hN hE
  have hFour : Φ.Four ((l ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_of_galois_class_sums ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hCS
  let v : ∀ y', (Φ.V y')ˣ := fun y' => (hU y').unit⁻¹
  have happ : ∀ e' : ℕ, ∃ a : X₁.M.Z.presheaf.stalk z₁, ∀ y', Φ.ev y' a - ((v y')⁻¹ : (Φ.V y')ˣ) ∈
      (maximalIdeal (X₁.M.Z.presheaf.stalk z₁) ^ e').map (Φ.ev y') := by
    intro e'
    obtain ⟨a, ha⟩ := GlobalTheory.T.fourierTermSystem_indexZero_coefficient_approx ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hN hE hLam hFour
      (fun y₁ y₂ h₁ h₂ => (hM y₁ h₁).trans (hM y₂ h₂).symm) c₀ e'
    refine ⟨a, fun y' => ?_⟩
    simpa [v] using ha y'
  have hFour' : (Φ.rescale v).Four ((l ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_rescale_approximated_units ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hFour v happ
  have hLam' : (Φ.rescale v).abelian₂ := hLam
  refine ⟨j, X₁, z₁, (Φ.rescale v).toVSys ((l ^ j) ^ 2) hLam' hFour', y, ρ, e, h,
    le_trans (le_max_left _ _) hj, hR, ?_⟩
  obtain ⟨h1, h2, h3, h4, D, e₈, hS, hT⟩ := hC
  refine ⟨h1, h2, h3, h4, D, e₈, hS, ?_⟩
  have h0 : Φ.term y (fun a => e.symm ((0 : Fin 8 → Q.X) a)) c₀ * ((v y : (Φ.V y)ˣ) : Φ.V y) = 1 := by
    have hz : (fun a => e.symm ((0 : Fin 8 → Q.X) a)) = 0 := by
      funext a; simp
    rw [hz]
    simp [VPre.term, mono, qW, v]
  have := GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one (Φ.V y) D ((l ^ j) ^ 2) (Fin 8 → Q.X) Φ.Q e₈
    (fun mu c => Φ.term y (fun a => e.symm (mu a)) c) (v y) c₀ hT h0
  refine cast (congrArg (fun T : (Fin 8 → Q.X) → Φ.Q → Φ.V y => IsThetaTerms D ((l ^ j) ^ 2) e₈ T) ?_) this
  funext mu c
  show Φ.u y (fun a => e.symm (mu a)) c * mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a)) * ((v y : (Φ.V y)ˣ) : Φ.V y) =
    Φ.u y (fun a => e.symm (mu a)) c * ((v y : (Φ.V y)ˣ) : Φ.V y) * mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a))
  exact mul_right_comm _ _ _
