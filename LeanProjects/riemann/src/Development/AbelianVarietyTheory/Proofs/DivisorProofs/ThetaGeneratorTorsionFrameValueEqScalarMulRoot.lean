import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaTermsTorsionPointsFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFibreSectionEqScalarMulIntegralThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameMulIntegralFrameEqRootMulRigStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

noncomputable section

namespace GlobalTheory.USep.FrameInt

theorem frameValue_eq_lam_root_mul : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (x : Over.mk (spMap ev) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : K), IsTorsFrame D.P ρ₀ (m ^ 2) x τ → IsValueAt D.P.A D.P.L ((1 : ℕ) : ℤ) th x (powFrame D.P.A D.P.L x τ ((1 : ℕ) : ℤ)) (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro m hm hm3 V₁ _ _ _ hV hunit D X C _ e u mo hmo hT K _ _ ev ρ₀ hρ₀ th hth
  obtain ⟨θ, hθ, -⟩ := ThetaOne.main hV D
  obtain ⟨b, t, s₀, hcov, htg, hκ, hid⟩ := GlobalTheory.T.integral_thetaTerms_torsionPoints_frames m hm hm3 V₁ hV hunit D X C e u mo hmo hT θ hθ ρ₀ hρ₀
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.thetaFibre_section_eq_scalar_mul_integralTheta V₁ D θ hθ K ev th
  refine ⟨(m ^ 2) ^ 2, Λ * ev s₀, Nat.one_le_pow _ _ (by positivity), ?_⟩
  intro x τ c hτ hval
  obtain ⟨c₀, rfl⟩ := hcov K (spMap ev) x hτ.1
  obtain ⟨ζ, hζ, hζv⟩ := GlobalTheory.T.torsionFrame_mul_integralFrame_eq_root_mul_rig V₁ D K ev ρ₀ hρ₀ (m ^ 2) (Nat.one_le_pow _ _ (by omega)) (b c₀) τ hτ (t c₀) (htg c₀)
    (fun κ hκn z J hJ => hκ c₀ κ hκn _ _ z J hJ)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hζ
    exact zero_ne_one hζ
  refine ⟨c₀, ζ⁻¹, by rw [inv_pow, hζ, inv_one], ?_⟩
  let z : (Over.mk (spMap ev)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  choose J hJ using fun χ : (Over.mk (spMap ev)).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have hG : Good D.P.L z J := hJ
  have h1 := GlobalTheory.CoordSep.sv_value hval hG
  have h2 := hΛ _ (lift (𝟙 _) (toUnit _ ≫ b c₀)).left z J hG
  have h3 := hid c₀ _ (Over.mk (spMap ev)).hom z J hG
  have h4 := hζv z J hG
  have eT : (toUnit (Over.mk (spMap ev))).left = (Over.mk (spMap ev)).hom := by
    simpa using Over.w (toUnit (Over.mk (spMap ev)))
  have e1 : (lift (𝟙 (Over.mk (spMap ev))) (toUnit _ ≫ b c₀)).left ≫ (fst (Over.mk (spMap ev)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have e2 : (lift (𝟙 (Over.mk (spMap ev))) (toUnit _ ≫ b c₀)).left ≫ (snd (Over.mk (spMap ev)) D.P.A).left =
      (Over.mk (spMap ev)).hom ≫ (b c₀).left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left, eT]
  rw [e1, e2] at h2
  rw [GlobalTheory.UT.NonVan.val_powFrame] at h1
  have e11 : val τ (𝟙 (Over.mk (spMap ev)).left) z J ^ (((1 : ℕ) : ℤ)) = val τ (𝟙 (Over.mk (spMap ev)).left) z J := zpow_one _
  rw [e11] at h1
  dsimp only [GlobalTheory.VVRank.sv] at h1
  let G : K →+* (Over.mk (spMap ev)).left.presheaf.stalk z := RatioVal.germConst K z
  have g1 : ∀ a : K, gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf a) = G a := fun a => RatioVal.gs_id_const z a
  have g2 : ∀ a : V₁, gs (Over.mk (spMap ev)).hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom a) = G (ev a) :=
    fun a => (RatioVal.gs_specMap ev z _).trans (congrArg (fun y => G (ev y))
      (by rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]))
  have g3 : gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf Λ) = G Λ := g1 Λ
  rw [g1] at h1 h4
  rw [g3] at h2
  rw [g2] at h3
  have key : G (c * ζ) * ↑(val ρ₀ (Over.mk (spMap ev)).hom z J) =
      G (Λ * ev (s₀ * u 0 c₀)) * ↑(val ρ₀ (Over.mk (spMap ev)).hom z J) := by
    rw [map_mul, map_mul, _root_.mul_assoc, ← h4, ← _root_.mul_assoc, ← h1, h2, _root_.mul_assoc, h3, _root_.mul_assoc]
  have key2 := (Units.mul_left_inj _).1 key
  have key3 : c * ζ = Λ * ev (s₀ * u 0 c₀) := G.injective key2
  rw [map_mul] at key3
  field_simp
  linear_combination key3

end GlobalTheory.USep.FrameInt
