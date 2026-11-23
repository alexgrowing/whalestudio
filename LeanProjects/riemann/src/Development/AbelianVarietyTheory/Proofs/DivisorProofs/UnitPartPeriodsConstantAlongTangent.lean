import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialDegenerationUnitPartExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartPeriodTauZeroValueOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPsiTauTangentVectorVariationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitsAlong

theorem alg {G : Type} [CommGroup G] (P T Rg Wy Wyz Wz W0 U2 E Pc Tc Rgc : G) (e : ℕ) (n n' : ℤ)
    (hA : P ^ e * T * Rg ^ e = Wy ^ n * Wyz * Wz⁻¹ * W0 ^ n' * (U2 * E) * Pc ^ e * Tc * Rgc ^ e)
    (hB : P ^ e * 1 * Rg ^ e = Wy ^ n * Wy * W0⁻¹ * W0 ^ n' * U2 * Pc ^ e * 1 * Rgc ^ e) :
    T = Wyz * Wy⁻¹ * Wz⁻¹ * W0 * E * Tc := by
  apply Additive.ofMul.injective
  have hA' := congrArg Additive.ofMul hA
  have hB' := congrArg Additive.ofMul hB
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, ofMul_one, add_zero] at hA' hB' ⊢
  calc Additive.ofMul T = (e • Additive.ofMul P + Additive.ofMul T + e • Additive.ofMul Rg) -
        (e • Additive.ofMul P + e • Additive.ofMul Rg) := by abel
    _ = _ := by rw [hA', hB']; abel

theorem unitTau_along : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ c : ℚ, c ≠ 0 ∧ ∃ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen ∧ ∀ y z τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam y z τ₀ → ∀ e : (DualNumber k)ˣ, (e : DualNumber k) = 1 + TrivSqZeroExt.inr (∑ i, (c : k) * MvPowerSeries.constantCoeff (q i) * gam i y z) → ∀ zz J, Good P.D.toPre.P.L zz J → val τ₀ (spMap ρ) zz J = gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) * (gm (c' (y)) zz _ (w.s (fun _ => J (c' (y) ≫ π₂), fun _ => J (c' (y) ≫ π₁))))⁻¹ * (gm (c' (z)) zz _ (w.s (fun _ => J (c' (z) ≫ π₂), fun _ => J (c' (z) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) * val τ₀ (spMap (constHom ρ)) zz J := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  intro Y n' v' dd hdd D q hq h hB hdef hΘ ρ hρ B' _ π₁ π₂ c' h₁ h₂ hfib hc'
  obtain ⟨w, hw⟩ := GlobalTheory.ConstDefSym.lbIso_pull_of_const (ChartRing k m d) P.D.toPre k ρ B' inferInstance π₁ π₂ h₁ h₂ hfib
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.unitPart_psi_tau_tangent_vector_variation E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hB hdef hΘ ρ hρ B' π₁ π₂ c' h₁ h₂ hfib hc' w hw
  refine ⟨-1, by norm_num, w, hw, ?_⟩
  intro y z τ₀ hτ ee hee zz J hJ
  obtain ⟨n, ψ₀, hψ⟩ := GlobalTheory.UnitPart.exists_isUnitPart P.D.toPre (bdParam k m d) gam hmon y
  obtain ⟨τ₁, hτ₁, hv₁⟩ := GlobalTheory.T.exists_unitPartPeriodTau_zero_value_one E H k m d t P gam y
  obtain ⟨e₁, he₁⟩ := hlam y z n ψ₀ τ₀ hψ hτ
  obtain ⟨e₂, he₂⟩ := hlam y 0 n ψ₀ τ₁ hψ hτ₁
  obtain ⟨u₂, hu₂⟩ : ∃ u : (DualNumber k)ˣ, (u : DualNumber k) = 1 + TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i)) :=
    ⟨⟨_, 1 - TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i)),
      by ext <;> simp, by ext <;> simp⟩, rfl⟩
  have hu₁ : ((u₂ * ee : (DualNumber k)ˣ) : DualNumber k) = 1 + TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y z : k)) * MvPowerSeries.constantCoeff (q i)) := by
    rw [Units.val_mul, hu₂, hee]
    have hs : ∀ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y z : k)) * MvPowerSeries.constantCoeff (q i) =
        (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i) -
          (((-1 : ℚ) : k) * MvPowerSeries.constantCoeff (q i) * (gam i y z : k)) := by
      intro i
      simp only [map_zero, Int.cast_zero, add_zero, Rat.cast_neg, Rat.cast_one]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_sub_distrib]
    ext <;> simp
    ring
  have A := he₁ (max e₁ e₂) (le_max_left _ _) (u₂ * ee) hu₁ zz J hJ
  have B := he₂ (max e₁ e₂) (le_max_right _ _) u₂ hu₂ zz J hJ
  rw [hv₁ _ (spMap ρ) zz J hJ, hv₁ _ (spMap (constHom ρ)) zz J hJ] at B
  have hW : ∀ a : P.D.toPre.X, a = y →
      gm (c' a) zz _ (w.s (fun _ => J (c' a ≫ π₂), fun _ => J (c' a ≫ π₁))) =
        gm (c' y) zz _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))) := by
    rintro a rfl; rfl
  rw [hW (y + 0) (add_zero y)] at B
  have hG : gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn (u₂ * ee)) =
      gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn u₂) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) := by
    rw [← map_mul]; congr 1; simp only [unitOn, map_mul]
  rw [hG] at A
  exact alg (hA := A) (hB := B)

end GlobalTheory.UnitsAlong
