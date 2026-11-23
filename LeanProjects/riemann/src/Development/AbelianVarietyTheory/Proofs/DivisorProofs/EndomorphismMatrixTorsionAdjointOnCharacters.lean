import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelCongruenceEndoAllAlgClosedFieldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTauLineBundleCoordinateEqExpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdjointApplyOfWeightedQuadraticSumPolarStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section
namespace GlobalTheory.Poinc.FibMatrix

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ sc : ℝ, 0 < sc → ∀ j : u.D.toPre.X ≃+ (Fin 8 → X₀), (∀ χ, l.q χ = sc * (qW W β (j χ) : ℤ)) → ∀ (e : ρ.P.A ⟶ ρ.P.A) (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ e.left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) → ∀ (F : u.G ⟶ u.G) (eA : u.A.A ⟶ u.A.A), IsMonHom F → eA.left ≫ u.φ = u.φ ≫ e.left → eA.left ≫ genMap u.U = genMap u.U ≫ F.left → ∀ m : u.D.toPre.X →+ u.D.toPre.X, EndChar u.U F m → ∀ χ, j (m χ) = fun a => ∑ b, E' a b • j χ b := by
  intro o Ω _ _ _ S ρ p _ y₀ u l W hW X₀ _ β hβs hβp sc hsc j hq e E E' hEE hlab F eA hF heA hgen m hm χ
  have hCZ : CharZero u.V :=
    RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hBase : GlobalTheory.Mum.Base u.V := ⟨⟨inferInstance, inferInstance, inferInstance, u.complete⟩, hCZ⟩
  let Em : (Fin 8 → X₀) →+ (Fin 8 → X₀) :=
    { toFun := fun y a => ∑ b, E a b • y b
      map_zero' := by ext; simp
      map_add' := fun y y' => by ext; simp [smul_add, Finset.sum_add_distrib] }
  have hEm : ∀ y, Em y = fun a => ∑ b, E a b • y b := fun _ => rfl
  let s : u.D.toPre.X →+ u.D.toPre.X := (j.symm.toAddMonoidHom.comp Em).comp j.toAddMonoidHom
  have hs : ∀ x, j (s x) = Em (j x) := fun x => by simp [s]
  have hlab' : ∀ (k : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) k) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A),
      1 ≤ k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk' x' →
      x'.left = x.left ≫ eA.left → CongMod k pk'.y (s pk.y) := by
    intro k pk pk' x x' hk hx hx' hxx
    obtain ⟨w, hw⟩ := hlab k pk pk' x x' hk hx hx' (by rw [hxx, Category.assoc, heA])
    refine ⟨j.symm w, j.injective ?_⟩
    rw [map_add, map_nsmul, AddEquiv.apply_symm_apply, hs, hw, hEm]
  have hT := GlobalTheory.T.labelCongruence_endo_all_algClosed_fields o Ω S ρ p y₀ u eA s hlab'
  haveI : Mono (jK u.V) := GlobalTheory.PolDeg.Wit.mono_jK
  haveI : Mono (genMap u.U) := by unfold genMap; infer_instance
  have hTor := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar u.V hBase u.G u.semi u.D u.A u.U F hF m hm
  have hmain := GlobalTheory.TauFormHom.main u.V hBase inferInstance u.G u.semi u.D u.A u.U u.G u.semi u.D u.A u.U F hF m s hTor
    (by
      intro F' _ _ _ k hk q q' a a' hqa hqa' haa
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hk)
      have ha : a.left = a'.left ≫ eA.left := by
        rw [← cancel_mono (genMap u.U), haa, Category.assoc, hgen]
      exact hT F' k hk1 hk q q' a a' hqa hqa' ha)
  have hunit : ∀ w : u.Vˣ, ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V))‖ = 1 := by
    intro w
    have h1 := (u.norm_le (algebraMap u.V _ (w : u.V))).2 ⟨w, rfl⟩
    have h2 := (u.norm_le (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V))‖ *
        ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    have h4 := norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V)))
    have h5 := norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V)))
    nlinarith
  have hpol : ∀ a' b, l.q (s a' + b) - l.q (s a') - l.q b = l.q (a' + m b) - l.q a' - l.q (m b) := by
    intro a' b
    obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord u.V u.D.toPre (s a') b
    obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord u.V u.D.toPre a' (m b)
    obtain ⟨w, hw⟩ := hmain a' b x x' hx hx'
    have n₁ := GlobalTheory.T.norm_tauLineBundleCoordinate_eq_exp o Ω S ρ p y₀ u l (s a') b x hx
    have n₂ := GlobalTheory.T.norm_tauLineBundleCoordinate_eq_exp o Ω S ρ p y₀ u l a' (m b) x' hx'
    rw [hw, map_mul, norm_mul, hunit, _root_.one_mul, n₂] at n₁
    have := Real.exp_injective n₁
    linarith
  have hpolW : ∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + j χ) - qW W β (fun a => ∑ b, E a b • y b) -
      qW W β (j χ) = qW W β (y + j (m χ)) - qW W β y - qW W β (j (m χ)) := by
    intro y
    have h := hpol (j.symm y) χ
    rw [hq, hq, hq, hq, hq, hq, map_add, map_add, hs, AddEquiv.apply_symm_apply, hEm] at h
    have h' : sc * ((qW W β ((fun a => ∑ b, E a b • y b) + j χ) - qW W β (fun a => ∑ b, E a b • y b) -
        qW W β (j χ) : ℤ) : ℝ) = sc * ((qW W β (y + j (m χ)) - qW W β y - qW W β (j (m χ)) : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast mul_left_cancel₀ hsc.ne' h'
  exact GlobalTheory.T.eq_adjoint_apply_of_weightedQuadraticSum_polar W hW X₀ β hβs hβp E E' hEE (j χ) (j (m χ)) hpolW

end GlobalTheory.Poinc.FibMatrix
