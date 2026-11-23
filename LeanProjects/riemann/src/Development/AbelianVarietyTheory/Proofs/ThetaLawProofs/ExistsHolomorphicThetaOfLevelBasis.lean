import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRepresentativesModSimilitudeTransposeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicCoordSimilitudeThetaProductStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharLevelOneAndHolomorphicParameterStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaGeneratorPullbackMulConstInFramesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeGeneratorEqExpInFramesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaUniformisationFrameEqAutomorphyMulStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MulTransposeEqOfTransposeMulEq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.SimilTheta

theorem germ_stalkClosedPointTo_appLE {Y : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ Y)
    (U : Y.Opens) (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    Y.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]

theorem exists_ev {Y : Scheme.{0}} (p : Sp ℂ ⟶ Y) :
    ∃ (y : Y) (ev : Y.presheaf.stalk y →+* ℂ),
      (∀ (X : Scheme.{0}) (f : Y ⟶ X) (U : X.Opens), f y ∈ U ↔ ⊤ ≤ (p ≫ f) ⁻¹ᵁ U) ∧
      ∀ (X : Scheme.{0}) (f : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)), f y ∈ U → ev (gs f y U a) = valAt' (p ≫ f) U a := by
  refine ⟨p (IsLocalRing.closedPoint ℂ), (Scheme.stalkClosedPointTo (R := .of ℂ) p).hom, fun X f U => ?_,
    fun X f U a h => ?_⟩
  · rw [top_le_preimage_iff_mem, Subsingleton.elim (α := PrimeSpectrum ℂ) default (IsLocalRing.closedPoint ℂ)]
    rfl
  · have hU := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of ℂ) p (U := f ⁻¹ᵁ U) h).ge
    have e := germ_stalkClosedPointTo_appLE (R := .of ℂ) p (f ⁻¹ᵁ U) h
    rw [gs_eq f _ U h, ← valAt'_comp, valAt'_eq_valAt p hU]
    exact congrArg (fun q => q.hom ((f.app U).hom a)) e

theorem val_cst {X : Scheme.{0}} (p : Sp ℂ ⟶ X) (f : X ⟶ Sp ℂ) (hp : p ≫ f = 𝟙 _) (a : ℂ) :
    valAt' p ⊤ (cst f ⊤ a) = a := by
  refine (valAt'_map p (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op _ le_top).trans ?_
  refine (valAt'_comp p f ⊤ _).trans ?_
  rw [hp, valAt'_id_top]

theorem ev_val {X Y Z : Scheme.{0}} {p : Sp ℂ ⟶ Z} {z : Z} {ev : Z.presheaf.stalk z →+* ℂ}
    (hev : ∀ (X : Scheme.{0}) (f : Z ⟶ X) (U : X.Opens) (a : Γ(X, U)), f z ∈ U → ev (gs f z U a) = valAt' (p ≫ f) U a)
    {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ep : K → ℤ} (t : LB.Gen (LB.LinComb L φ ep)) (r : Z ⟶ Y)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (j : K → L.ι) (h : ∀ k, J (r ≫ φ k) = j k) (q : Sp ℂ ⟶ Y) (hq : p ≫ r = q) :
    ev (val t r z J).val = valAt' q (LB.wchart L φ j) (t.s j).val := by
  obtain rfl : (fun k => J (r ≫ φ k)) = j := funext h
  subst hq
  exact (congrArg ev (gs_unit r z _ (hJ.mem φ r) _).symm).trans (hev _ _ _ _ (hJ.mem φ r))

variable {g : ℕ} (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g)

theorem ex_zsmul (n : ℤ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n :=
  map_zpow (MonoidHom.mk' (fun z : Multiplicative (Fin g → ℂ) => u.ex z.toAdd) fun _ _ => u.ex_add _ _)
    (Multiplicative.ofAdd z) n

theorem ex_prod (s : Fin 4 → ℤ) (y : Fin 4 → Fin g → ℂ) :
    (List.ofFn fun c => u.ex (y c) ^ s c).prod = u.ex (∑ c, s c • y c) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, Fin.sum_univ_succ, Fin.sum_univ_zero,
    u.ex_add, ex_zsmul, CubeValues.ex_zero]

theorem comp_alMap (al : Matrix (Fin 4) (Fin 4) ℤ) (r : Fin 4) (t : Fin g → ℂ) (y : Fin 4 → Fin g → ℂ)
    (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4) (hy : ∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) :
    pt ≫ alMap x al r (u.ex t) = u.ex (∑ c, al r c • y c + t) := by
  have e₀ : pt ≫ toUnit _ = 𝟙 _ := toUnit_unique _ _
  rw [u.ex_add, ← ex_prod]
  simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul,
    GrpObj.comp_zpow, MonObj.comp_one, hy, reassoc_of% e₀]

theorem theta_eq {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {al : Matrix (Fin 4) (Fin 4) ℤ} {m N : ℕ}
    (hth : u.IsFn x.th (thetaChar τ a b)) (bs : Fin N → RR x m) (Th : Fin N → (Fin g → ℂ) → ℂ)
    (hb : ∀ k, FnPw x u (bs k) (Th k)) (k n : Fin 4 → Fin g → ℤ) (ξ : Fin 4 → Pt x)
    (hξ : ∀ r, ξ r = u.ex (tors τ al m k n r))
    (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left)
      (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (C : ℂ)
    (hC : ∀ (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4), (∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) → ∀ j : Fin 4 ⊕ Fin 4 → x.P.L.ι, (∀ r, ⊤ ≤ (u.ex (∑ c, al r c • y c + tors τ al m k n r)).left ⁻¹ᵁ x.P.L.U (j (Sum.inl r))) → (∀ c, ⊤ ≤ (u.ex (y c)).left ⁻¹ᵁ x.P.L.U (j (Sum.inr c))) → valAt' pt.left (LB.wchart x.P.L (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) j) (w.s j).val * Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c) = C * ((∏ r, u.fr (j (Sum.inl r)) (∑ c, al r c • y c + tors τ al m k n r)) * ∏ c, u.fr (j (Sum.inr c)) (y c) ^ (-(m : ℤ))))
    (Q : (Fin 4 → Fin N) → ℂ)
    (hQ : ∀ (y : (Out.powObj x.P.A 4).left) J, Good x.P.L y J →
      ∏ r, gs (alMap x al r (ξ r)).left y _ (x.th.f (J (alMap x al r (ξ r)).left)) =
        (val w (𝟙 _) y J).val * ∑ I', gs (𝟙 _) y ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I')) *
          ∏ c, gs (Out.powPr x.P.A c).left y (x.P.L.U (J (Out.powPr x.P.A c).left))
            ((bs (I' c)).f (J (Out.powPr x.P.A c).left)))
    (y : Fin 4 → Fin g → ℂ) :
    simTheta τ a b al m k n y = ∑ I', (C * Q I') * ∏ c, Th (I' c) (y c) := by
  let pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4 := (Out.powIsLimit x.P.A 4).lift (Fan.mk _ fun c => u.ex (y c))
  have hy : ∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c) := fun c =>
    (Out.powIsLimit x.P.A 4).fac (Fan.mk _ fun c => u.ex (y c)) ⟨c⟩
  obtain ⟨p, hp⟩ : ∃ p : Sp ℂ ⟶ (Out.powObj x.P.A 4).left, p = pt.left := ⟨_, rfl⟩
  have e₁ : ∀ c, p ≫ (Out.powPr x.P.A c).left = (u.ex (y c)).left := fun c => by
    rw [hp]; exact congrArg (·.left) (hy c)
  have e₂ : ∀ r, p ≫ (alMap x al r (ξ r)).left = (u.ex (∑ c, al r c • y c + tors τ al m k n r)).left := fun r => by
    rw [hp, hξ]; exact congrArg (·.left) (comp_alMap x u al r _ y pt hy)
  obtain ⟨y₀, ev, hmem, hev⟩ := exists_ev p
  choose J hJ using fun ψ : (Out.powObj x.P.A 4).left ⟶ x.P.A.left => exists_chart x.P.isLB (ψ y₀)
  have m₁ : ∀ c, ⊤ ≤ (u.ex (y c)).left ⁻¹ᵁ x.P.L.U (J (Out.powPr x.P.A c).left) := fun c => by
    rw [← e₁]; exact (hmem _ _ _).1 (hJ _)
  have m₂ : ∀ r, ⊤ ≤ (u.ex (∑ c, al r c • y c + tors τ al m k n r)).left ⁻¹ᵁ
      x.P.L.U (J (alMap x al r (ξ r)).left) := fun r => by
    rw [← e₂]; exact (hmem _ _ _).1 (hJ _)
  have v₁ : ∀ r, ev (gs (alMap x al r (ξ r)).left y₀ _ (x.th.f (J (alMap x al r (ξ r)).left))) =
      thetaChar τ a b (∑ c, al r c • y c + tors τ al m k n r) *
        u.fr (J (alMap x al r (ξ r)).left) (∑ c, al r c • y c + tors τ al m k n r) := fun r => by
    rw [hev _ _ _ _ (hJ _), e₂]; exact hth _ _ (m₂ r)
  have v₂ : ∀ c i, ev (gs (Out.powPr x.P.A c).left y₀ (x.P.L.U (J (Out.powPr x.P.A c).left))
      ((bs i).f (J (Out.powPr x.P.A c).left))) = Th i (y c) * u.fr (J (Out.powPr x.P.A c).left) (y c) ^ m :=
    fun c i => (hev _ _ _ _ (hJ _)).trans (by rw [e₁]; exact hb i _ _ (m₁ c))
  have v₃ : ∀ q : ℂ, ev (gs (𝟙 _) y₀ ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ q)) = q := fun q => by
    refine (hev _ _ _ _ (Set.mem_univ _)).trans ?_
    rw [Category.comp_id]
    exact val_cst p _ (by rw [hp]; exact Over.w pt) q
  have v₄ : ev (val w (𝟙 _) y₀ J).val * Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c) =
      C * ((∏ r, u.fr (J (alMap x al r (ξ r)).left) (∑ c, al r c • y c + tors τ al m k n r)) *
        ∏ c, u.fr (J (Out.powPr x.P.A c).left) (y c) ^ (-(m : ℤ))) := by
    rw [ev_val hev w (𝟙 _) hJ (Sum.elim (fun r => J (alMap x al r (ξ r)).left) fun c => J (Out.powPr x.P.A c).left)
      (by rintro (r | c) <;> exact congrArg J (Category.id_comp _)) pt.left ((Category.comp_id _).trans hp)]
    exact hC y pt hy _ m₂ m₁
  have h := congrArg ev (hQ y₀ J hJ)
  simp only [map_prod, map_mul, map_sum, v₁, v₂, v₃, Finset.prod_mul_distrib] at h
  have n₁ : (∏ r, u.fr (J (alMap x al r (ξ r)).left) (∑ c, al r c • y c + tors τ al m k n r)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => u.fr_ne _ _ (m₂ r)
  have n₂ : (∏ c, u.fr (J (Out.powPr x.P.A c).left) (y c) ^ (-(m : ℤ))) *
      ∏ c, u.fr (J (Out.powPr x.P.A c).left) (y c) ^ m = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun c _ => ?_
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (u.fr_ne _ _ (m₁ c)))]
  simp only [← _root_.mul_assoc, ← Finset.sum_mul] at h
  apply mul_right_cancel₀ n₁
  simp only [_root_.mul_assoc C, ← Finset.mul_sum]
  rw [simTheta]
  generalize (∑ I' : Fin 4 → Fin N, Q I' * ∏ c, Th (I' c) (y c)) = S at h ⊢
  generalize (∏ r, u.fr (J (alMap x al r (ξ r)).left) (∑ c, al r c • y c + tors τ al m k n r)) = F₁ at *
  generalize (∏ c, u.fr (J (Out.powPr x.P.A c).left) (y c) ^ (-(m : ℤ))) = F₂ at *
  generalize (∏ c, u.fr (J (Out.powPr x.P.A c).left) (y c) ^ m) = F₃ at *
  generalize Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c) = e at *
  linear_combination e * h + S * F₃ * v₄ + C * F₁ * S * n₂

theorem rho_eq {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {al : Matrix (Fin 4) (Fin 4) ℤ} {m : ℕ} (hm : 1 ≤ m)
    (hrig : u.IsRig x.rig) (hlat : ∀ k n, lat τ k n ∈ u.Λ)
    (hfr : ∀ (k n : Fin g → ℤ) (i : x.P.L.ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i →
      u.fr i z = aut τ a b k n z * u.fr i (z + lat τ k n))
    (k n : Fin 4 → Fin g → ℤ) (ξ : Fin 4 → Pt x)
    (hξ : ∀ r, ξ r = u.ex (tors τ al m k n r))
    (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2])) (D : ℂ)
    (hD : ∀ (z : Fin g → ℂ) (j : Fin 2 → x.P.L.ι), ⊤ ≤ (u.ex ((m : ℤ) • z)).left ⁻¹ᵁ x.P.L.U (j 0) → ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (j 1) → valAt' (u.ex z).left (LB.wchart x.P.L ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] j) (mu.s j).val = D * (u.fr (j 0) ((m : ℤ) • z) * u.fr (j 1) z ^ (-(m : ℤ) ^ 2)))
    (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left)
      (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (C : ℂ)
    (hC : ∀ (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4), (∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) → ∀ j : Fin 4 ⊕ Fin 4 → x.P.L.ι, (∀ r, ⊤ ≤ (u.ex (∑ c, al r c • y c + tors τ al m k n r)).left ⁻¹ᵁ x.P.L.U (j (Sum.inl r))) → (∀ c, ⊤ ≤ (u.ex (y c)).left ⁻¹ᵁ x.P.L.U (j (Sum.inr c))) → valAt' pt.left (LB.wchart x.P.L (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) j) (w.s j).val * Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c) = C * ((∏ r, u.fr (j (Sum.inl r)) (∑ c, al r c • y c + tors τ al m k n r)) * ∏ c, u.fr (j (Sum.inr c)) (y c) ^ (-(m : ℤ))))
    (rho : ℂ)
    (hrho : ∀ (p : (𝟙_ (Over (Sp ℂ))).left) J, Good x.P.L p J →
      val mu (eSec x.P.A) p J = val x.rig (𝟙 _) p J ^ (1 - (m : ℤ) ^ 2) ∧
      (val w (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ r).left p J).val =
        gs (𝟙_ (Over (Sp ℂ))).hom p ⊤ (cst (𝟙 (Sp ℂ)) ⊤ rho) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val) :
    rho * ∏ r, aut τ a b (∑ c, al r c • k c) (∑ c, al r c • n c) 0 = C ^ (m ^ 2) := by
  obtain ⟨p, hp⟩ : ∃ p : Sp ℂ ⟶ (𝟙_ (Over (Sp ℂ))).left, p = 𝟙 (Sp ℂ) := ⟨_, rfl⟩
  have hp' : ∀ {X : Scheme.{0}} (f : (𝟙_ (Over (Sp ℂ))).left ⟶ X), p ≫ f = f := fun f => by
    rw [hp]; exact Category.id_comp f
  obtain ⟨y₀, ev, hmem, hev⟩ := exists_ev p
  choose J hJ using fun ψ : (𝟙_ (Over (Sp ℂ))).left ⟶ x.P.A.left => exists_chart x.P.isLB (ψ y₀)
  obtain ⟨h₁, h₂⟩ := hrho y₀ J hJ
  have mem : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (J (u.ex z).left) := fun z => by
    have := (hmem _ _ _).1 (hJ (u.ex z).left)
    rwa [hp'] at this
  have e0 : (u.ex 0).left = eSec x.P.A := by rw [CubeValues.ex_zero]; exact PowUnif.one_left
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have et : ∀ r, (m : ℤ) • tors τ al m k n r = lat τ (∑ c, al r c • k c) (∑ c, al r c • n c) := fun r => by
    rw [tors, lat_sum, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hmc, one_smul]
    simp only [lat_zsmul]
  have em : ∀ z, (u.ex z).left ≫ ((𝟙 x.P.A) ^ m).left = (u.ex ((m : ℤ) • z)).left := fun z => by
    rw [ex_zsmul, zpow_natCast, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]

  have vr : ev (val x.rig (𝟙 _) y₀ J).val = u.fr (J (u.ex 0).left) 0 := by
    rw [ev_val hev x.rig (𝟙 _) hJ (fun _ => J (u.ex 0).left)
      (fun _ => congrArg J ((Category.id_comp _).trans e0.symm)) (𝟙 (Sp ℂ)) ((Category.comp_id _).trans hp)]
    refine (hrig (fun _ => J (u.ex 0).left) fun q hq => Set.mem_iInter.2 fun _ => ?_).symm
    have := mem 0 hq
    rw [← e0]
    exact this
  have vm : ∀ z, u.ex ((m : ℤ) • z) = u.ex 0 → ev (val mu (u.ex z).left y₀ J).val =
      D * (u.fr (J (u.ex 0).left) ((m : ℤ) • z) * u.fr (J (u.ex z).left) z ^ (-(m : ℤ) ^ 2)) := fun z hz => by
    rw [ev_val hev mu (u.ex z).left hJ ![J (u.ex 0).left, J (u.ex z).left] (fun i => by
      fin_cases i
      · exact congrArg J ((em z).trans (congrArg (·.left) hz))
      · exact congrArg J (Category.comp_id _)) (u.ex z).left (hp' _)]
    exact hD z _ (by rw [hz]; exact mem 0) (mem z)
  have evz : ∀ (s : ((𝟙_ (Over (Sp ℂ))).left.presheaf.stalk y₀)ˣ) (i : ℤ), ev (s ^ i).val = ev s.val ^ i := fun s i => by
    have := congrArg Units.val (map_zpow (Units.map (ev : _ →* ℂ)) s i)
    rw [Units.val_zpow_eq_zpow_val] at this
    exact this
  have f0 : u.fr (J (u.ex 0).left) 0 ≠ 0 := u.fr_ne _ _ (mem 0)
  have hD1 : D = 1 := by
    have h := congrArg (fun s => ev (Units.val s)) h₁
    simp only [evz, vr] at h
    rw [← e0, vm 0 (by rw [smul_zero]), smul_zero, sub_eq_add_neg, zpow_add₀ f0, zpow_one] at h
    exact mul_right_cancel₀ (mul_ne_zero f0 (zpow_ne_zero _ f0)) (h.trans (_root_.one_mul _).symm)
  have vw : ev (val w (eSec (Out.powObj x.P.A 4)) y₀ J).val =
      C * ((∏ r, u.fr (J (u.ex (tors τ al m k n r)).left) (tors τ al m k n r)) *
        ∏ _c : Fin 4, u.fr (J (u.ex 0).left) 0 ^ (-(m : ℤ))) := by
    have hy : ∀ c : Fin 4, (1 : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4) ≫ Out.powPr x.P.A c =
        u.ex ((0 : Fin 4 → Fin g → ℂ) c) := fun c => by
      rw [MonObj.one_comp, Pi.zero_apply, CubeValues.ex_zero]
    have e1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4).left = eSec (Out.powObj x.P.A 4) := PowUnif.one_left
    have ez : ∀ r, ∑ c, al r c • (0 : Fin 4 → Fin g → ℂ) c + tors τ al m k n r = tors τ al m k n r := fun r => by
      simp
    rw [ev_val hev w (eSec (Out.powObj x.P.A 4)) hJ
      (Sum.elim (fun r => J (u.ex (tors τ al m k n r)).left) fun _ => J (u.ex 0).left) (by
        rintro (r | c)
        · refine congrArg J ?_
          have := congrArg (·.left) (comp_alMap x u al r (tors τ al m k n r) 0 1 hy)
          rw [ez, ← hξ] at this
          rw [← e1, ← hξ]
          exact this
        · refine congrArg J ?_
          rw [← e1]
          exact congrArg (·.left) (hy c)) (1 : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4).left ((hp' _).trans e1.symm)]
    have := hC 0 1 hy (Sum.elim (fun r => J (u.ex (tors τ al m k n r)).left) fun _ => J (u.ex 0).left)
      (fun r => by rw [ez]; exact mem _) (fun c => mem 0)
    simp only [ez, Pi.zero_apply, dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero, _root_.mul_one] at this
    simpa only [smul_zero, Finset.sum_const_zero, zero_add, Sum.elim_inl, Sum.elim_inr] using this
  have vc : ev (gs (𝟙_ (Over (Sp ℂ))).hom y₀ ⊤ (cst (𝟙 (Sp ℂ)) ⊤ rho)) = rho := by
    refine (hev _ _ _ _ (Set.mem_univ _)).trans ?_
    rw [hp']
    exact val_cst (𝟙 _) (𝟙 _) (Category.comp_id _) rho
  have vx : ∀ r, aut τ a b (∑ c, al r c • k c) (∑ c, al r c • n c) 0 * ev (val mu (ξ r).left y₀ J).val =
      u.fr (J (u.ex 0).left) 0 *
        (u.fr (J (u.ex (tors τ al m k n r)).left) (tors τ al m k n r) ^ (m ^ 2))⁻¹ := fun r => by
    rw [hξ, vm _ (by rw [et, (u.ker _).2 (hlat _ _), CubeValues.ex_zero]), hD1, _root_.one_mul, et,
      hfr (∑ c, al r c • k c) (∑ c, al r c • n c) _ 0 (mem 0), zero_add, zpow_neg, ← Nat.cast_pow, zpow_natCast,
      _root_.mul_assoc]
  have h := congrArg ev h₂
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, map_mul, map_pow, map_prod, evz, vr, vc, vw] at h
  have hx := Finset.prod_congr (s₁ := Finset.univ) rfl fun r _ => vx r
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_inv_distrib,
    Finset.prod_pow] at hx h
  have n₁ : (∏ r, u.fr (J (u.ex (tors τ al m k n r)).left) (tors τ al m k n r)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => u.fr_ne _ _ (mem _)
  generalize (∏ r, u.fr (J (u.ex (tors τ al m k n r)).left) (tors τ al m k n r)) = F at *
  generalize u.fr (J (u.ex 0).left) 0 = f at *
  generalize (∏ r, aut τ a b (∑ c, al r c • k c) (∑ c, al r c • n c) 0) = A at *
  generalize (∏ r, ev (val mu (ξ r).left y₀ J).val) = M at *
  have e : f ^ (4 - 4 * (m : ℤ) ^ 3) = ((f ^ (-(m : ℤ))) ^ 4) ^ (m ^ 2) * f ^ 4 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ f0]
    congr 1
    push_cast
    ring
  apply mul_right_cancel₀ (zpow_ne_zero (4 - 4 * (m : ℤ) ^ 3) f0)
  have hF : F ^ (m ^ 2) * (F ^ (m ^ 2))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ n₁)
  rw [mul_pow, mul_pow] at h
  rw [mul_right_comm, ← h, e]
  linear_combination (C ^ m ^ 2 * F ^ m ^ 2 * ((f ^ (-(m : ℤ))) ^ 4) ^ m ^ 2) * hx +
    (C ^ m ^ 2 * ((f ^ (-(m : ℤ))) ^ 4) ^ m ^ 2 * f ^ 4) * hF

omit x u in
theorem differentiableOn_prod {E K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Set E} (s : Finset K)
    {f : K → E → ℂ} (h : ∀ i ∈ s, DifferentiableOn ℂ (f i) W) : DifferentiableOn ℂ (fun e => ∏ i ∈ s, f i e) W := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).fun_mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit x u in
theorem mul_transpose_eq {al : Matrix (Fin 4) (Fin 4) ℤ} {m : ℕ} (hm : 1 ≤ m)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  first
  | exact @_root_.GlobalTheory.TransposeMulCommute.mul_transpose_eq_of_transpose_mul_eq
  | exact _root_.GlobalTheory.TransposeMulCommute.mul_transpose_eq_of_transpose_mul_eq
  | (apply _root_.GlobalTheory.TransposeMulCommute.mul_transpose_eq_of_transpose_mul_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TransposeMulCommute.mul_transpose_eq_of_transpose_mul_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TransposeMulCommute.mul_transpose_eq_of_transpose_mul_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TransposeMulCommute.mul_transpose_eq_of_transpose_mul_eq ..)

omit x u in

theorem eq_tors_add {τ : Matrix (Fin g) (Fin g) ℂ} {al : Matrix (Fin 4) (Fin 4) ℤ} {m : ℕ} (hm : 1 ≤ m)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (t : Fin 4 → Fin g → ℂ)
    (k n d e : Fin 4 → Fin g → ℤ)
    (h : ∀ c, ∑ r, al r c • t r = lat τ (k c + ∑ r, al r c • d r) (n c + ∑ r, al r c • e r)) (r : Fin 4) :
    t r = tors τ al m k n r + lat τ (d r) (e r) := by
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : ∀ c, lat τ (k c) (n c) = ∑ r, al r c • (t r - lat τ (d r) (e r)) := fun c => by
    simp only [smul_sub, Finset.sum_sub_distrib, h, lat_add, lat_sum, lat_zsmul, add_sub_cancel_right]
  have h2 : ∀ v : Fin 4 → Fin g → ℂ, ∑ c, al r c • ∑ r', al r' c • v r' = (m : ℂ) • v r := fun v => by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ r', ∑ c, (al r c * al r' c) • v r' = if r = r' then (m : ℤ) • v r' else 0 := fun r' => by
      have := congrFun (congrFun (mul_transpose_eq hm hal) r) r'
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
      rw [← Finset.sum_smul, this]
      split_ifs <;> simp
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  rw [tors]
  simp only [h1]
  rw [h2, smul_smul, inv_mul_cancel₀ hmc, one_smul, sub_add_cancel]

omit x u in

theorem l2Val_holomorphic : Out.Laws → ThetaUnifAV → ∀ (g m : ℕ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (Th : Fin (m ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ), charHalf g a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → LevBasis a b m Th → ∃ lam : (Fin g → Fin g → ℂ) → ℂ, DifferentiableOn ℂ lam (Key.phDom g) ∧ ∀ p ∈ Key.phDom g, ∀ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (bs : Fin (m ^ x.P.g) → RR x m) (la : ℂˣ), Wit x h u (per p) a b → (∀ k, FnPw x u (bs k) (Th (k.cast (by rw [h])) p)) → IsSquareDeterminantComparison x m al bs la → (la : ℂ) = lam p := by
  intro _ _ g m a b al Th hab hm hal hTh
  obtain ⟨k, n, hkn⟩ := GlobalTheory.T.exists_perm_representatives_mod_similitude g m al hm hal
  choose qa hqa hqa' using fun I => GlobalTheory.T.exists_holomorphic_coord_similitudeThetaProduct g m a b al Th hab hm hal hTh (k I) (n I)
  refine ⟨fun p => (Matrix.of fun I => qa I p).det ^ (2 * m ^ 2) /
    (∏ I, ∏ r, aut (per p) a b (∑ c, al r c • k I c) (∑ c, al r c • n I c) 0) ^ 2, ?_, ?_⟩
  · simp only [div_eq_mul_inv]
    refine DifferentiableOn.fun_mul (DifferentiableOn.fun_pow ?_ _) (DifferentiableOn.fun_inv
      (DifferentiableOn.fun_pow ?_ _) fun p _ => pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun I _ => Finset.prod_ne_zero_iff.2 fun r _ => aut_ne_zero _ _ _ _ _ _))
    · simp only [Matrix.det_apply', Matrix.of_apply]
      exact DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul
        (differentiableOn_prod _ fun I _ => hqa _ _) _
    · exact differentiableOn_prod _ fun I _ => differentiableOn_prod _ fun r _ =>
        ((GlobalTheory.T.thetaChar_level_one_and_holomorphic_parameter g a b hab).2.2 _ _ _).differentiableOn
  rintro p hp x h u bs la hW hb ⟨ξ, mu, w, Q, rho, hne, hker, hmu, hw, hnorm, hQ, hla⟩
  subst h
  have hlat : ∀ k n, lat (per p) k n ∈ u.Λ := fun k n => (hW.2.2.1 _).2 ⟨k, n, rfl⟩
  choose t ht using fun I r => u.ex_onto (ξ I r)
  have hk : ∀ I c, ∃ k' n', ∑ r, al r c • t I r = lat (per p) k' n' := fun I c => by
    refine (hW.2.2.1 _).1 ((u.ker _).1 ?_)
    rw [← ex_prod]
    simp only [ht]
    exact hker I c
  choose k' n' hk' using hk
  have hx : ∀ I (k n d e : Fin 4 → Fin x.P.g → ℤ), (∀ c, k' I c = k c + ∑ r, al r c • d r ∧ n' I c = n c + ∑ r, al r c • e r) →
      ∀ r, ξ I r = u.ex (tors (per p) al m k n r) := fun I k n d e h r => by
    rw [← ht, eq_tors_add hm hal (t I) k n d e (fun c => by rw [hk', (h c).1, (h c).2]) r,
      CubeValues.ex_add_period u _ _ (hlat _ _)]
  obtain ⟨σ, hσ⟩ := hkn k' n' (by
    rintro I I' hI ⟨d, e, h⟩
    obtain ⟨r, hr⟩ := hne I I' hI (IsLocalRing.closedPoint ℂ)
    exact hr (by rw [hx I _ _ d e h r, hx I' (k' I') (n' I') 0 0 (fun c => by simp) r]))
  have hξ : ∀ I r, ξ I r = u.ex (tors (per p) al m (k (σ I)) (n (σ I)) r) := fun I => by
    obtain ⟨d, e, h⟩ := hσ I
    exact hx I _ _ d e h
  obtain ⟨D, -, hD⟩ := GlobalTheory.T.theta_generator_pullback_mul_const_in_frames _ m x rfl u (per p) a b al hab hW hm hal mu hmu
  choose C _ hC using fun I => GlobalTheory.T.similitude_generator_eq_exp_in_frames _ m x rfl u (per p) a b al hab hW hm hal (k (σ I)) (n (σ I)) (ξ I) (hξ I) (w I) (hw I)
  have h₁ : ∀ I, (fun I' => C I * Q I I') = qa (σ I) p := fun I =>
    (hqa' (σ I) p hp _).1 (theta_eq x u hW.2.2.2.2.1 bs (fun i => Th i p) hb _ _ (ξ I) (hξ I) (w I) (C I) (hC I)
      (Q I) (hQ I))
  have h₂ := fun I => rho_eq x u hm hW.2.2.2.1 hlat (GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul _ x rfl u (per p) a b hab hW) _ _ (ξ I) (hξ I) mu D hD
    (w I) (C I) (hC I) (rho I) fun q J hJ => ⟨(hnorm q J hJ).1, (hnorm q J hJ).2 I⟩
  have h₃ : (∏ I, C I) * Q.det = Equiv.Perm.sign σ * (Matrix.of fun I => qa I p).det := by
    rw [← Matrix.det_mul_column, ← Matrix.det_permute]
    congr 1
    ext I I'
    exact congrFun (h₁ I) I'
  have h₄ : (Matrix.of fun I => qa I p).det ^ 2 = ((∏ I, C I) * Q.det) ^ 2 := by
    rw [h₃, mul_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h₅ := Finset.prod_congr (s₁ := Finset.univ) rfl fun I _ => h₂ I
  rw [Finset.prod_mul_distrib, Finset.prod_pow,
    Equiv.prod_comp σ fun I => ∏ r, aut (per p) a b (∑ c, al r c • k I c) (∑ c, al r c • n I c) 0] at h₅
  beta_reduce
  rw [eq_div_iff (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun I _ => Finset.prod_ne_zero_iff.2 fun r _ =>
    aut_ne_zero _ _ _ _ _ _)), hla, Finset.prod_pow, _root_.mul_assoc, ← mul_pow, h₅, pow_mul (Matrix.det (Matrix.of _)), h₄]
  ring

end GlobalTheory.SimilTheta
end
