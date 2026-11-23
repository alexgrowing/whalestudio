import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinearStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescentPowerIsoEndomorphismAbelianPartUniformizaStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiCompEndomorphismEqPowOfPullbackIsoStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.PsiPrim

theorem exists_norm_three {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (f : G ⟶ G) [IsMonHom f]
    (N : ℕ) (h : HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, f.left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) :
    ∃ β : LB.Gen (LB.LinComb Lr.L (K := Fin 3) ![𝟙 _, f.left, (1 : G ⟶ G).left]
      ![(N : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - N]), β.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ β (eSec G)) (LB.oneGen Lr.L) := by
  have h1 := h.add ((GlobalTheory.PullGenG.hasGen_one Lr).zsmul (((1 : ℕ) : ℤ) - N))
  obtain ⟨X0, hX0⟩ := h1.gen Lr.isLB (K' := Fin 3) ![𝟙 _, f.left, (1 : G ⟶ G).left]
      ![(N : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - N] (by
    simp only [fsum, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val, lf_single, Finsupp.smul_single_one,
      _root_.one_mul, Matrix.cons_val_zero, Matrix.cons_val_one])
  have hzp : eSec G ≫ (toUnit G).left = 𝟙 _ := by
    simp only [eSec, ← Over.comp_left]
    rw [show η[G] ≫ toUnit G = 𝟙 _ from toUnit_unique _ _]
    rfl
  obtain ⟨β, hβ, n⟩ := exists_normalized Lr.isLB _ _ X0 hX0 (toUnit G).left (eSec G) hzp (by
    have ha : eSec G ≫ f.left = eSec G := by
      simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
    have hb : eSec G ≫ (1 : G ⟶ G).left = eSec G := by
      show eSec G ≫ (toUnit G).left ≫ eSec G = _
      rw [← Category.assoc, hzp, Category.id_comp]
    simp only [fsum, Fin.sum_univ_three, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
      ha, hb, ← Finsupp.single_add]
    rw [show (N : ℤ) + -((1 : ℕ) : ℤ) + (((1 : ℕ) : ℤ) - N) = 0 by ring, Finsupp.single_zero])
  exact ⟨β, hβ, corr_one_of (fun j hj => n j hj)⟩

theorem star_smul_injective {O : Type} [CommRing O] [StarRing O] {X : Type} [AddCommGroup X] [Module O X]
    [Module.Free ℤ X] (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) {x y : X}
    (h : star a • x = star a • y) : x = y := by
  have h2 := congrArg (a • ·) h
  simp only [smul_smul, hN, Nat.cast_smul_eq_nsmul] at h2
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h3 : (N : ℤ) • (x - y) = 0 := by
    rw [smul_sub, natCast_zsmul, natCast_zsmul, h2, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_left hN0)

theorem exists_norm_form : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (w₀ : O), LBIso U.LG.L (cubeLB G ![𝟙 G, ιG.act w₀] U.LG.L) → ∀ (a : O) (N : ℕ), a * star a = (N : O) → 1 ≤ N →
    ∃ κ : LB.Gen (kapLB D.toPre (ιD.onB.act a) N 1), Normd κ ∧ ∀ y (z : (TK R).left) J, Good D.toPre.P.L z J →
      val (D.toPre.psi (a • y)) (𝟙 _) z J * rigV D.toPre (TK R).hom z J =
        val (D.toPre.psi y) (𝟙 _) z J ^ N * val κ (D.toPre.xK y) z J * rigV D.toPre (TK R).hom z J ^ N := by
  intro hL h1 h2 h3 h4 R _ _ _ I hI D A G _ _ hG U O _ _ _ ιD ιA ιG hlin hadj w₀ hprim a N hN hN1
  obtain ⟨E, eG, -, eB, eh, -⟩ := GlobalTheory.T.exists_uniformizationEndomorphism_of_linear hL R I hI D A G hG U O ιD ιA ιG hlin a
  obtain ⟨E', eG', -, -, eh', -⟩ := GlobalTheory.T.exists_uniformizationEndomorphism_of_linear hL R I hI D A G hG U O ιD ιA ιG hlin (star a)
  have hg := GlobalTheory.PullGenG.hasGen_pull U.LG U.cubG ιG w₀ a N hN (hadj a) hprim 1
  rw [← eG] at hg
  haveI := E.homG
  obtain ⟨β, hβ, nβ⟩ := exists_norm_three U.LG E.aG N hg
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E N 1 β hβ nβ
  have key := GlobalTheory.T.psi_comp_endomorphism_eq_pow_of_pullback_iso hL h1 h2 h3 h4 R I hI D A G hG U (AlgebraicClosure (FractionRing R)) E E'
    (by rw [eG, eG']; exact hadj a)
    (fun x y e => star_smul_injective a N hN hN1 (by rw [← eh, ← eh]; exact e)) N hN1
    (fun y => by rw [eh, eh', star_star, smul_smul, mul_comm, hN, Nat.cast_smul_eq_nsmul])
    (hg.gen U.LG.isLB _ _ (by rw [_root_.one_mul])) κ hκ
  rw [← eB]
  refine ⟨κ, hκ, fun y z J hJ => ?_⟩
  have := key y z J hJ
  rwa [eh', star_star] at this

theorem prod_kap {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (f : D.P.A ⟶ D.P.A) (N : ℕ) {U : Type} [CommGroup U]
    (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ i : Fin 3, h ((![𝟙 _, f.left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → _) i) ^
      (![(N : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - N] : Fin 3 → ℤ) i =
      h (𝟙 _) ^ (N : ℤ) * h f.left ^ (-((1 : ℕ) : ℤ)) * h (1 : D.P.A ⟶ D.P.A).left ^ (((1 : ℕ) : ℤ) - N) :=
  Fin.prod_univ_three _

theorem traceFormTwistIso_of_primitive_lineBundle : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (w₀ : O) (ν : ℕ), w₀ + star w₀ = 1 → w₀ * star w₀ = (ν : O) → 1 ≤ ν → Even ν → LBIso U.LG.L (cubeLB G ![𝟙 G, ιG.act w₀] U.LG.L) → TraceFormTwistIso D.toPre ιD w₀ := by
  intro hL h1 h2 h3 h4 R _ _ _ I hI D A G _ _ hG U O _ _ _ ιD ιA ιG hlin hadj w₀ ν htr hν hν1 _ hprim
  have H := exists_norm_form hL h1 h2 h3 h4 R I hI D A G hG U O ιD ιA ιG hlin hadj w₀ hprim
  obtain ⟨κ₀, ⟨g₀, n₀⟩, v₀⟩ := H w₀ ν hν hν1
  obtain ⟨κ₁, ⟨g₁, n₁⟩, v₁⟩ := H (1 + w₀) (ν + 2) (by
    rw [star_add, star_one]; push_cast; linear_combination htr + hν) (by omega)
  have e₁ : ιD.onB.act (1 + w₀) = padd D.toPre.P.A (𝟙 _) (ιD.onB.act w₀) := by
    rw [ιD.onB.map_add, ιD.onB.map_one]
  obtain ⟨u, hu, vu⟩ := exists_gen D.toPre.P.isLB (K' := Fin 4)
    (φ' := ![(padd D.toPre.P.A (𝟙 _) (ιD.onB.act w₀)).left, 𝟙 D.toPre.P.A.left, (ιD.onB.act w₀).left,
      (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left]) (ε' := ![1, -2, -1, 2]) (fun V _ h => by
      refine (prod_sum₂ (K := Fin 3) (K' := Fin 3) (U := V) _ (prod_kap D.toPre _ ν h)
        (prod_neg _ _ (prod_kap D.toPre _ (ν + 2) h))).trans ?_
      rw [Fin.prod_univ_four, e₁]
      have o : (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]) = 1 := rfl
      rw [o]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ κ₀ (LB.invGen D.toPre.P.L _ _ κ₁))
    (mulGen_isGen _ _ _ _ _ _ _ g₀ (invGen_isGen _ _ _ _ g₁))
  refine ⟨u, hu, corr_of_val D.toPre.P.isLB fun z J hJ => ?_, fun y => corr_of_val D.toPre.P.isLB fun z J hJ => ?_⟩
  · have a₀ := val_corr hJ n₀ (𝟙 _)
    have a₁ := val_corr hJ n₁ (𝟙 _)
    rw [val_pull hJ] at a₀ a₁
    rw [val_pull hJ, vu _ _ z J hJ, val_mul hJ, val_inv, a₀, a₁, mul_inv_cancel, val_one]
  · have t : val (D.toPre.tau y (w₀ • y)) (𝟙 _) z J = val (D.toPre.psi (y + w₀ • y)) (𝟙 _) z J *
        (val (D.toPre.psi y) (𝟙 _) z J)⁻¹ * (val (D.toPre.psi (w₀ • y)) (𝟙 _) z J)⁻¹ * (val D.toPre.rigK (𝟙 _) z J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have r : val D.toPre.rigK (𝟙 _) z J = rigV D.toPre (TK R).hom z J :=
      (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)
    have b₀ := v₀ y z J hJ
    have b₁ := v₁ y z J hJ
    rw [add_smul, one_smul] at b₁
    rw [val_mul hJ, val_mul hJ, val_pull hJ, Category.id_comp, vu _ _ z J hJ, val_mul hJ, val_inv, t, r]
    apply Additive.ofMul.injective
    have c₀ := congrArg Additive.ofMul b₀
    have c₁ := congrArg Additive.ofMul b₁
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at c₀ c₁ ⊢
    linear_combination (norm := module) c₁ - c₀

end GlobalTheory.PsiPrim

end
