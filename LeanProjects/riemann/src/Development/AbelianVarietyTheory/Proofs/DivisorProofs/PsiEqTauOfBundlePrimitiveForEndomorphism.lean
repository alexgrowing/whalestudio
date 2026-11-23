import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePsiW0
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LinearUniformisationTorsionMapIsLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaOfField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWFinal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaElementLevelFourSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleSymmetricPullbackOfUniformisatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySignsTwoTorsionRelationOfLbIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEqTauFromSignRelationFourTorsionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PsiSign
open GlobalTheory.UT.SymFrame GlobalTheory.UT.PsiPull GlobalTheory.UT.CoefBasic

section Canon
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem toHas {Y : Over (Spec (CommRingCat.of R))} {P v} (h : GRep D.P.L Y P v) : GlobalTheory.SymFrame.HasGen D.P.L Y P v := h

theorem val_double (hG : GlobalFnsSt) {a : D.P.A ⟶ D.P.A} (ha : a = 𝟙 D.P.A ^ 2) {x y : D.X} (hx : x = 2 • y)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) x) (D.Oφ a y)) (Sum.elim Oε Oinvε))) (hu : Normd u)
    {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u b.left z J * th D z J (cP D T y) b b * (th D z J (cP D T y) (cP D T y) b)⁻¹ = 1 := by
  subst ha hx
  have ru : GRep D.P.L D.P.A _ (fun _ r z J => val u r.left z J) :=
    ⟨_, inferInstance, _, _, u, hu.1, fun U _ h => prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
      (prod_O (𝟙 _) (2 • y) h) (prod_Oinv (𝟙 D.P.A ^ 2) y h), fun _ _ _ _ _ => rfl⟩
  have key := ((ru.mul (grep_cub (cP D _ y) (𝟙 _) (𝟙 _))).mul (grep_cub (cP D _ y) (cP D _ y) (𝟙 _)).inv).triv hG
    (fun U _ h => by
      rw [cPoint_nsmul, pow_two, pow_two, mul_comm (𝟙 D.P.A) (cP D D.P.A y * cP D D.P.A y),
        mul_comm (𝟙 D.P.A * 𝟙 D.P.A) (cP D D.P.A y), ← _root_.mul_assoc (cP D D.P.A y) (𝟙 _) (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    (fun w I hI => by
      have C : IsCub (cubV D.cub (T := 𝟙_ _) w I) := isCub_cubV D.cub hI
      beta_reduce
      rw [Category.comp_id, normd_one hu hI, C.face₃, C.face₃]
      simp) T b z J hJ
  beta_reduce at key
  rwa [comp_cP, Category.comp_id] at key

theorem exists_gam (hG : GlobalFnsSt) {a : D.P.A ⟶ D.P.A} (ha : a = 𝟙 D.P.A ^ 2) (κ : LB.Gen (kapLB D a 4 1))
    (hκ : Normd κ) (ν : LB.Gen (nuLB D 4)) (hν : Normd ν) :
    ∃ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (g b : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        th D z J (g ^ 4) (g ^ 4) b * (th D z J (g ^ 4) b b)⁻¹ * val κ b.left z J * val gam g.left z J =
          val κ (b * g * g).left z J * cubN (th D z J) 4 1 g (b * g) * cubN (th D z J) 4 (g ^ 4) g b *
            (th D z J (g ^ 4) b g)⁻¹ * val ν g.left z J := by
  subst ha
  obtain ⟨gam, hgam, -⟩ := (((grep_kap (n := 2) κ hκ.1 (𝟙 D.P.A ^ 2)).mul (grep_cubN (𝟙 _) (𝟙 _) 4)).mul
    (grep_nu ν hν.1 (𝟙 _))).normd
    ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3] (fun U _ h => by
      rw [Fin.prod_univ_four, ← pow_mul, ← pow_succ, ← pow_two (𝟙 D.P.A)]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) (fun w I hI => by
      have C : IsCub (cubV D.cub (T := 𝟙_ _) w I) := isCub_cubV D.cub hI
      beta_reduce
      rw [comp_id_pow, one_pow, Category.comp_id, normd_one hκ hI, normd_one hν hI, C.N_one]
      simp)
  refine ⟨gam, hgam, fun T g b z J hJ => ?_⟩
  let β : D.P.A ⊗ D.P.A ⟶ D.P.A := fst _ _
  let ξ : D.P.A ⊗ D.P.A ⟶ D.P.A := snd _ _
  have rg : GRep D.P.L (D.P.A ⊗ D.P.A) (fun _ _ h => h (β ^ 5).left ^ (2 : ℤ) * h (β ^ 4).left ^ (-3 : ℤ) *
      h β.left ^ (-2 : ℤ) * h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left ^ (3 : ℤ)) (fun _ r z J => val gam (r ≫ β).left z J) :=
    (grep_gen gam hgam.1 β.left).congr (fun _ _ h => by
      rw [Fin.prod_univ_four, ← left_pow β 5, ← left_pow β 4, ← left_one β]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Category.comp_id]) (fun _ _ _ _ _ => rfl)
  have H := (toHas ((((grep_cub (β ^ 4) (β ^ 4) ξ).mul (grep_cub (β ^ 4) ξ ξ).inv).mul
    (grep_kap (n := 2) κ hκ.1 ξ)).mul rg)).unique D.P.isLB
    ((((toHas ((grep_kap (n := 2) κ hκ.1 (ξ * β * β)).mul (grep_cubN β (ξ * β) 4))).mul
      (GlobalTheory.SymFrame.hasGen_cubN D.cub (β ^ 4) β ξ 4)).mul (toHas (grep_cub (β ^ 4) ξ β).inv)).mul
      (toHas (grep_nu ν hν.1 β)))
    (fun U _ h => by
      have a₁ : (ξ * β * β) ^ 2 = β ^ 4 * ξ * ξ := by
        apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_pow]; module
      have a₂ : β ^ 4 * (ξ * β) = β ^ 4 * ξ * β := (_root_.mul_assoc _ _ _).symm
      have a₃ : β * (ξ * β) = ξ * β * β := mul_comm _ _
      rw [a₁, a₂, a₃, mul_comm β ξ, pow_succ β 4, pow_two ξ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      push_cast
      module)
    (by
      rw [← Over.w (snd D.P.A D.P.A)]
      exact surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) (lift 1 1) (fun y I hI => by
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      simp only [β, ξ, MonObj.comp_mul, MonObj.comp_pow, lift_fst, lift_snd,
        _root_.mul_one, inv_one, one_pow, C.face, C.N_one, normd_one hν hI, normd_one hκ hI, normd_one hgam hI])
    T (lift g b) z J hJ
  simpa only [β, ξ, MonObj.comp_mul, MonObj.comp_pow, lift_fst, lift_snd] using H

end Canon

theorem pull_val : AllUF fun {R} _ _ {_} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre),
    Function.Injective E.h → ∀ ν : ℕ, 1 ≤ ν →
    (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(ν : ℤ), -((1 : ℕ) : ℤ)]), β.IsGen) →
    ∀ κ : LB.Gen (kapLB D.toPre E.aB ν 1), Normd κ → ∀ w₀ : W0 U.toUnifPre, w₀.IsGen →
    ∃ α : LB.Gen (LB.LinComb A.L (K := Fin 2)
      ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ≫ E.aA).left] ![(ν : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen ∧
      ∀ (t : SecA A F 1) (t' : SecA A F ν) s s', U.ExpandsF F 1 w₀ t s → U.ExpandsF F ν w₀ t' s' →
      IsTwistPull A.A A.L (lift (fst _ _) (snd (TFK (R := R) F) A.A ≫ E.aA)) _ (lift_snd _ _) ν (1 : ℕ) α t t' →
      ∀ χ (b : TF (R := R) F ⟶ D.toPre.P.A) (z : (TF (R := R) F).left) J, Good D.toPre.P.L z J →
        sval (s'.s (E.h χ)) (lift (𝟙 (TF (R := R) F)) b).left z J * (rigV D.toPre (TF (R := R) F).hom z J).val =
          sval (s.s χ) (lift (𝟙 (TF (R := R) F)) (b ≫ E.aB)).left z J *
            (val (E.u χ) b.left z J * val κ b.left z J * rigV D.toPre (TF (R := R) F).hom z J ^ ν).val := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ E hE ν hν ⟨β, hβ⟩ κ hκ w₀ hw
  have hL := GlobalTheory.firstFiveLaws
  have := E.homA
  obtain ⟨ρ, hw₀⟩ := GlobalTheory.SymFrame.exists_normW U.toUnifPre w₀ hw
  obtain ⟨α₀, hα₀⟩ := exists_gen_generic E _ _ β hβ (TFK (R := R) F)
  obtain ⟨α, hα, hαn⟩ := exists_normalised A.isLB hw₀.2.1 (snd (TFK (R := R) F) A.A ≫ E.aA) (by
    rw [← Over.comp_left, ptSecT, lift_snd_assoc, MonObj.one_comp]; rfl) _ _ α₀ hα₀
  refine ⟨α, hα, fun t t' s s' ht ht' htt χ b z J hJ => ?_⟩
  have H := (GlobalTheory.T.expansion_pullback_section_endomorphism hL R I hI D A G hG U F E hE ν 1 le_rfl hν ⟨β, hβ⟩).2 w₀ ρ hw₀ _ _ (lift_snd _ _) (lift_fst _ _)
    rfl α hα hαn t t' s s' ht ht' htt κ hκ
  obtain ⟨g, rfl⟩ := (gt_onto_divisible_kernel hL R I hI D F).1 b
  obtain ⟨g', hg', -⟩ := (GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hI D A G hG U F E E E).1 g
  obtain ⟨w', hw'⟩ := (coef_basic R D.toPre F ν g).1
  obtain ⟨w, hw, hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F g'.b) (ε' := DegPre.lineε 1)
    (fun V _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 3) (U := V) _ (prod_line ν g.b h) (prod_kap g.b E.aB ν h)).trans ?_
      rw [prod_line, hg'.1]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ w' (LB.pullGen D.toPre.P.L _ _ κ g.b.left))
    (mulGen_isGen _ _ _ _ _ _ _ hw' (pullGen_isGen _ _ _ _ hκ.1 _))
  have hww : ∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J := fun z J hJ => by
    rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, Category.id_comp]
  have a₁ := isCoef_coef g hw' (E.h χ) s' z J hJ
  have a₂ := isCoef_coef g' hw χ s z J hJ
  rw [(H g g' hg' w' w hw' hw hww).1 χ] at a₁
  rw [← hww z J hJ, hg'.2 χ z J hJ, pow_one] at a₂
  rw [← hg'.1]
  refine (Units.mul_left_inj (val (g.s (E.h χ)) (𝟙 _) z J * val w' (𝟙 _) z J)).1 ?_
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at a₂ ⊢
  linear_combination (rigV D.toPre (TF (R := R) F).hom z J).val ^ ν * a₂ -
    (rigV D.toPre (TF (R := R) F).hom z J).val * a₁

theorem alg_units {M : Type} [CommRing M] {s p₀ p₁ p₂ p₃ q : M} (hs : IsUnit s) {l r a u k₀ k₁ n₁ n₂ w y : Mˣ}
    (h₁ : p₁ = p₀ * (n₁ * w).val) (h₂ : p₂ = p₁ * (n₂ * (y * w)).val) (h₃ : p₂ = l.val * p₃)
    (h₄ : p₃ * r.val = q * (u * k₀ * r ^ 4).val) (h₅ : q = s * (a * r).val) (h₆ : p₀ * r.val = s * (k₁ * r ^ 4).val) :
    l * (a * r) * (u * k₀) = k₁ * n₁ * n₂ * y * w ^ 2 := by
  obtain ⟨s, rfl⟩ := hs
  have e := congrArg (· * r.val) h₃
  beta_reduce at e
  rw [_root_.mul_assoc l.val, h₄, h₅, h₂, h₁, mul_right_comm, mul_right_comm p₀, h₆] at e
  simp only [← Units.val_mul, Units.val_inj] at e
  apply Additive.ofMul.injective
  have b := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_pow] at b ⊢
  linear_combination (norm := module) -b

theorem sign_eq : AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∃ gam : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4) ![(𝟙 D.toPre.P.A ^ 5).left, (𝟙 D.toPre.P.A ^ 4).left, 𝟙 _, (1 : D.toPre.P.A ⟶ D.toPre.P.A).left] ![2, -3, -2, 3]), Normd gam ∧ ∀ (p : QkPt D.toPre F 4) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F 4 p x → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∀ (z : (TF (R := R) F).left) JA J, Good A.L (Z := (TFK (R := R) F).left) z JA → Good D.toPre.P.L z J → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val σ (x ^ 2).left z JA) * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi (p.y)) (jFK (R := R) F) z J) * rigV D.toPre (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _
  have hL := GlobalTheory.firstFiveLaws
  have hGF := hL.1.globalFns
  have := hI.1
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  obtain ⟨E, eG, eA, eB, eh, -⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U).1 2
  have := E.homB
  have hE : Function.Injective E.h := fun a b e => by
    rw [eh, eh] at e
    have h : (2 : ℤ) • (a - b) = 0 := by rw [smul_sub, two_smul, two_smul, ← two_nsmul, ← two_nsmul, e, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h).resolve_left two_ne_zero)
  have hβ : ∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]),
      β.IsGen := by
    rw [eG]; exact exists_gen_mulPull_pow_unif R I D A G U.toUnifPre 2 1 4 rfl
  obtain ⟨κ, hκ⟩ := (GlobalTheory.T.expansion_pullback_section_endomorphism hL R I hI D A G hG U F E hE 4 1 le_rfl (by omega) hβ).1
  obtain ⟨ν, hν⟩ := exists_nu (D := D.toPre) hL.1.mulPull 4
  obtain ⟨gam, hgam, canon⟩ := exists_gam hGF eB κ hκ ν hν
  refine ⟨gam, hgam, fun p x hx σ hσ nσ z JA J hJA hJ => ?_⟩
  have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨h4, hx'⟩ := hx w₀ hw₀
  obtain ⟨θ, hθ, hsym, c, hc, hsq⟩ := GlobalTheory.T.exists_symmetric_thetaElement_level_four_square R A F x h4 σ hσ nσ
  obtain ⟨w, hw, hΦ⟩ := hx' θ hθ
  have sq := GlobalTheory.SymFrame.sq_frame_of_symmetric hL R I hI D A G hG U F 4 (by omega) p θ w₀ w hw₀ hw hΦ hsym ν hν z J hJ
  obtain ⟨α, hα, pull⟩ := pull_val R I hI D A G hG U F E hE 4 (by omega) hβ κ hκ w₀ hw₀
  obtain ⟨bij, lin⟩ := expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D.toPre) (F := F) hGF hL.2.1.secTwist D.tau_bimult le_rfl 0
  obtain ⟨v, j, hv, hu⟩ := exists_torsion_ne_zero hL.1 (s.s 0) ((hs 0).2 ⟨0, by simp⟩) (l := 4 + 1) (by omega)
  obtain ⟨b₁, rfl⟩ := exists_comp_eq hL.1 E.aB (by omega) κ hκ.1 (Nat.one_le_pow _ _ (by omega))
    (Nat.Coprime.pow_left j (by norm_num)) v hv
  obtain ⟨b, rfl⟩ : ∃ b, b * p.g.b * p.g.b = b₁ := ⟨b₁ * p.g.b⁻¹ * p.g.b⁻¹, by simp⟩
  obtain ⟨t, ht, -⟩ := (bij F 1 le_rfl w₀ hw₀).2 s
  obtain ⟨t₁, h₁⟩ := GlobalTheory.SymFrame.exists_twist A.A A.isLB (ψ := lift (fst _ _) (snd (TFK (R := R) F) A.A ≫ E.aA))
    (hm := lift_snd _ _) hα t
  obtain ⟨t₂, h₂⟩ := ThetaNu.exists_isActOf A.isLB θ t₁
  obtain ⟨t₃, h₃⟩ := ThetaNu.exists_isActOf A.isLB θ t₂
  obtain ⟨ts, -⟩ := bij F 4 (by omega) w₀ hw₀
  obtain ⟨s₁, hs₁, -⟩ := ts t₁
  obtain ⟨s₂, hs₂, -⟩ := ts t₂
  obtain ⟨s₃, hs₃, -⟩ := ts t₃
  have e := hsq _ _ (lift_snd _ _) (lift_fst _ _) (by rw [eA, MonObj.comp_pow, Category.comp_id]) α hα t t₁ t₂ t₃ h₁ h₂ h₃
  have z₀ : U.ExpandsF F 4 w₀ SecOps.secZero ((-1 : F) • s₁ + s₁) := lin F 4 w₀ t₁ t₁ _ s₁ s₁ (-1) hs₁ hs₁ fun j => by
    rw [map_neg, map_one, liftFun, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_add_cancel]; rfl
  have e₃ : s₃ = c • s₁ := by
    have := (ts t₃).unique hs₃ (lin F 4 w₀ t₁ _ t₃ s₁ _ c hs₁ z₀ fun j => (e j).trans (add_zero _).symm)
    rwa [neg_one_smul, neg_add_cancel, add_zero] at this
  have cy : cP D.toPre (TF (R := R) F) p.y = p.g.b ^ 4 := cPoint_y p
  have a₁ := GlobalTheory.SymFrame.phi_at hGF p w hw (hΦ _ _ _ _ hs₁ hs₂ h₂) 0 p.y (zero_add _) (b * p.g.b) z hJ
  have a₂ := GlobalTheory.SymFrame.phi_at hGF p w hw (hΦ _ _ _ _ hs₂ hs₃ h₃) p.y (E.h p.y) (by rw [eh, two_nsmul]) b z hJ
  have a₃ : sval (s₃.s (E.h p.y)) (lift (𝟙 (TF (R := R) F)) b).left z J =
      (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val σ (x ^ 2).left z JA)).val *
        sval (s₁.s (E.h p.y)) (lift (𝟙 (TF (R := R) F)) b).left z J := by
    rw [e₃, sval_smul _ _ _ _ z hJ, ← Over.comp_left, lift_fst]
    exact congrArg₂ (· * ·) (hc z JA hJA).symm rfl
  have a₄ := pull t t₁ s s₁ ht hs₁ h₁ p.y b z J hJ
  have a₅ := fe_zero hGF D.tau_bimult s p.y (one_nsmul _).symm (b ≫ E.aB) z J hJ
  have a₆ := pull t t₁ s s₁ ht hs₁ h₁ 0 (b * p.g.b * p.g.b) z J hJ
  have e₀ : ∀ χ, χ = 0 → ∀ r : (TF (R := R) F).left ⟶ _, sval (s₁.s χ) r z J = sval (s₁.s 0) r z J := by
    rintro _ rfl _; rfl
  have eb : (b ≫ E.aB) * cP D.toPre (TF (R := R) F) p.y = (b * p.g.b * p.g.b) ≫ E.aB := by
    rw [cy, eB, comp_id_pow, comp_id_pow]
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_pow]; module
  rw [e₀ _ (map_zero E.h), val_twist_zero hGF E.aB (map_zero E.h) (E.u 0) (E.u_norm 0) _ z J hJ, _root_.one_mul] at a₆
  rw [eb, cubN, Finset.prod_range_one, pow_zero, _root_.mul_one, C.face, _root_.one_mul, pow_one] at a₅
  have z₁ : val (p.g.s 0) (𝟙 _) z J = 1 := TorusExt.charVal_zero p.g hJ
  rw [cPoint_zero, C.face, inv_one, _root_.mul_one, z₁, _root_.one_mul] at a₁
  rw [cy] at a₂
  have k₁ := alg_units (hu z J hJ) a₁ a₂ a₃ a₄ a₅ a₆
  have k₂ := val_double hGF eB (eh p.y) (E.u p.y) (E.u_norm _) b z J hJ
  have k₃ := canon _ p.g.b b z J hJ
  rw [cy] at k₂
  apply Additive.ofMul.injective
  have b₀ := congrArg Additive.ofMul sq
  have b₁ := congrArg Additive.ofMul k₁
  have b₂ := congrArg Additive.ofMul k₂
  have b₃ := congrArg Additive.ofMul k₃
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at b₀ b₁ b₂ b₃ ⊢
  linear_combination (norm := module) b₁ + b₀ - b₂ - b₃

theorem corr_of_ext {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] {X : Scheme.{0}}
    {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((TK R).left ⟶ X)} {ε : K → ℤ}
    {φ' : K' → ((TK R).left ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (h : ∀ (z : Spec (CommRingCat.of F)) J, Good L z J → val t (jFK (R := R) F) z J = val t' (jFK (R := R) F) z J) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  refine corr_of_val hL fun z J hJ => ?_
  obtain ⟨z'⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  obtain rfl : z = jFK (R := R) F z' := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
  let ρ := jFK (R := R) F
  have : Surjective ρ := ⟨fun x => ⟨z', Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _⟩⟩
  have : Flat ρ := inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))))
  have : Epi ρ := Flat.epi_of_flat_of_surjective ρ
  obtain ⟨J', hJ', e⟩ := exists_good L hL (Z := Spec (CommRingCat.of F)) z'
    (fun ψ : (TK R).left ⟶ X => ρ ≫ ψ) J (fun a b e => congrArg J ((cancel_epi ρ).1 e)) (fun ψ => hJ ψ)
  obtain rfl : (fun ψ => J' (ρ ≫ ψ)) = J := funext e
  have hinj : Function.Injective (ρ.stalkMap z').hom := by
    let _ := (ρ.stalkMap z').hom.toAlgebra
    have : Module.Flat ((TK R).left.presheaf.stalk (ρ z')) ((Spec (CommRingCat.of F)).presheaf.stalk z') :=
      Flat.stalkMap ρ z'
    have : IsLocalHom (algebraMap ((TK R).left.presheaf.stalk (ρ z')) ((Spec (CommRingCat.of F)).presheaf.stalk z')) :=
      inferInstanceAs (IsLocalHom (ρ.stalkMap z').hom)
    have : Module.FaithfullyFlat ((TK R).left.presheaf.stalk (ρ z')) ((Spec (CommRingCat.of F)).presheaf.stalk z') :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective ((TK R).left.presheaf.stalk (ρ z')) _
  exact Units.ext (hinj ((EvalZero.val_comp_map t ρ (𝟙 _) ρ (Category.comp_id _) z' hJ').symm.trans
    ((congrArg Units.val (h z' J' hJ')).trans (EvalZero.val_comp_map t' ρ (𝟙 _) ρ (Category.comp_id _) z' hJ'))))

theorem exists_act : AllUF fun {R} _ _ {_} {D} {A} {G} _ _ U F _ _ => ∀ (O : Type) [CommRing O] [StarRing O]
    [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG →
    (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L)) →
    ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F k p x → ∀ a : O,
      ∃ q : QkPt D.toPre F k, q.y = a • p.y ∧ GtAct o a p.g q.g ∧ QkToAkU U.toUnifPre F k q (x ≫ oA.act a) := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ O _ _ _ o oA oG hlin hadj k hk p x hx a
  have hL := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange
  obtain ⟨E, eG, eA, -, -, eact⟩ := GlobalTheory.T.exists_uniformizationEndomorphism_of_linear hL R I hI D A G hG U O o oA oG hlin a
  obtain ⟨E', eG', -, -, eh', -⟩ := GlobalTheory.T.exists_uniformizationEndomorphism_of_linear hL R I hI D A G hG U O o oA oG hlin (star a)
  obtain ⟨b₁, b₂⟩ := GlobalTheory.T.uniformisation_adjoint_endomorphisms_commute hL (twistBCSpan_of hT) TWM.vRatioGt (TWM.tw_of_laws hL.1 hT) (UUA.uu hL.1 hT) R I hI D A G hG U F E E'
    (by rw [eG, eG']; exact hadj a)
  obtain ⟨ex, add, -⟩ := GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hI D A G hG U F E E E
  choose f hf _ using ex
  letI := TorusExt.gtGroup D.toPre F
  let φ : GtPtF D.toPre F →+ GtPtF D.toPre F := AddMonoidHom.mk' f fun g g' =>
    (TorusExt.isAdd_iff_eq _ _ _).1 (add g g' _ _ _ _ ((TorusExt.isAdd_iff_eq _ _ _).2 rfl) (hf _) (hf _) (hf _))
  obtain ⟨h, hn, hι⟩ := p.eq
  let q : QkPt D.toPre F k := ⟨E'.h p.y, f p.g, f h, (TorusExt.isNsmul_iff_eq _ _ _).2 (by
    rw [(TorusExt.isNsmul_iff_eq _ _ _).1 hn]; exact map_nsmul φ k p.g), b₁ _ _ _ hι (hf h)⟩
  exact ⟨q, (eh' _).trans (by rw [star_star]), (eact F _ _).1 (hf _), eA ▸ b₂ k hk p q x rfl (hf _) hx⟩

theorem psi_eq_tau_of_bundle_primitive_for_endomorphism : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L)) → ∀ w : O, w + star w = 1 → LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → TraceFormTwistIso D.toPre o w := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin hadj w hw hprim
  have := hR.2
  have hL := GlobalTheory.firstFiveLaws
  have := o.onB.hom w
  have := oA.hom w
  let F := AlgebraicClosure (FractionRing R)
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.polarisationBundle_symmetric_pullback_of_uniformisation R _ hR.1 D A G hG U O o oA oG hlin w hprim
  obtain ⟨u, hu, hn⟩ := GlobalTheory.PsiRescale.exists_normalised D.toPre.P.isLB (o.onB.act w) u₀ hu₀
  obtain ⟨σ, hσ, nσ, vσ⟩ := GlobalTheory.T.symmetry_signs_two_torsion_relation_of_lbIso R _ hR.1 D A G hG U O o oA oG hlin w hprim
  obtain ⟨gam, hgam, key⟩ := sign_eq R _ hR.1 D A G hG U F
  refine ⟨u, hu, hn, fun y => corr_of_ext F D.toPre.P.isLB _ _ fun z J hJ => ?_⟩
  obtain ⟨h, hh⟩ := TorusExt.exists_iota (F := F) D.tau_bimult y
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL R _ hR.1 D F).2.1 4 (by omega) h
  let p : QkPt D.toPre F 4 := ⟨y, g, h, hg, hh⟩
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL R _ hR.1 D A G hG U F 4 (by omega)
  have hx := (hf p _).2 rfl
  obtain ⟨q, qy, qg, hq⟩ := exists_act R _ hR.1 D A G hG U F O o oA oG hlin hadj 4 (by omega) p _ hx w
  obtain ⟨r, ry, rg, hr⟩ := exists_act R _ hR.1 D A G hG U F O o oA oG hlin hadj 4 (by omega) p _ hx (1 + w)
  obtain ⟨w₀, hw₀⟩ := U.ext
  have h4 : f p ^ 4 = 1 := (hx w₀ hw₀).1
  obtain ⟨JA, hJA⟩ := GlobalTheory.UU.exists_good_pt A.isLB (Z := (TFK (R := R) F).left) z
  have e₁ : (f p ≫ oA.act w) ^ 2 = (f p ^ 2) ≫ oA.act w := by rw [pow_two, pow_two, MonObj.mul_comp]
  have e₂ : (f p ≫ oA.act (1 + w)) ^ 2 = (f p ^ 2) * ((f p ^ 2) ≫ oA.act w) := by
    rw [oA.map_add, oA.map_one, ← e₁, ← mul_pow]
    exact congrArg (· ^ 2) ((MonObj.comp_mul _ _ _).trans (congrArg₂ (· * ·) (Category.comp_id _) rfl))
  have h2 : (f p ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h4
  have hv := vσ (TFK (R := R) F) (f p ^ 2) h2 z JA hJA
  rw [← e₂, ← e₁] at hv
  have H := GlobalTheory.T.psi_eq_tau_from_sign_relation_four_torsion R D.toPre F O o w hw u ⟨hu, hn⟩ gam hgam p q r qy ry qg rg z J hJ _ _ _
    (key p _ hx σ hσ nσ z JA J hJA hJ) (key q _ hq σ hσ nσ z JA J hJA hJ) (key r _ hr σ hσ nσ z JA J hJA hJ) hv
  have r₁ : val D.toPre.rigK (jFK (R := R) F) z J = rigV D.toPre (TF (R := R) F).hom z J := val_pull hJ _ _ _
  have r₂ : jFK (R := R) F ≫ D.toPre.xK y = (cP D.toPre (TF (R := R) F) y).left := (Category.assoc _ _ _).symm
  rw [val_mul hJ, val_mul hJ, val_pull hJ, r₁, r₂]
  exact H

end GlobalTheory.PsiSign
end
