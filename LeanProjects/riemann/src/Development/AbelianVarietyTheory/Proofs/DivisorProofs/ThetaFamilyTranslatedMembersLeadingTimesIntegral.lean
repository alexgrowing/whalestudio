import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ThFam

theorem prod_famB {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
    (ρ : T ⟶ D.P.A) (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (ρ.left ≫ D.famφB α i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (DVR.cP D T α * ρ).left * (h (DVR.cP D T α).left)⁻¹ *
        h (1 : T ⟶ D.P.A).left := by
  have e₀ : ρ.left ≫ D.famφB α 0 = ρ.left := Category.comp_id _
  have e₁ : ρ.left ≫ D.famφB α 1 = (DVR.cP D T α * ρ).left := by
    have : ρ ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α) = DVR.cP D T α * ρ := by
      show ρ ≫ (𝟙 _ * DVR.cP D D.P.A α) = _
      rw [MonObj.comp_mul, Category.comp_id, DVR.comp_cP, mul_comm]
    exact congrArg (fun q => q.left) this
  have e₂ : ρ.left ≫ D.famφB α 2 = (DVR.cP D T α).left := congrArg (fun q => q.left) (DVR.comp_cP D ρ α)
  have e₃ : ρ.left ≫ D.famφB α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem exists_genB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) (α mu : D.X) {K : Type} [Fintype K]
    (φ : K → (Spec (CommRingCat.of R) ⟶ D.P.A.left)) (ε : K → ℤ) (v : LB.Gen (LB.LinComb D.P.L φ ε)), v.IsGen →
    (∀ (U : Type) [CommGroup U] (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) (α + mu)).left)⁻¹ *
        h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) α).left *
        h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) mu).left *
        (h (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ D.P.A).left)⁻¹ *
        (h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) mu).left ^ k)⁻¹ *
        h (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ D.P.A).left ^ k) →
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + k • mu))
        (fun i => (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu)).left ≫ D.famφB α i)) (DegPre.deltaε k)),
      u.IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.P.A) (z : T.left)
        (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val u ρ.left z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN (ReciprocityTheory.ChartRestriction.G.DVR.th D z J) k
            (ReciprocityTheory.ChartRestriction.G.DVR.cP D T α) (ReciprocityTheory.ChartRestriction.G.DVR.cP D T mu) ρ *
          (ReciprocityTheory.ChartRestriction.G.DVR.th D z J (ReciprocityTheory.ChartRestriction.G.DVR.cP D T α) ρ (ReciprocityTheory.ChartRestriction.G.DVR.cP D T mu))⁻¹ *
          val v (ρ.left ≫ D.P.A.hom) z J := by
  intro R _ _ D k α mu K _ φ ε v hv hF
  have htr : padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu) = (𝟙 D.P.A) * (DVR.cP D D.P.A mu) := rfl
  have hα' : DVR.cP D D.P.A (α + k • mu) = (DVR.cP D D.P.A α) * (DVR.cP D D.P.A mu) ^ k := by rw [DVR.cPoint_add, DVR.cPoint_nsmul]
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (DVR.cP D D.P.A α) (DVR.cP D D.P.A mu) (𝟙 D.P.A) k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := Sum.elim (D.famφB (α + k • mu))
      (fun i => (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu)).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub (DVR.cP D D.P.A α) (𝟙 D.P.A) (DVR.cP D D.P.A mu) h
      have p₂ := hF U (fun q => h (D.P.A.hom ≫ q))
      have p₃ : ∏ i, h (D.famφB (α + k • mu) i) ^ DegPre.famε k i = h (Over.Hom.left (𝟙 D.P.A)) ^ ((k : ℤ) - 1) *
          h ((DVR.cP D D.P.A α) * (DVR.cP D D.P.A mu) ^ k * 𝟙 D.P.A).left *
          (h ((DVR.cP D D.P.A α) * (DVR.cP D D.P.A mu) ^ k).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left := by
        have := prod_famB D (𝟙 D.P.A) (α + k • mu) k h
        rw [hα'] at this
        refine Eq.trans ?_ this
        simp only [Over.id_left, Category.id_comp]
      have p₄ := prod_famB D (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu)) α k h
      have c₁ : ∀ χ, D.P.A.hom ≫ (DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) χ).left = (DVR.cP D D.P.A χ).left :=
        fun χ => congrArg (fun q => q.left) (DVR.comp_cP D (toUnit D.P.A) χ)
      have c₂ : D.P.A.hom ≫ (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ D.P.A).left = (1 : D.P.A ⟶ D.P.A).left :=
        congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toUnit D.P.A))
      rw [c₁, c₁, c₁, c₂, DVR.cPoint_add] at p₂
      rw [htr] at p₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (DVR.prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (DVR.prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (DVR.prod_neg _ _ p₄)).symm)
      rw [← _root_.mul_assoc (DVR.cP D D.P.A α), mul_comm (DVR.cP D D.P.A mu) (𝟙 D.P.A)]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (DVR.cP D D.P.A α) (lift (𝟙 D.P.A) (DVR.cP D D.P.A mu))).left)))
      (LB.pullGen D.P.L _ _ v D.P.A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hN
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))) (DVR.pullGen_isGen _ _ _ _ hv _))
  refine ⟨u₀, hu₀, fun T ρ z J hJ => ?_⟩
  have h1 := vu₀ _ ρ.left z J hJ
  rw [val_mul hJ] at h1
  erw [val_mul hJ] at h1
  rw [vN T ρ z J hJ] at h1
  erw [val_inv, val_cub D.cub ρ hJ] at h1
  rw [val_pull hJ] at h1
  rw [h1]
  simp only [DVR.comp_cP, Category.comp_id]

theorem exists_readGen : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (κ : D.X → (FractionRing R)ˣ),
    GlobalTheory.ThFam.Reads D κ → ∀ (k : ℕ) (α mu : D.X),
    ∃ (K : Type) (_ : Fintype K) (φ : K → (Spec (CommRingCat.of R) ⟶ D.P.A.left)) (ε : K → ℤ)
      (v : LB.Gen (LB.LinComb D.P.L φ ε)), v.IsGen ∧
      (∀ (U : Type) [CommGroup U] (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
        (h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) (α + mu)).left)⁻¹ *
          h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) α).left *
          h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) mu).left *
          (h (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ D.P.A).left)⁻¹ *
          (h (ReciprocityTheory.ChartRestriction.G.DVR.cP D (Over.mk (𝟙 (Spec (CommRingCat.of R)))) mu).left ^ k)⁻¹ *
          h (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ D.P.A).left ^ k) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
        (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (DegPre.famMult D (FractionRing R) k mu α) r z J =
          GlobalTheory.ThFam.unitAt (r ≫ jFK (R := R) (FractionRing R)) z (GlobalTheory.ThFam.lead κ k α mu) *
            val v (r ≫ jFK (R := R) (FractionRing R) ≫ jK R) z J := by
  intro R _ _ D κ hκ k α mu
  obtain ⟨g, hg, hgv⟩ := hκ
  let T₀ : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
  let rigR := LB.pullGen D.P.L _ _ D.rig (toUnit T₀).left
  let tauR := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g (mu + α))
    (LB.invGen D.P.L _ _ (g mu))) (LB.invGen D.P.L _ _ (g α))) (LB.invGen D.P.L _ _ rigR)
  let v := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (g mu) k) tauR)
    (GeneratorPullback.powGen D.P.L _ _ rigR k)
  have hrig : rigR.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _
  refine ⟨_, inferInstance, _, _, v, ?_, ?_, ?_⟩
  · exact ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen _ _ _ _ (hg mu) k)
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
        (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hg _) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hg _)))
        (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hg _))) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ hrig)))
      (ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen _ _ _ _ hrig k)
  · intro U _ h
    have a₁ : ∀ χ, ptR D χ = (ReciprocityTheory.ChartRestriction.G.DVR.cP D T₀ χ).left := fun _ => rfl
    have a₂ : (toUnit T₀).left ≫ eSec D.P.A = (1 : T₀ ⟶ D.P.A).left := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
    rw [add_comm mu α]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  · intro Z r z J hJ
    have t₁ : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
    have t₂ : (toUnit T₀).left = 𝟙 (Spec (CommRingCat.of R)) := rfl
    have vp : ∀ {K' : Type} [Fintype K'] {φ : K' → (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left)}
        {ε : K' → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (n : ℕ) (r' : Z ⟶ _),
        val (GeneratorPullback.powGen D.P.L φ ε t n) r' z J = val t r' z J ^ n := fun t n r' => map_pow _ _ _
    have vpR : ∀ {K' : Type} [Fintype K'] {φ : K' → (Spec (CommRingCat.of R) ⟶ D.P.A.left)}
        {ε : K' → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (n : ℕ) (r' : Z ⟶ _),
        val (GeneratorPullback.powGen D.P.L φ ε t n) r' z J = val t r' z J ^ n := fun t n r' => map_pow _ _ _
    rw [DegPre.famMult, val_pull hJ, val_mul hJ, val_mul hJ, vp, vp, DegPre.tau, val_mul hJ, val_mul hJ, val_mul hJ,
      val_inv, val_inv, val_inv, DegPre.rigK, val_pull hJ, hgv _ _ _ _ _ hJ, hgv _ _ _ _ _ hJ, hgv _ _ _ _ _ hJ]
    simp only [v, tauR, rigR]
    rw [val_mul hJ, val_mul hJ, vpR, vpR, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
      val_pull hJ, t₁, t₂]
    simp only [lead, map_mul, map_pow, map_inv, Category.assoc, Category.comp_id]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, smul_add]
    abel

theorem member_integral : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (κ : D.toPre.X → (FractionRing R)ˣ), GlobalTheory.ThFam.Reads D.toPre κ → ∀ (k : ℕ), 1 ≤ k → ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (F : Fam D.toPre (FractionRing R) k), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) b (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) → ∀ (mu : D.toPre.X) (r : R), algebraMap R (FractionRing R) r = ((GlobalTheory.ThFam.lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) → ∃ f : D.toPre.SecB k (α + k • mu), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) (α + k • mu)) (DegPre.famε k) (F.s (α + k • mu)) (D.toPre.famφB (α + k • mu)) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) ∧ ∀ e : ℕ, r ∈ maximalIdeal R ^ (e + 1) → VanMod (maximalIdeal R) f e := by
  intro R _ _ _ _ D κ hκ k hk α b F hb mu r hr
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hL := D.toPre.P.isLB
  obtain ⟨Kv, _, φv, εv, v, hv, hF, hval⟩ := exists_readGen R D.toPre κ hκ k α mu
  obtain ⟨uR, huR, valR⟩ := exists_genB R D.toPre k α mu φv εv v hv hF
  obtain ⟨f₀, hf₀⟩ := exists_sec hL (φ' := D.toPre.famφB (α + k • mu)) (ε' := DegPre.famε k) (fun U _ h => by
      refine Eq.trans (ReciprocityTheory.ChartRestriction.G.DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
        (c := ∏ i, h ((padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c mu)).left ≫ D.toPre.famφB α i) ^ DegPre.famε k i) rfl
        (ReciprocityTheory.ChartRestriction.G.DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (D.toPre.famφB (α + k • mu) i) ^ DegPre.famε k i) rfl (ReciprocityTheory.ChartRestriction.G.DVR.prod_neg _ _ rfl))) ?_
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _))
    (pullMulSec b (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c mu)).left uR huR)
  let f : GlobalTheory.FieldBaseChange.SecOver D.toPre.P.A.hom
      (LB.LinComb D.toPre.P.L (D.toPre.famφB (α + k • mu)) (DegPre.famε k)) :=
    (r • (show GlobalTheory.FieldBaseChange.SecOver D.toPre.P.A.hom
      (LB.LinComb D.toPre.P.L (D.toPre.famφB (α + k • mu)) (DegPre.famε k)) from f₀) :
        GlobalTheory.FieldBaseChange.SecOver D.toPre.P.A.hom (LB.LinComb D.toPre.P.L (D.toPre.famφB (α + k • mu)) (DegPre.famε k)))
  refine ⟨f, ?_, ?_⟩
  · have hbF : F.s α = GlobalTheory.FieldBaseChange.pullOver D.toPre.P.L (DegPre.famε k)
        (GlobalTheory.FieldBaseChange.prB_hom D.toPre (FractionRing R)) (GlobalTheory.FieldBaseChange.famφ_prB D.toPre (FractionRing R) α) b := by
      have := (GlobalTheory.FieldBaseChange.secScal_iff (GlobalTheory.FieldBaseChange.prB_hom D.toPre (FractionRing R))
        (GlobalTheory.FieldBaseChange.famφ_prB D.toPre (FractionRing R) α) hL (F.s α) b _ (algebraMap R (FractionRing R))
        (GlobalTheory.FieldBaseChange.bf_hom D.toPre (FractionRing R)) 1).1 hb
      rw [map_one] at this
      exact (this.trans (one_smul _ _)).symm
    refine (GlobalTheory.FieldBaseChange.secScal_iff_val hL _ _ _ _).2 fun y J hJ => ?_
    obtain ⟨⟨uK, huK, hcK⟩, hvK⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := D.toPre) (F := FractionRing R) hG k mu α
    have e₁ := (secRel_iff hL _ _ _ _ _ _ _ _ _ uK).1 (F.fe mu α uK huK hcK) _ (𝟙 _) y J hJ
    have e₂ := hvK uK huK hcK _ (𝟙 _) y J hJ
    have e₃ := hval _ (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left y J hJ
    have e₄ := valR _ (DegPre.prB D.toPre (FractionRing R)) y J hJ
    have e₅ := hf₀ _ ((DegPre.prB D.toPre (FractionRing R)).left) y J hJ
    have e₆ := sval_pullMulSec b (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c mu)).left uR huR
      (DegPre.prB D.toPre (FractionRing R)).left y hJ
    have hf := GlobalTheory.FieldBaseChange.sval_smul' (π := D.toPre.P.A.hom) hJ (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing R)).left) r
      (f₀ : GlobalTheory.FieldBaseChange.SecOver D.toPre.P.A.hom _)
    have m₁ : (DegPre.prB D.toPre (FractionRing R)).left ≫
        (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c mu)).left =
        (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
      have m₁' : DegPre.prB D.toPre (FractionRing R) ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c mu) =
          DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R) := by
        rw [ReciprocityTheory.ChartRestriction.G.DVR.trF_eq, ReciprocityTheory.ChartRestriction.G.DVR.tr_pr, ReciprocityTheory.ChartRestriction.G.DVR.comp_cP]
        show DegPre.prB _ _ ≫ (𝟙 _ * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre D.toPre.P.A mu) = _
        rw [MonObj.comp_mul, Category.comp_id, ReciprocityTheory.ChartRestriction.G.DVR.comp_cP]
      exact congrArg (fun q => q.left) m₁'
    have m₂ : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom =
        (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) ≫ jK R := by
      rw [Over.w (DegPre.prB D.toPre (FractionRing R)), ← Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)]
      rfl
    have m₃ : ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) k α
        (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre (TF (R := R) (FractionRing R)) mu) (𝟙 _) y J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN (ReciprocityTheory.ChartRestriction.G.DVR.th D.toPre y J) k
            (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ α) (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (DegPre.prB D.toPre (FractionRing R)) *
          (ReciprocityTheory.ChartRestriction.G.DVR.th D.toPre y J (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ α) (DegPre.prB D.toPre (FractionRing R))
            (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu))⁻¹ := by
      rw [ReciprocityTheory.ChartRestriction.G.DVR.uVal_id, ReciprocityTheory.ChartRestriction.G.DVR.comp_cP]
    have m₄ : GlobalTheory.FieldBaseChange.constVal ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫
        jFK (R := R) (FractionRing R) ≫ jK R) y r =
        (unitAt ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y
          (lead κ k α mu)).val := by
      rw [← Category.assoc, GlobalTheory.FieldBaseChange.constVal_specMap, hr, GlobalTheory.FieldBaseChange.constVal,
        gs_eq _ y ⊤ (by trivial)]
      rfl
    have m₅ : gs (𝟙 _) y ⊤ (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) = 1 := by
      rw [gs_eq _ y ⊤ (by trivial)]
      simp only [scal, map_one]
    rw [hf]
    simp only [Category.id_comp, Over.id_left] at e₁ e₂ ⊢
    rw [e₅, e₆, e₄, m₅, _root_.one_mul, e₁, hbF]
    erw [GlobalTheory.FieldBaseChange.sval_pullOver (GlobalTheory.FieldBaseChange.prB_hom D.toPre (FractionRing R))
      (GlobalTheory.FieldBaseChange.famφ_prB D.toPre (FractionRing R) α) b (DegPre.trF D.toPre (FractionRing R) mu).left hJ]
    rw [e₂, e₃, m₃, m₁, m₂, m₄]
    simp only [Units.val_mul]
    ring
  · intro e he j
    have hpf := pullback.condition (f := D.toPre.P.A.hom) (g := thick R (maximalIdeal R) e)
    refine fn_ext fun y hy => ?_
    rw [gs_pull (𝟙 _) _ y _ hy, GlobalTheory.FieldBaseChange.gs_zero' _ y _ hy]
    have key := GlobalTheory.FieldBaseChange.gs_smul (R := R) D.toPre.P.A.hom
      (𝟙 _ ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) y
      (LB.wchart D.toPre.P.L (D.toPre.famφB (α + k • mu)) j) hy r (f₀.f j)
    refine key.trans ?_
    rw [Category.id_comp, hpf,
      GlobalTheory.FieldBaseChange.constVal_specMap, (Ideal.Quotient.eq_zero_iff_mem).2 he]
    simp only [GlobalTheory.FieldBaseChange.constVal, map_zero]
    rw [GlobalTheory.FieldBaseChange.gs_zero' (pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) y ⊤ (by trivial), zero_mul]

end GlobalTheory.ThFam
