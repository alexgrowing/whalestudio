import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

theorem powGen_isGen' {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) : (GeneratorPullback.powGen L φ ε t n).IsGen := by
  exact ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen L φ ε t ht n

section Val

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem genHasVal_powGen {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) (k : ℕ) :
    GenHasVal ϖ L φ φ' hφ (fun i => (k : ℤ) * ε i) (GeneratorPullback.powGen L φ' ε t k) (k * n) := by
  obtain ⟨e, he, c, hc, hte⟩ := hn
  refine ⟨GeneratorPullback.powGen L φ ε e k, ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen L φ ε e he k, c ^ k, ?_, ?_⟩
  · obtain ⟨u, rfl⟩ := hc
    refine ⟨u ^ k, ?_⟩
    rw [mul_pow, ← zpow_natCast (_ ^ n), ← zpow_mul, mul_comm n, Units.val_pow_eq_pow_val, map_pow]
  · intro j
    have h1 : (GeneratorPullback.powGen L φ' ε t k).s j = t.s j ^ k := rfl
    have h2 : (GeneratorPullback.powGen L φ ε e k).s j = e.s j ^ k := rfl
    rw [h1, h2, Units.val_pow_eq_pow_val, hte j]
    erw [mul_pow, map_pow, map_pow, Units.val_pow_eq_pow_val]
    congr 1
    simp only [scal, resTop, map_pow]
    rfl

theorem val_genHasVal {X : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix]
    {φ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    {hφ : ∀ k, φ' k = jK V ≫ φ k} {ε : Ix → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)}
    {e : LB.Gen (LB.LinComb L φ ε)} {c : FractionRing V}
    (hte : ∀ j, (t.s j).val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j))).val)
    {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing V))) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) :
    (val t r z J).val = gs r z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (val e (r ≫ jK V) z J).val := by
  have hz : r z ∈ LB.wchart L φ' (fun k => J (r ≫ φ' k)) := hJ.mem φ' r
  have hj : (fun k => J ((r ≫ jK V) ≫ φ k)) = fun k => J (r ≫ φ' k) := by
    funext k
    rw [hφ k, Category.assoc]
  have hz' : (r ≫ jK V) z ∈ LB.wchart L φ (fun k => J (r ≫ φ' k)) := by
    have := hJ.mem φ (r ≫ jK V)
    rwa [hj] at this
  have he := congrArg (fun j : Ix → L.ι => (gm (r ≫ jK V) z (LB.wchart L φ j) (e.s j)).val) hj
  unfold val
  erw [he, ← gs_unit _ _ _ hz, ← gs_unit _ _ _ hz', hte, gs_mul _ _ _ hz]
  congr 1
  · exact gs_res r z le_top hz _
  · simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
    erw [gs_res r z _ hz, gs_pull r (jK V) z _ hz']

theorem exists_val_genHasVal {X : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix]
    {φ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    {hφ : ∀ k, φ' k = jK V ≫ φ k} {ε : Ix → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)} {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) :
    ∃ (e : LB.Gen (LB.LinComb L φ ε)) (c : FractionRing V), e.IsGen ∧ HasVal ϖ c n ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing V))) (z : Z) (J : (Z ⟶ X) → L.ι),
        Good L z J → (val t r z J).val = gs r z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
          (val e (r ≫ jK V) z J).val := by
  obtain ⟨e, he, c, hc, hte⟩ := hn
  exact ⟨e, c, he, hc, fun Z r z J hJ => val_genHasVal (hφ := hφ) hte r z hJ⟩

end Val

section Fam

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ}

theorem ahom_c (χ : D.toPre.X) :
    D.toPre.P.A.hom ≫ (D.toPre.c χ).left = (cQ D.toPre D.toPre.P.A χ).left := by
  simp [cQ]

theorem ahom_e : D.toPre.P.A.hom ≫ 𝟙 _ ≫ eSec D.toPre.P.A = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := by
  rw [Category.id_comp, CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem famMult_data (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (k : ℕ) (mu α : D.toPre.X) :
    ∃ (Ix : Type) (_ : Fintype Ix) (φV : Ix → (Spec (CommRingCat.of V) ⟶ D.toPre.P.A.left)) (εV : Ix → ℤ)
      (e' : LB.Gen (LB.LinComb D.toPre.P.L φV εV)), e'.IsGen ∧
      (∀ (U : Type) [CommGroup U] (h : (D.toPre.P.A.left ⟶ D.toPre.P.A.left) → U),
        ∏ i, h (D.toPre.P.A.hom ≫ φV i) ^ εV i =
          (h (cQ D.toPre D.toPre.P.A α * cQ D.toPre D.toPre.P.A mu).left)⁻¹ * h (cQ D.toPre D.toPre.P.A α).left *
            h (cQ D.toPre D.toPre.P.A mu).left * (h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left)⁻¹ *
            (h (cQ D.toPre D.toPre.P.A mu).left ^ k)⁻¹ * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ k) ∧
      ∃ c₀ : FractionRing V, HasVal ϖ c₀ (k * Q mu + bOf D.toPre Q mu α) ∧
        ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F))
          (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J →
          (val (DegPre.famMult D.toPre F k mu α) r z J).val =
            gs (r ≫ jFK (R := V) F) z ⊤ (scal (𝟙 _) c₀) * (val e' (r ≫ DegPre.jFR (R := V) F) z J).val := by
  have hL := D.toPre.P.isLB
  have hp := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (hQ mu) k
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ (hQ (mu + α))
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (hQ mu))
  have h2 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ h1
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (hQ α))
  have h3 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ h2
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (rigK_val D))
  have hr := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (rigK_val (ϖ := ϖ) D) k
  have h4 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _
    (genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hp h3) hr
  obtain ⟨e', c₀, he', hc₀, hv⟩ := exists_val_genHasVal h4
  refine ⟨_, _, _, _, e', he', fun U _ h => ?_, c₀, ?_, fun F _ _ Z r z J hJ => ?_⟩
  · simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, ahom_c, ahom_e, cQ_add]
    rw [mul_comm (cQ D.toPre D.toPre.P.A mu)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  · have e : (k : ℤ) * Q mu + (Q (mu + α) + -Q mu + -Q α + -0) + (k : ℤ) * 0 = k * Q mu + bOf D.toPre Q mu α := by
      simp only [bOf]; ring
    exact e ▸ hc₀
  · have H := hv Z (r ≫ jFK (R := V) F) z J hJ
    unfold DegPre.famMult
    rw [val_pull hJ]
    exact H.trans (by rw [Category.assoc]; rfl)

end Fam

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
