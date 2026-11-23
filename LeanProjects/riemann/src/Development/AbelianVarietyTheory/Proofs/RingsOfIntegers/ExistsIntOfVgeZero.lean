import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFamilyOfStrictMin

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralSection

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.IntegralExpansion

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem exists_eq_of_nonneg (hϖ : Irreducible ϖ) {v : AddValuation (FractionRing V) (WithTop ℚ)}
    (hv : ValOver ϖ (FractionRing V) v) {c : FractionRing V} (h : 0 ≤ v c) :
    ∃ b : V, c = algebraMap V (FractionRing V) b := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, (map_zero _).symm⟩
  obtain ⟨n, u, hu⟩ := hasVal_of_ne_zero hϖ hc

  have hvc : v c = ((n : ℚ) : WithTop ℚ) := hv c n ⟨u, hu⟩
  have hn : (0 : ℤ) ≤ n := by
    rw [hvc] at h
    have h' : (0 : ℚ) ≤ (n : ℚ) := WithTop.coe_le_coe.mp h
    exact_mod_cast h'

  lift n to ℕ using hn
  refine ⟨ϖ ^ n * (u : V), ?_⟩
  rw [hu, map_mul, map_pow, zpow_natCast]

theorem exists_int_of_vge_zero (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)}
    {v : AddValuation (FractionRing V) (WithTop ℚ)} (hv : ValOver ϖ (FractionRing V) v) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))}
    (hs : VGe D (FractionRing V) v k α s 0) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, ha, hsum⟩ := hs

  have hint : ∀ i, ∃ b : V, a i = algebraMap V (FractionRing V) b := fun i =>
    exists_eq_of_nonneg hϖ hv (by simpa using ha i)
  choose b hb using hint

  refine ⟨FamInt.secLin (fun i => constFn D.toPre.P.A.hom ⊤ (b i)) σ, ?_⟩
  refine SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_
  rw [SectionScalarValuation.sval_lin _ σ (fun j => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF
      (fun j => (hsum j).trans (by simp only [constBF_eq]; rfl)) _ y hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SectionScalarValuation.secScal_sval (hσ i) (𝟙 _) y hJ]
  congr 1
  clear hsum hσ ha hJ
  rw [gs_constFn]
  · rw [hb i]

    have e1 := gs_pull (𝟙 _) (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) (b i)))
    rw [Category.id_comp] at e1
    have e1' : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (algebraMap V (FractionRing V) (b i))) =
        cst (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y (algebraMap V (FractionRing V) (b i)) := e1
    rw [e1', ← cst_comp, Category.id_comp]
    congr 1

    have h1 := Over.w (DegPre.prB D.toPre (FractionRing V))
    have h2 := Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)
    rw [h1]
    rw [← h2]
    congr 1

    unfold TF spMap
    change jFK _ ≫ jK V = _
    unfold jFK jK
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · trivial

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (s : U.SecK k) (E : Fam D.toPre (FractionRing V) k), U.Expands k s E → (∀ α, VGe D (FractionRing V) vK k α (E.s α) 0) → ∃ σ : H0 U.LG.L k, GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 := by
  intro V _ _ _ ϖ hϖ D vK hvK A G _ _ U k s E hE hvE
  obtain ⟨r, hr, σ, f, hσ, hf, hexp⟩ := hE
  have hg : ∀ α, ∃ g : D.toPre.SecB k α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α)
      (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing V)).left 1 :=
    fun α => exists_int_of_vge_zero hϖ hvK (hvE α)
  choose g hg using hg
  have hfg : ∀ α, SecIsMul D.toPre.P.A.hom r (f α) (g α) := fun α =>
    secIsMul_of_secScal D.toPre.P.isLB D.toPre.P.A.hom (prB_app_injective D.toPre) (hg α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing V))]; exact hf α)
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ

  have hmul : ∀ α, ∃ g' : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom (ϖ ^ m) (f α) g' := by
    intro α
    obtain ⟨g', hg'⟩ := exists_secIsMul D.toPre.P.A.hom (u : V) (g α)
    obtain ⟨F', hF'⟩ := exists_secIsMul D.toPre.P.A.hom (ϖ ^ m) g'
    have hc := SecIsMul.comp hF' hg'
    have hF'f : F' = f α := SecOps.sec_ext fun j => by
      rw [hc j, hfg α j, hu, mul_comm (u : V)]
    exact ⟨g', hF'f ▸ hF'⟩
  choose g' hg' using hmul

  have hdiv : ∃ τ : H0 U.LG.L k, SecIsMul G.hom (ϖ ^ m) σ τ := by
    rcases m with _ | e
    · refine ⟨σ, fun j => ?_⟩
      simp [scal]
    · exact exists_div_of_expandsAt hϖ U e k σ g' f hg' (hexp e)
  obtain ⟨τ, hτ⟩ := hdiv

  obtain ⟨σ', hσ'⟩ := exists_secIsMul G.hom ((u⁻¹ : Vˣ) : V) τ
  refine ⟨σ', SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_⟩
  have hlin : ∀ {a : V} {t t' : H0 U.LG.L k}, SecIsMul G.hom a t' t →
      sval t' (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
        gs (𝟙 _ ≫ pullback.fst G.hom (jK V)) y ⊤ (scal G.hom a) * sval t (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J := by
    intro a t t' ht
    have hl := SectionScalarValuation.sval_lin (fun _ : Fin 1 => scal G.hom a) (fun _ => t)
      (fun j => by rw [Fin.sum_univ_one]; exact ht j) (𝟙 _ ≫ pullback.fst G.hom (jK V)) y hJ
    rwa [Fin.sum_univ_one] at hl
  have hgs : ∀ {X : Scheme.{0}} (r' : _ ⟶ X) (p : X ⟶ Spec (CommRingCat.of V)) (a : V),
      gs r' y ⊤ (scal p a) = cst (r' ≫ p) y a := fun r' p a => gs_pull r' p y ⊤ trivial _
  have hq : (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom = 𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V := by
    rw [Category.assoc, pullback.condition]
  have key := GlobalTheory.IntegralExpansion.sval_of_secScal hσ (𝟙 _) y hJ
  rw [hlin hτ, hgs, hgs, hq, hu, cst_mul] at key
  rw [hlin hσ', hgs, hq]

  have hunit : IsUnit (cst (𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V) y (ϖ ^ m)) := by
    have hK : algebraMap V (FractionRing V) (ϖ ^ m) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr (pow_ne_zero _ hϖ.ne_zero)
    rw [← Category.assoc]
    change IsUnit (cst (_ ≫ spMap (algebraMap V (FractionRing V))) y _)
    rw [cst_comp]
    have h1 := (cst_mul (𝟙 _ ≫ pullback.snd G.hom (jK V)) y (algebraMap V (FractionRing V) (ϖ ^ m))
      (algebraMap V (FractionRing V) (ϖ ^ m))⁻¹).symm.trans (by rw [mul_inv_cancel₀ hK, cst_one])
    exact ⟨⟨_, _, h1, (mul_comm _ _).trans h1⟩, rfl⟩
  have hT : sval τ (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
      cst (𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V) y (u : V) * sval s (𝟙 _) y J :=
    hunit.mul_left_cancel (by rw [key]; ring)
  rw [hT, ← _root_.mul_assoc, ← cst_mul, Units.inv_mul, cst_one, _root_.one_mul]

end GlobalTheory.IntegralSection
