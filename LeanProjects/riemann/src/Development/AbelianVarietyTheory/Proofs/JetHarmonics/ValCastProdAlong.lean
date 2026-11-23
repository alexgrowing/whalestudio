import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GCorCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GCorCut Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermRatio
open GlobalTheory.BoxFamily GlobalTheory.PowGerm.FrameN

theorem clause_along {X' Y Y₁ Z : Scheme.{0}} {M' : LB X'} (g : Y₁ ⟶ X') (z : Y ⟶ Y₁) (q : ℤ)
    (σ : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => g) (fun _ => q))) (a : Γ(Y, ⊤))
    (τ : LB.Gen (LB.LinComb M' (K := PUnit.{1}) (fun _ => z ≫ g) (fun _ => q)))
    (H : ∀ j : Fin 1 → M'.ι, (Y.presheaf.map (homOfLE (ExpBijectiveUniformisation.wchart_comp_le M' g z j)).op).hom ((z.app _).hom (σ.f j)) =
      (Y.presheaf.map (homOfLE le_top).op).hom a * (τ.s (fun _ => j 0)).val) (r : Z ⟶ Y) (y : Z) (J) (hJ : Good M' y J) :
    sval σ (r ≫ z) y J = gs r y ⊤ a * (val τ r y J).val := by
  have hy : r y ∈ LB.wchart M' (fun _ : PUnit.{1} => z ≫ g) (fun _ => J (r ≫ z ≫ g)) := hJ.mem _ r
  have e := congrArg (gs r y _) (H (fun _ => J (r ≫ z ≫ g)))
  rw [sval_of σ (r ≫ z) y J (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [Category.assoc])]
  exact ((gs_res _ y _ hy _).trans (gs_pull r z y _ (ExpBijectiveUniformisation.wchart_comp_le M' g z (fun _ => J (r ≫ z ≫ g)) hy) _)).symm.trans
    (e.trans ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res _ y le_top hy _) (gs_unit _ y _ hy _))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]

theorem val_cast_prod_along (t : SAB H (Sp V)) {n : ℕ}
    (L : LB t.G.left) (h : t.PP.L = L) {Y Y₀ Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y₀ ⟶ t.G.left)) (ε : K → ℤ)
    (e : LB.Gen (LB.LinComb t.PP.L φ ε)) (q : ℕ) (r : Fin n → (Y ⟶ Y₀)) (ρ : Z ⟶ Y) (y : Z) (J) (hJ : Good L y J) :
    val (genCast h _ _ (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
      LB.pullGen t.PP.L _ _ (genPowG t _ _ e q) (r i))) ρ y J = ∏ i, val (genCast h _ _ e) (ρ ≫ r i) y J ^ q := by
  subst h
  show val (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
      LB.pullGen t.PP.L _ _ (genPowG t _ _ e q) (r i)) ρ y J = ∏ i, val e (ρ ≫ r i) y J ^ q
  rw [val_finProd _ _ _ _ _ hJ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [val_pull hJ, GermD.val_genPowG]

theorem val_eL_ratio {t : SAB H (Sp V)} {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {FT : Fin d → PS V 2 d}
    {act : 𝓞 E → Fin d → PS V 1 d} {tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)} {uv : Fin d → Fin d → V}
    (hch : IsChartG t (𝟙 (Sp V)) d FT act tg uv x) (wP : PrimTyG t) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m)
    (m : ℕ) (U : (Jet V (Fin 2 × Fin d) m)ˣ)
    (hU : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ (e (m + 1))
      (homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _)).left) (scaleGenG t _ _ (unitΓ U) (e m)))
    (L : LB t.G.left) (h : t.PP.L = L) {Z : Scheme.{0}} (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 1).left) (y : Z) (J)
    (hJ : Good L y J) :
    val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP (m + 1))) (r ≫ (GermD.ρT (𝟙 (Sp V)) d m).left) y J =
      gm (r ≫ (homAt (𝟙 (Sp V)) (GermD.sL m (act H.w0))).left) y ⊤ (unitΓ U) *
        val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP m)) r y J := by
  subst h
  have hx : (GermD.ρT (𝟙 (Sp V)) d m).left ≫ (x (m + 1)).left = (x m).left := by
    rw [← Over.comp_left, hch.trunc m]
  have hs : (GermD.ρT (𝟙 (Sp V)) d m).left ≫ (homAt (𝟙 (Sp V)) (GermD.sL (m + 1) (act H.w0))).left =
      (homAt (𝟙 (Sp V)) (GermD.sL m (act H.w0))).left ≫
        (homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _)).left := by
    rw [← Over.comp_left, ← Over.comp_left, GermD.homAt_comp, GermD.homAt_comp, GermD.sL_trunc]
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (val_mul hJ _ _ _).symm))
  rw [mul_left_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (val_pull hJ wP _ _).trans ((congrArg (fun s => val wP s y J)
      ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) hx))).trans (val_pull hJ wP _ _).symm)
  · exact (val_pull hJ (e (m + 1)) _ _).trans ((congrArg (fun s => val (e (m + 1)) s y J)
      ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hs).trans (Category.assoc _ _ _).symm))).trans
      ((val_pull hJ (e (m + 1)) _ _).symm.trans ((val_corr hJ hU _).trans
        ((GermB.val_scale t _ _ _ _ _ y J hJ).trans (congrArg (_ * ·) (val_pull hJ (e m) _ _).symm)))))

theorem trunc_jcN (F : Type) [Field F] [Algebra V F] (d n m : ℕ) (i : Fin n) :
    spMap ((jetTrunc : Jet F (Fin n × Fin d) (m + 1) →ₐ[F] Jet F (Fin n × Fin d) m) :
        Jet F (Fin n × Fin d) (m + 1) →+* Jet F (Fin n × Fin d) m) ≫ jcN V F d n (m + 1) i =
      jcN V F d n m i ≫ (GermD.ρT (𝟙 (Sp V)) d m).left := by
  rw [← coef_cpy, ← coef_cpy, ← Category.assoc, GermBasic.spMap_comp_eq, JetTr.jetCoef_trunc,
    ← GermBasic.spMap_comp_eq, Category.assoc, trunc_cpy, Category.assoc]
  rfl

theorem cst_prod_pow {A : Type} [CommRing A] {Z : Scheme.{0}} (r : Z ⟶ Sp A) (y : Z) {n : ℕ} (a : Fin n → A) (q : ℕ) :
    cst r y (∏ i, a i ^ q) = ∏ i, cst r y (a i) ^ q := by
  simp only [cst, gs_eq r y ⊤ trivial, map_prod, map_pow]

section Germ

variable [IsDomain V] {I : Ideal V} {t : SAB H (Sp V)} {P : PELUnif I t} {d : ℕ}
  {xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {act : 𝓞 E → Fin d → PS V 1 d} {eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m} {wPT : PrimTyG t}
  {n : ℕ} {D' : DegData V I} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Sp V)}
  [GrpObj G'] [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} {pG : IsPowGrp G' t.G n}
  {U' : Unif I D' A' G'} {PU : UnifPowOf pD pA pG U' P.U}
  {F : Type} [Field F] [Algebra (FractionRing V) F] [Algebra V F] {q : ℕ} {σ' : U'.toUnifPre.SecGF F q} {f : PS F n d}

theorem val_of_germ (h : IsGermN P xT act eT wPT pG PU F q σ' f) (m : ℕ) :
    ∃ z : Sp (Jet F (Fin n × Fin d) m) ⟶ (UnifPre.GF (R := V) (G := G') F).left,
      z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
        spMap (algebraMap F (Jet F (Fin n × Fin d) m)) ∧
      (∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet F (Fin n × Fin d) m)) (y : Z) (J J'), Good P.U.LG.L y J → Good U'.LG.L y J' →
        (om (pr := fun i => (pG.pr i).left) PU.wL y J J' ((r ≫ z) ≫ UnifPre.gFK (R := V) (G := G') F) ^ q).val *
          sval σ' (r ≫ z) y J' =
          cst r y (psJet m f) * (∏ i, val (genCast (congrArg RigLB.L P.bundle).symm _ _
            (eLG t (𝟙 (Sp V)) d xT act eT wPT m)) (r ≫ jcN V F d n m i) y J ^ q).val := by
  obtain ⟨z, τ, b, h₀, h₁, h₂, h₃, h₄⟩ := h m
  refine ⟨z, h₀, h₁, fun Z r y J J' hJ hJ' => ?_⟩
  have e₁ := mapsAt_val (pr := fun i => (pG.pr i).left) PU.wL _ _ τ b h₂ r y hJ hJ'
  have e₂ := (val_corr hJ ((corr_genCast _ _ _).1 h₃) r).trans (val_cast_prod_along t _ _ _ _ _ q _ r y J hJ)
  rw [clause_along _ z _ σ' _ τ h₄ r y J' hJ', mul_left_comm, e₂.symm.trans e₁, Category.assoc, zpow_natCast,
    Units.val_mul]
  rfl

omit [IsCommMonObj G'] in
theorem gFK_hom : UnifPre.gFK (R := V) (G := G') F ≫ G'.hom =
    (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left ≫
      (TFK (R := V) F).hom ≫ jK V := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, Over.w]
  exact congrArg (· ≫ jK V) (Over.w (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G')))

end Germ

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (t : SAB H (Sp V)) (P : PELUnif I t) (d n : ℕ) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V), IsChartG t (𝟙 (Sp V)) d FT act tg uv xT → ∀ (wPT : PrimTyG t), IsPrimG t wPT → ∀ (D' : DegData V I) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n) (U' : Unif I D' A' G') (PU : UnifPowOf pD pA pG U' P.U) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n d) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m), (∀ m, (eT m).IsGen) → IsGermN P xT act eT wPT pG PU F q σ' h → ∀ (m : ℕ) (U : (Jet V (Fin 2 × Fin d) m)ˣ), LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ (eT (m + 1)) (homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _)).left) (scaleGenG t _ _ (unitΓ U) (eT m)) → psJet m h * ∏ i : Fin n, (jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m) (jetCoef (algebraMap V F) (Fin 1 × Fin d) m (jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))) ^ q = psJet m h := by
  intro E _ _ _ H V _ _ I t P d n xT FT act tg uv hch wPT _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ q σ' h eT _ hg m U hU
  obtain ⟨z₁, a₁, b₁, c₁⟩ := val_of_germ hg (m + 1)
  obtain ⟨z₀, a₀, b₀, c₀⟩ := val_of_germ hg m
  let ρ := spMap ((jetTrunc : Jet F (Fin n × Fin d) (m + 1) →ₐ[F] Jet F (Fin n × Fin d) m) :
        Jet F (Fin n × Fin d) (m + 1) →+* Jet F (Fin n × Fin d) m)
  have hf : (ρ ≫ z₁) ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
      (𝟙 _ ≫ z₀) ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left := by
    rw [Category.assoc, a₁, Category.id_comp, a₀]
    exact spMap_comp_alg _
  have hz : ρ ≫ z₁ = 𝟙 _ ≫ z₀ := by
    refine GermBasic.gf_ext hf (pow_ext pG _ _ ?_ fun i => ?_)
    · rw [Category.assoc, Category.assoc _ (UnifPre.gFK (R := V) (G := G') F), gFK_hom, ← Category.assoc, hf,
        Category.assoc]
    · have hx : (GermD.ρT (𝟙 (Sp V)) d m).left ≫ (xT (m + 1)).left = (xT m).left := by
        rw [← Over.comp_left, hch.trunc m]
      rw [Category.id_comp, Category.assoc, Category.assoc, b₁, Category.assoc, b₀, jptN, jptN, ← Category.assoc,
        trunc_jcN, Category.assoc, hx]
  refine H1.cst_ext fun y => ?_
  obtain ⟨J, hJ⟩ := exists_good_at P.U.LG.isLB y
  obtain ⟨J', hJ'⟩ := exists_good_at U'.LG.isLB y
  have e₁ := c₁ _ ρ y J J' hJ hJ'
  have e₀ := c₀ _ (𝟙 _) y J J' hJ hJ'
  rw [hz, e₀] at e₁
  have k : cst ρ y (psJet (m + 1) h) = cst (𝟙 _) y (psJet m h) :=
    (H1.gs_spec _ y _).trans (congrArg (cst (𝟙 _) y) (FrRatio.psJet_trunc m h))
  have l := fun i => (congrArg (fun s => val (genCast (congrArg RigLB.L P.bundle).symm _ _
      (eLG t (𝟙 (Sp V)) d xT act eT wPT (m + 1))) s y J) (trunc_jcN F d n m i)).trans
    (val_eL_ratio hch wPT eT m U hU _ (congrArg RigLB.L P.bundle).symm (jcN V F d n m i) y J hJ)
  rw [k, Finset.prod_congr rfl fun i _ => congrArg (· ^ q) (l i)] at e₁
  simp only [Category.id_comp, mul_pow, Finset.prod_mul_distrib, Units.val_mul, ← _root_.mul_assoc] at e₁
  refine Eq.trans ?_ ((Units.mul_left_inj _).1 e₁).symm
  rw [H1.cst_mul, cst_prod_pow, Units.coe_prod]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun i _ => ?_)
  rw [Units.val_pow_eq_pow_val]
  refine congrArg (· ^ q) (Eq.trans ?_ (gs_unit _ y ⊤ trivial _))
  exact ((ExpansionValueZero.cst_comp (jcN V F d n m i) _ y _).trans (H1.gs_spec _ y _)).symm

end GlobalTheory.GermRatio
