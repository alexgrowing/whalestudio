import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LiftOUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsValGenHasVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem v_ratio_gt (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = p.g.b)
    (α : D.toPre.X) (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (gtφO hϖ hv m α) DegPre.gtε)) (hG₀ : G₀.IsGen) (t : F)
    (ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (val G₀ (r ≫ (ιS hϖ hv).left) z J).val) :
    ∃ q : ℚ, v t = (q : WithTop ℚ) ∧ (k : ℚ) * q = QForm.bOf D.toPre Q p.y α := by
  have hL := D.toPre.P.isLB
  have hmk : m ^ k = cP D.toPre (TO hϖ hv) p.y := by
    apply liftO_unique hϖ hv
    rw [comp_cP, cPoint_y, ← hm]
    exact map_pow (preHom (ιS hϖ hv)) m k
  obtain ⟨Ix, _, φV, εV, e', he', hfe', c₀, hc₀, hve'⟩ := famMult_data D hϖ hQ k p.y α
  obtain ⟨eψ, heψ, cψ, hcψ, hteψ⟩ := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (hQ p.y) k
  obtain ⟨er, her, cr, hcr, hter⟩ := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (QForm.rigK_val (ϖ := ϖ) D) k
  obtain ⟨tc, htc, hvtc⟩ := exists_cubN D.toPre.cub (1 : TO hϖ hv ⟶ D.toPre.P.A) m (cP D.toPre _ α) k
  let h₀ := (TO hϖ hv).hom
  let u := LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ e' h₀)
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ eψ h₀)))
    (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ er h₀))) tc)
    (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ G₀ k))
  have hu : u.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ he' _) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ heψ _)))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ her _))) htc) (invGen_isGen _ _ _ _ (powGen_isGen' _ _ _ _ hG₀ k))
  have hform1 : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      ∏ i, h (Sum.elim (Sum.elim (Sum.elim (Sum.elim (fun i => h₀ ≫ φV i) (fun i => h₀ ≫ (fun _ : PUnit => (D.toPre.c p.y).left) i))
        (fun i => h₀ ≫ (fun _ : PUnit => 𝟙 _ ≫ eSec D.toPre.P.A) i))
          (![((1 : TO hϖ hv ⟶ D.toPre.P.A) * m ^ k * cP D.toPre (TO hϖ hv) α).left,
            ((1 : TO hϖ hv ⟶ D.toPre.P.A) * m ^ k).left, ((1 : TO hϖ hv ⟶ D.toPre.P.A) * cP D.toPre (TO hϖ hv) α).left,
            (1 : TO hϖ hv ⟶ D.toPre.P.A).left, (m * cP D.toPre (TO hϖ hv) α).left, m.left,
            (cP D.toPre (TO hϖ hv) α).left, (1 : TO hϖ hv ⟶ D.toPre.P.A).left] :
            Fin 8 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left))) (gtφO hϖ hv m α) i) ^
        (Sum.elim (Sum.elim (Sum.elim (Sum.elim εV (fun i => -((k : ℤ) * (fun _ : PUnit => (-1 : ℤ)) i)))
          (fun i => -((k : ℤ) * (fun _ : PUnit => (1 : ℤ)) i)))
            (![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)] : Fin 8 → ℤ)) (fun i => -((k : ℤ) * DegPre.gtε i)) i) = 1 :=
    (fun U _ h => by
      have c1 : ∀ χ, (1 : TO hϖ hv ⟶ D.toPre.P.A).left ≫ (SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left = (cP D.toPre (TO hϖ hv) χ).left :=
        fun χ => by rw [← Over.comp_left, SectionScalarValuation.comp_cQ]; rfl
      have c2 : (1 : TO hϖ hv ⟶ D.toPre.P.A).left ≫ (SectionScalarValuation.cQ D.toPre D.toPre.P.A α * SectionScalarValuation.cQ D.toPre D.toPre.P.A p.y).left =
          (cP D.toPre (TO hϖ hv) α * cP D.toPre (TO hϖ hv) p.y).left := by
        rw [← Over.comp_left, MonObj.comp_mul, SectionScalarValuation.comp_cQ, SectionScalarValuation.comp_cQ]; rfl
      have c3 : (1 : TO hϖ hv ⟶ D.toPre.P.A).left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TO hϖ hv ⟶ D.toPre.P.A).left := by
        rw [← Over.comp_left, MonObj.comp_one]
      have c4 : ∀ i, (1 : TO hϖ hv ⟶ D.toPre.P.A).left ≫ D.toPre.P.A.hom ≫ φV i = h₀ ≫ φV i := fun i => by
        rw [← Category.assoc, Over.w]
      have E1 := hfe' U (fun ψ => h ((1 : TO hϖ hv ⟶ D.toPre.P.A).left ≫ ψ))
      simp only [c1, c2, c3, c4] at E1
      have htu : (toUnit (TO hϖ hv)).left = h₀ :=
        (Category.comp_id _).symm.trans (Over.w (toUnit (TO hϖ hv)))
      have c5 : h₀ ≫ (D.toPre.c p.y).left = (cP D.toPre (TO hϖ hv) p.y).left := by
        rw [cP, Over.comp_left, htu]
      have c6 : h₀ ≫ 𝟙 (𝟙_ (Over (Spec (CommRingCat.of V)))).left ≫ eSec D.toPre.P.A =
          (1 : TO hϖ hv ⟶ D.toPre.P.A).left := by
        rw [Hom.one_def]
        simp [eSec, htu]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, E1, c5, c6,
        Fin.prod_univ_succ, gtφO, DegPre.gtε, _root_.one_mul, hmk, zpow_neg, zpow_natCast,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
      rw [mul_comm m (cP D.toPre (TO hϖ hv) α), mul_comm (cP D.toPre (TO hϖ hv) p.y) (cP D.toPre (TO hϖ hv) α)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
  have hsurj : Function.Surjective (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)).hom := fun x => ⟨x, by simp⟩
  obtain ⟨a, ha⟩ : ∃ a : Γ((TO hϖ hv).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TO hϖ hv).left) (z : Z) (J),
      Good D.toPre.P.L z J → (val u r z J).val = gs (r ≫ 𝟙 _) z ⊤ a :=
    ReciprocityTheory.ChartRestriction.G.H1.exists_const D.toPre.P.L hL (𝟙 _) hsurj u hu (hform1)
  obtain ⟨a', ha'⟩ : ∃ a : Γ((TO hϖ hv).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TO hϖ hv).left) (z : Z) (J),
      Good D.toPre.P.L z J → (val (LB.invGen D.toPre.P.L _ _ u) r z J).val = gs (r ≫ 𝟙 _) z ⊤ a :=
    ReciprocityTheory.ChartRestriction.G.H1.exists_const D.toPre.P.L hL (𝟙 _) hsurj _ (invGen_isGen _ _ _ _ hu) (fun U _ h => by
      simp only [zpow_neg, Finset.prod_inv_distrib]; rw [inv_eq_one]; exact hform1 U h)
  let z₀ : Spec (CommRingCat.of F) := default
  choose J₀ hJ₀ using fun χ : (TF (R := V) F).left ⟶ D.toPre.P.A.left => exists_chart hL (χ z₀)
  have hG : Good D.toPre.P.L z₀ J₀ := hJ₀
  have h1 := ht _ (𝟙 _) z₀ J₀ hG
  have h2 := chain_val (𝟙 (TF (R := V) F)) hG p α
  have h3 := val_famMult (𝟙 (TF (R := V) F)) hG k p.y α
  have h4 := hve' F _ (𝟙 _) z₀ J₀ hG
  have h5 := val_genHasVal (hφ := fun _ => QForm.ptK_eq D.toPre p.y) hteψ ((𝟙 _) ≫ jFK (R := V) F) z₀ hG
  have h6 := val_genHasVal (hφ := fun _ => by rw [Category.id_comp]; rfl) hter ((𝟙 _) ≫ jFK (R := V) F) z₀ hG
  have h7 := hvtc (TF (R := V) F) (ιS hϖ hv) z₀ J₀ hG
  have h8 := ha _ (ιS hϖ hv).left z₀ J₀ hG
  have h8' := ha' _ (ιS hϖ hv).left z₀ J₀ hG
  have hι : (ιS hϖ hv).left ≫ (TO hϖ hv).hom = DegPre.jFR (R := V) F := Over.w (ιS hϖ hv)
  have hid : Over.Hom.left (𝟙 (TF (R := V) F)) = 𝟙 (Spec (CommRingCat.of F)) := Over.id_left _
  rw [hid] at h2 h3
  simp only [Category.id_comp] at h1 h2 h3 h4 h5 h6 h8 h8'

  have hu8 : val u (ιS hϖ hv).left z₀ J₀ = val (Z := (TF (R := V) F).left) e' (DegPre.jFR (R := V) F) z₀ J₀ *
      (val (Z := (TF (R := V) F).left) eψ (DegPre.jFR (R := V) F) z₀ J₀)⁻¹ *
      (val (Z := (TF (R := V) F).left) er (DegPre.jFR (R := V) F) z₀ J₀)⁻¹ *
      val tc (ιS hϖ hv).left z₀ J₀ * (val G₀ (ιS hϖ hv).left z₀ J₀ ^ k)⁻¹ := by
    simp only [u, h₀, val_mul hG, val_inv, val_pull hG, val_powGen, hι]
  have h7' : val tc (ιS hϖ hv).left z₀ J₀ = cubN (th D.toPre z₀ J₀) k 1 p.g.b (cP D.toPre (TF (R := V) F) α) := by
    rw [h7, MonObj.comp_one, hm, comp_cP]

  have hjF : (𝟙 (Spec (CommRingCat.of F)) ≫ jFK (R := V) F) = jFK (R := V) F := Category.id_comp _
  have hjR : jFK (R := V) F ≫ jK V = DegPre.jFR (R := V) F := rfl
  rw [hjF] at h2 h3
  rw [hjR] at h5 h6
  have hu8' : (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀)ˣ (val u (ιS hϖ hv).left z₀ J₀)) * val eψ (DegPre.jFR (R := V) F) z₀ J₀ *
      val er (DegPre.jFR (R := V) F) z₀ J₀ *
      (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀)ˣ (val G₀ (ιS hϖ hv).left z₀ J₀)) ^ k =
      val e' (DegPre.jFR (R := V) F) z₀ J₀ *
      (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀)ˣ (val tc (ιS hϖ hv).left z₀ J₀)) := by
    rw [hu8]
    simp only [id]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  have hU := congrArg Units.val hu8'
  have hchain := congrArg Units.val (show val (DegPre.famMult D.toPre F k p.y α) (𝟙 (Spec (CommRingCat.of F))) z₀ J₀ *
      (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀)ˣ (val tc (ιS hϖ hv).left z₀ J₀)) =
      val (p.g.s α) (𝟙 (Spec (CommRingCat.of F))) z₀ J₀ ^ k *
      (val (GeneratorPullback.powGen D.toPre.P.L (fun _ => ptK (D.toPre.c p.y)) (fun _ => -1) (D.toPre.psi p.y) k)
          (jFK (R := V) F) z₀ J₀ *
        val (GeneratorPullback.powGen D.toPre.P.L (fun _ => Over.Hom.left (toUnit (TK V)) ≫ eSec D.toPre.P.A) (fun _ => 1)
          D.toPre.rigK k) (jFK (R := V) F) z₀ J₀) by
    simp only [id]
    rw [h3, h7', ← h2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel)
  push_cast [Units.val_mul, Units.val_pow_eq_pow_val] at hU hchain
  simp only [id] at hU hchain
  rw [h4, h5, h6] at hchain
  rw [h8] at hU
  have h1' : ((val (p.g.s α) (𝟙 (Spec (CommRingCat.of F))) z₀ J₀ :
      ((Spec (CommRingCat.of F)).presheaf.stalk z₀)ˣ) : (Spec (CommRingCat.of F)).presheaf.stalk z₀) =
      gs (𝟙 (Spec (CommRingCat.of F))) z₀ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀) ((val G₀ (ιS hϖ hv).left z₀ J₀ : ((TF (R := V) F).left.presheaf.stalk z₀)ˣ) : (TF (R := V) F).left.presheaf.stalk z₀)) := h1
  rw [h1'] at hchain
  simp only [id] at hchain
  have hw : IsUnit ((val eψ (DegPre.jFR (R := V) F) z₀ J₀ : (Spec (CommRingCat.of F)).presheaf.stalk z₀) *
      (val er (DegPre.jFR (R := V) F) z₀ J₀ : (Spec (CommRingCat.of F)).presheaf.stalk z₀) *
      (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀) ((val G₀ (ιS hϖ hv).left z₀ J₀ : ((TF (R := V) F).left.presheaf.stalk z₀)ˣ) : (TF (R := V) F).left.presheaf.stalk z₀)) ^ k) :=
    ((Units.isUnit _).mul (Units.isUnit _)).mul ((Units.isUnit _).pow k)
  have hring : gs (𝟙 (Spec (CommRingCat.of F))) z₀ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) ^ k *
      gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) cψ) *
      gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) cr) =
      gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (TK V).left) c₀) *
      (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀) (gs ((ιS hϖ hv).left ≫ 𝟙 (TO hϖ hv).left) z₀ ⊤ a)) := by
    apply (hw.mul_left_inj).mp
    simp only [id]
    linear_combination (-1 : (Spec (CommRingCat.of F)).presheaf.stalk z₀) * hchain -
      gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (TK V).left) c₀) * hU

  let ev : F →+* (Spec (CommRingCat.of F)).presheaf.stalk z₀ :=
    ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z₀ trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hev : Function.Injective ev := ev.injective
  have gs_id : ∀ x : F,
      gs (𝟙 (Spec (CommRingCat.of F))) z₀ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) = ev x := by
    intro x
    rw [gs_eq (𝟙 (Spec (CommRingCat.of F))) z₀ ⊤ trivial]
    rfl
  have gs_K : ∀ c : FractionRing V,
      gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) =
        ev (algebraMap (FractionRing V) F c) := by
    intro c
    rw [← gs_id, ← Category.id_comp (jFK (R := V) F), ← gs_pull _ _ z₀ ⊤ trivial]
    congr 1
    show (jFK (R := V) F).appTop.hom _ = _
    rw [appTop_specMap]
    simp [scal]
  have gs_A : ∀ r : Γ((TO hϖ hv).left, ⊤),
      gs ((ιS hϖ hv).left ≫ 𝟙 (TO hϖ hv).left) z₀ ⊤ r = ev (ιr (v := v) r) := by
    intro r
    rw [Category.comp_id, ← gs_id, ← Category.id_comp (ιS hϖ hv).left, ← gs_pull _ _ z₀ ⊤ trivial]
    congr 1
    show (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))).appTop.hom r = _
    rw [appTop_specMap]
    rfl
  have hK0 : gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (TK V).left) c₀) = ev (algebraMap (FractionRing V) F c₀) :=
    gs_K c₀
  simp only [id] at hring
  rw [gs_id, gs_K, gs_K, hK0, gs_A, ← map_pow, ← map_mul, ← map_mul, ← map_mul] at hring
  have hF := hev hring

  have hinv := h8'
  rw [val_inv] at hinv
  have hAA : ev (ιr (v := v) a) * ev (ιr (v := v) a') = 1 := by
    rw [← gs_A, ← gs_A]
    rw [← h8, ← hinv]
    exact Units.mul_inv _
  rw [← map_mul, ← map_one ev] at hAA
  have hff := hev hAA

  have hvf : v (ιr (v := v) a) = 0 := by
    have h0 : v (ιr (v := v) a) + v (ιr (v := v) a') = 0 := by
      rw [← AddValuation.map_mul, hff, AddValuation.map_one]
    exact le_antisymm (le_zero_of_add_eq_zero_nonneg h0 (v_ιr a')) (v_ιr a)
  have hvψ := hv cψ _ hcψ
  have hvr := hv cr _ hcr
  have hv0 := hv c₀ _ hc₀
  have hvF := congrArg v hF
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, hvψ, hvr, hv0,
    hvf] at hvF
  have ht0 : v t ≠ ⊤ := by
    intro htop
    have htz : t = 0 := (AddValuation.top_iff v).mp htop
    have hc0 : algebraMap (FractionRing V) F c₀ ≠ 0 := by
      intro h0
      have h00 := hv0
      rw [h0, AddValuation.map_zero] at h00
      exact WithTop.top_ne_coe h00
    have hf0 : ιr (v := v) a ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hff
      exact zero_ne_one hff
    rw [htz, zero_pow (by omega), zero_mul, zero_mul] at hF
    exact mul_ne_zero hc0 hf0 hF.symm
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ht0
  refine ⟨q, hq.symm, ?_⟩
  rw [← hq] at hvF
  have hQ' : (((k • q + ((k * Q p.y : ℤ) : ℚ) + ((k * 0 : ℤ) : ℚ)) : ℚ) : WithTop ℚ) =
      ((((k * Q p.y + QForm.bOf D.toPre Q p.y α : ℤ) : ℚ)) : WithTop ℚ) := by
    rw [WithTop.coe_add, WithTop.coe_add, WithTop.coe_nsmul, hvF, add_zero]
  have h := WithTop.coe_injective hQ'
  rw [nsmul_eq_mul] at h
  push_cast at h
  linarith

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
