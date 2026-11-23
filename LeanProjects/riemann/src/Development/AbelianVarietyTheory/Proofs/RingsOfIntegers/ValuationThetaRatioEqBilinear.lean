import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsValGenHasVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatioVal

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

def germConst (F : Type) [Field F] (z : Spec (CommRingCat.of F)) : F →+* (Spec (CommRingCat.of F)).presheaf.stalk z :=
  ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem gs_specMap {A F : Type} [CommRing A] [Field F] (f : A →+* F) (z : Spec (CommRingCat.of F))
    (a : Γ(Spec (CommRingCat.of A), ⊤)) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ a = germConst F z (f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a)) := by
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom (appTop_specMap (CommRingCat.ofHom f) a)

theorem gs_id_const {F : Type} [Field F] (z : Spec (CommRingCat.of F)) (c : F) :
    gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) = germConst F z c := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem gs_scal {A F : Type} [CommRing A] [Field F] (f : A →+* F) (z : Spec (CommRingCat.of F)) (c : A) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ (scal (𝟙 (Spec (CommRingCat.of A))) c) = germConst F z (f c) := by
  rw [gs_specMap]
  congr 2
  simp [scal]

theorem unit_calc {S : Type} [CommRing S] {s G τ C P R E Eψ Er fam u : Sˣ} {T c₀ cψ cr A : S} {k : ℕ}
    (h1 : s.val = T * G.val) (h2 : τ * C = s ^ k) (h3 : fam = τ * (P * R)) (h4 : fam.val = c₀ * E.val)
    (h5 : P.val = cψ * Eψ.val) (h6 : R.val = cr * Er.val) (h8 : u.val = A)
    (hu : u = E * Eψ⁻¹ * Er⁻¹ * C * (G ^ k)⁻¹) : c₀ * A = T ^ k * cψ * cr := by
  have e1 : u * (Eψ * Er * G ^ k) = E * C := by
    rw [hu]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have e2 : fam * C = s ^ k * (P * R) := by rw [h3, ← h2]; ac_rfl
  have e1' := congrArg Units.val e1
  have e2' := congrArg Units.val e2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, h1, h4, h5, h6, h8, mul_pow] at e1' e2'
  apply (Eψ * Er * G ^ k).isUnit.mul_right_cancel
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  linear_combination c₀ * e1' + e2'

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
  let h₀ : (TO hϖ hv).left ⟶ Spec (CommRingCat.of V) := (TO hϖ hv).hom
  let u := LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ e' h₀)
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ eψ h₀)))
    (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ er h₀))) tc)
    (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ G₀ k))
  have hu : u.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ he' _) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ heψ _)))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ her _))) htc) (invGen_isGen _ _ _ _ (powGen_isGen' _ _ _ _ hG₀ k))
  have hsurj : Function.Surjective (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)).hom := fun x => ⟨x, by simp⟩
  have hfs : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      (((((∏ i, h (h₀ ≫ φV i) ^ εV i) * (h (cP D.toPre (TO hϖ hv) p.y).left ^ ((k : ℤ) * -1))⁻¹) *
        (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ ((k : ℤ) * 1))⁻¹) *
        ∏ i, h (![(1 * m ^ k * cP D.toPre _ α).left, (1 * m ^ k).left, (1 * cP D.toPre _ α).left,
          (1 : TO hϖ hv ⟶ D.toPre.P.A).left, (m * cP D.toPre _ α).left, m.left, (cP D.toPre _ α).left,
          (1 : TO hϖ hv ⟶ D.toPre.P.A).left] i) ^ (![1, -1, -1, 1, -k, k, k, -k] : Fin 8 → ℤ) i) *
        (∏ i, h (gtφO hϖ hv m α i) ^ ((k : ℤ) * DegPre.gtε i))⁻¹) = 1 := by
    intro U _ h
    let o : TO hϖ hv ⟶ D.toPre.P.A := 1
    have e := hfe' U (fun q => h (o.left ≫ q))
    have w : o.left ≫ D.toPre.P.A.hom = h₀ := Over.w o
    have q₀ : ∀ i, o.left ≫ D.toPre.P.A.hom ≫ φV i = h₀ ≫ φV i := fun i => by rw [← Category.assoc, w]
    have q₁ : ∀ χ, o.left ≫ (cQ D.toPre D.toPre.P.A χ).left = (cP D.toPre (TO hϖ hv) χ).left := fun χ =>
      congrArg (fun q : TO hϖ hv ⟶ D.toPre.P.A => q.left) (comp_cP D.toPre o χ)
    have q₂ : o.left ≫ (cQ D.toPre D.toPre.P.A α * cQ D.toPre D.toPre.P.A p.y).left =
        (cP D.toPre (TO hϖ hv) α * cP D.toPre (TO hϖ hv) p.y).left :=
      congrArg (fun q : TO hϖ hv ⟶ D.toPre.P.A => q.left) ((MonObj.comp_mul o _ _).trans
        (congrArg₂ (· * ·) (comp_cP D.toPre o α) (comp_cP D.toPre o p.y)))
    have q₃ : o.left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TO hϖ hv ⟶ D.toPre.P.A).left :=
      congrArg (fun q : TO hϖ hv ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) o)
    simp only [q₀, q₁, q₂, q₃] at e
    rw [e, hmk, _root_.one_mul, _root_.one_mul, mul_comm (cP D.toPre (TO hϖ hv) p.y), mul_comm m]
    apply Additive.ofMul.injective
    simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, gtφO, DegPre.gtε]
    module
  have pψ : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      ∏ _i : PUnit.{1}, h (h₀ ≫ (D.toPre.c p.y).left) ^ ((k : ℤ) * -1) =
        h (cP D.toPre (TO hϖ hv) p.y).left ^ ((k : ℤ) * -1) := fun U _ h => by
    rw [Fintype.prod_unique]
    rfl
  have pr : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      ∏ _i : PUnit.{1}, h (h₀ ≫ 𝟙 _ ≫ eSec D.toPre.P.A) ^ ((k : ℤ) * 1) =
        h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ ((k : ℤ) * 1) := fun U _ h => by
    rw [Fintype.prod_unique, Hom.one_def]
    rfl
  obtain ⟨a, ha⟩ : ∃ a : Γ((TO hϖ hv).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TO hϖ hv).left) (z : Z) (J),
      Good D.toPre.P.L z J → (val u r z J).val = gs (r ≫ 𝟙 _) z ⊤ a :=
    ReciprocityTheory.ChartRestriction.G.H1.exists_const D.toPre.P.L hL (𝟙 _) hsurj u hu (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [pψ U h, pr U h]
      exact hfs U h)
  obtain ⟨a', ha'⟩ : ∃ a : Γ((TO hϖ hv).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TO hϖ hv).left) (z : Z) (J),
      Good D.toPre.P.L z J → (val (LB.invGen D.toPre.P.L _ _ u) r z J).val = gs (r ≫ 𝟙 _) z ⊤ a :=
    ReciprocityTheory.ChartRestriction.G.H1.exists_const D.toPre.P.L hL (𝟙 _) hsurj _ (invGen_isGen _ _ _ _ hu) (fun U _ h => by
      refine (prod_neg _ _ ?_).trans inv_one
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [pψ U h, pr U h]
      exact hfs U h)
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
  have key := unit_calc h1 (h7' ▸ h2) h3 h4 h5 h6 h8 hu8
  have g1 : gs (𝟙 (TF (R := V) F).left) z₀ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) = germConst F z₀ t :=
    gs_id_const z₀ t
  have g2 : ∀ c : FractionRing V, gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 _) c) =
      germConst F z₀ (algebraMap (FractionRing V) F c) := fun c => gs_scal _ z₀ c
  have g3 : ∀ b : Γ((TO hϖ hv).left, ⊤), gs ((ιS hϖ hv).left ≫ 𝟙 _) z₀ ⊤ b = germConst F z₀ (ιr (v := v) b) := fun b => by
    rw [Category.comp_id]; exact gs_specMap _ z₀ b
  have hinj : Function.Injective (germConst F z₀) := (germConst F z₀).injective
  have k1 : algebraMap (FractionRing V) F c₀ * ιr (v := v) a =
      t ^ k * algebraMap (FractionRing V) F cψ * algebraMap (FractionRing V) F cr := by
    apply hinj
    simp only [map_mul, map_pow]
    rw [← g1, ← g2, ← g2, ← g2, ← g3]
    exact key
  have k2 : ιr (v := v) a * ιr (v := v) a' = 1 := by
    apply hinj
    rw [map_mul, map_one, ← g3, ← g3, ← h8, ← h8', val_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have va : v (ιr (v := v) a) = 0 := by
    have e : v (ιr (v := v) a) + v (ιr (v := v) a') = 0 := by rw [← AddValuation.map_mul, k2, AddValuation.map_one]
    exact le_antisymm (le_zero_of_add_eq_zero_nonneg e (v_ιr a')) (v_ιr a)
  have k3 := congrArg v k1
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, va, hv _ _ hc₀,
    hv _ _ hcψ, hv _ _ hcr] at k3
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [g1, map_zero, zero_mul] at h1
    exact (val (p.g.s α) (𝟙 _) z₀ J₀).ne_zero h1
  obtain ⟨q, hq⟩ := wt_coe_of_ne (v := v) ht0
  refine ⟨q, hq, ?_⟩
  rw [hq] at k3
  have k4 : (((k : ℤ) * Q p.y + QForm.bOf D.toPre Q p.y α : ℤ) : ℚ) + 0 =
      k • q + (((k : ℤ) * Q p.y : ℤ) : ℚ) + (((k : ℤ) * 0 : ℤ) : ℚ) := by exact_mod_cast k3
  rw [nsmul_eq_mul] at k4
  push_cast at k4
  linarith

theorem main : TWM.VRatioGtStatement :=
  fun _ _ _ _ _ hϖ _ _ hQ _ _ _ _ hv _ hk p m hm α G₀ hG₀ t ht => v_ratio_gt hϖ hv hQ hk p m hm α G₀ hG₀ t ht

end GlobalTheory.RatioVal
