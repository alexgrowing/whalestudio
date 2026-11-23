import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiValue

open ReciprocityTheory.ChartRestriction.G.DVR.TWM ReciprocityTheory.ChartRestriction.G.DVR.TWO ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation ReciprocityTheory.ChartRestriction.G.DVR.QForm ReciprocityTheory.ChartRestriction.G.DVR.PeriodicValuation

theorem shift_explicit (hG : GlobalFnsSt) (hTW : TwistBCSpanStatement) (hVR : VRatioGtStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ) (hQ : IsQ D.toPre ϖ Q)
    (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v)
    (k : ℕ) (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (ζ : F) (hζ : ζ ≠ 0) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = p.g.b)
    (W₀ : LB.Gen (LB.LinComb D.toPre.P.L (lineφO hϖ hv m) (DegPre.lineε k))) (hW₀ : W₀.IsGen)
    (lam : F) (hlam0 : lam ≠ 0)
    (hlam' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val w r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom lam) *
        (val W₀ (r ≫ (ιS hϖ hv).left) z J).val)
    (qz ql : ℚ) (hqz : v ζ = (qz : WithTop ℚ)) (hql : v lam = (ql : WithTop ℚ)) :
    ∀ s t s' : Fam D.toPre F k, PhiRel D.toPre F k p w s t → Fam.IsSmul D.toPre F ζ t s' →
      ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' (r + (qz + ql - (Q p.y : ℚ) / k)) := by
  classical
  have hL := D.toPre.P.isLB
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hmy : cP D.toPre (TO hϖ hv) p.y = m ^ k := liftO_unique hϖ hv _ _ (by
    rw [comp_cP, cPoint_y, ← hm]; exact (map_pow (preHom (ιS hϖ hv)) m k).symm)
  choose G₀ hG₀ using fun α => exists_gen_of_local D.toPre.P.L hL (gtφO hϖ hv m α) DegPre.gtε
  have hg : ∀ α i, DegPre.gtφ D.toPre F p.g.b α i = (ιS hϖ hv).left ≫ gtφO hϖ hv m α i := by
    intro α i; fin_cases i
    · show (padd D.toPre.P.A (DegPre.cF D.toPre F α) p.g.b).left = (ιS hϖ hv).left ≫ (cP D.toPre _ α * m).left
      rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hm]; rfl
    · show (DegPre.cF D.toPre F α).left = (ιS hϖ hv).left ≫ (cP D.toPre _ α).left
      rw [← Over.comp_left, comp_cP]; rfl
    · show p.g.b.left = (ιS hϖ hv).left ≫ m.left
      rw [← Over.comp_left, hm]
    · show (DegPre.zeroF D.toPre F).left = (ιS hϖ hv).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left
      rw [← Over.comp_left, MonObj.comp_one]; rfl
  choose t ht0 ht using fun α => exists_ratio hL (p.g.s α) (p.g.isGen α)
    (LB.pullGen D.toPre.P.L _ _ (G₀ α) (ιS hϖ hv).left) (pullGen_isGen _ _ _ _ (hG₀ α) _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hg])
  have ht' : ∀ α (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (t α)) *
        (val (G₀ α) (r ≫ (ιS hϖ hv).left) z J).val := fun α Z r z J hJ => by
    rw [ht α Z r z J hJ, val_pull hJ]
  choose q hq hkq using fun α => hVR V ϖ hϖ D Q hQ F v hv k hk p m hm α (G₀ α) (hG₀ α) (t α) (ht' α)
  choose u hu hc using fun α => (gen_phi hG p w hw α).1
  have hF : ∀ α (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      ∏ i, h (Sum.elim (gtφO hϖ hv m α) (lineφO hϖ hv m) i) ^ (Sum.elim DegPre.gtε (DegPre.lineε k) i) =
        (h (cP D.toPre _ α * m).left)⁻¹ * h (cP D.toPre _ α).left * h m.left *
          (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left)⁻¹ * (h m.left ^ k)⁻¹ * h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ k :=
    fun α U _ h => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two]
      show h (cP D.toPre _ α * m).left ^ (-1 : ℤ) * h (cP D.toPre _ α).left ^ (1 : ℤ) * h m.left ^ (1 : ℤ) *
        h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ (-1 : ℤ) *
        (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ (k : ℤ) * h m.left ^ (-(k : ℤ))) = _
      simp only [zpow_neg, zpow_one, zpow_natCast]
      ac_rfl
  choose eO heO heOv using fun α => gen_uO hϖ hv k α (α + p.y) m (by rw [cPoint_add, hmy])
    (LB.mulGen D.toPre.P.L _ _ _ _ (G₀ α) W₀) (mulGen_isGen _ _ _ _ _ _ _ (hG₀ α) hW₀) (hF α)
  have hcg : ∀ α (T : Over (Spec (CommRingCat.of V))) (ρ : T ⟶ DegPre.BF D.toPre F) (z : T.left) (J),
      Good D.toPre.P.L z J → (val (u α) ρ.left z J).val =
        gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (t α * lam)) *
          (val (eO α) (ρ ≫ jO hϖ hv).left z J).val := by
    intro α T ρ z J hJ
    have e₁ := (gen_phi hG p w hw α).2 (u α) (hu α) (hc α) T ρ z J hJ
    have e₂ := heOv α T (ρ ≫ jO hϖ hv) z J hJ
    have p₁ : (ρ ≫ jO hϖ hv) ≫ fst _ _ ≫ m = ρ ≫ fst _ _ ≫ p.g.b := by
      rw [Category.assoc, ← Category.assoc (jO hϖ hv), whiskerRight_fst, Category.assoc, hm]
    have p₂ : (ρ ≫ jO hϖ hv) ≫ snd _ _ = ρ ≫ DegPre.prB D.toPre F := by
      rw [Category.assoc, whiskerRight_snd]
    have p₃ : ((ρ ≫ jO hϖ hv) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (ιS hϖ hv).left := by
      rw [Category.assoc, whiskerRight_fst]; rfl
    rw [p₁, p₂, p₃, val_mul hJ] at e₂
    rw [e₁, e₂, uVal, val_mul hJ]
    simp only [Units.val_mul]
    rw [ht' α _ _ z J hJ, hlam' _ _ z J hJ, map_mul, gs_mul _ z ⊤ trivial]
    ring
  have hgF : ∀ (c : F) (y : (DegPre.BF D.toPre F).left),
      gs (𝟙 _) y ⊤ (gF D.toPre F c) = gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) := fun c y => by
    rw [gF, RingHom.comp_apply]
    exact (gs_pull (𝟙 _) (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ trivial _).trans (by rw [Category.id_comp])
  have shift : ∀ α : D.toPre.X, (Q α : ℚ) / k + (q α + ql) + qz =
      (qz + ql - (Q p.y : ℚ) / k) + (Q (α + p.y) : ℚ) / k := by
    intro α
    have h1 := hkq α
    have hq' : q α = ((Q (p.y + α) : ℚ) - Q p.y - Q α) / k := by
      rw [eq_div_iff hk0]
      simp only [bOf] at h1
      push_cast at h1
      linarith
    rw [hq', add_comm α p.y]
    ring
  intro s t' s' hst hts r
  constructor
  · intro hs χ
    obtain ⟨α, rfl⟩ : ∃ α, α + p.y = χ := ⟨χ - p.y, sub_add_cancel _ _⟩
    have h1 := vge_moveO hϖ hv hTW hk (h := (DegPre.trPt D.toPre F p.g.b).left) (H := (trO hϖ hv m).left)
      (by rw [← Over.comp_left, tr_fst])
      (by rw [← Over.comp_left, ← Over.comp_left, jO_trO hϖ hv p.g.b m hm])
      (u α) (hst α (u α) (hu α) (hc α)) (eO α) (heO α)
      (fun U _ h => by
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib, Over.comp_left,
          Category.assoc]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
      (t α * lam) (fun y J hJ => by
        have e := hcg α _ (𝟙 _) y J hJ
        rw [Over.id_left, Category.id_comp, Category.id_comp] at e
        rw [e, hgF])
      (r := r + (Q α : ℚ) / k) (q := q α + ql)
      (by rw [AddValuation.map_mul, hq α, hql, ← WithTop.coe_add])
      (hs α)
    have h2 := VGe.smul h1 (q := qz) (ζ := ζ) (le_of_eq hqz.symm) (fun j => hts (α + p.y) j)
    refine VGe.mono h2 (le_of_eq ?_)
    linarith [shift α]
  · intro hs' α
    have hvi : v ζ⁻¹ = ((-qz : ℚ) : WithTop ℚ) := v_inv_coe (v := v) hζ hqz
    have h1 := VGe.smul (hs' (α + p.y)) (s' := t'.s (α + p.y)) (q := -qz) (ζ := ζ⁻¹) (le_of_eq hvi.symm) (fun j => by
      rw [hts (α + p.y) j, ← _root_.mul_assoc, ← constBF_mul, inv_mul_cancel₀ hζ, DVR.constBF_eq, map_one]
      simp [resTop])
    have hb1 : ιS hϖ hv ≫ m⁻¹ = p.g.b⁻¹ := by rw [← hm]; exact map_inv (preHom (ιS hϖ hv)) m
    have htt : DegPre.trPt D.toPre F p.g.b⁻¹ ≫ DegPre.trPt D.toPre F p.g.b = 𝟙 _ := by
      rw [H1.trPt_mul, inv_mul_cancel, H1.trPt_one]
    have hOO : trO hϖ hv m⁻¹ ≫ trO hϖ hv m = 𝟙 _ := by rw [trO_mul, inv_mul_cancel, trO_one]
    let u' := LB.pullGen D.toPre.P.L _ _ (LB.invGen D.toPre.P.L _ _ (u α)) (DegPre.trPt D.toPre F p.g.b⁻¹).left
    have hrel' : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
        (DegPre.famφ D.toPre F (α + p.y)) (DegPre.famε k) (t'.s (α + p.y)) (DegPre.trPt D.toPre F p.g.b⁻¹).left
        _ _ u' := by
      refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u').2 fun y J hJ => ?_
      have e := (secRel_iff hL _ _ _ _ _ _ _ _ _ (u α)).1 (hst α (u α) (hu α) (hc α)) _
        (DegPre.trPt D.toPre F p.g.b⁻¹).left y J hJ
      rw [← Over.comp_left, htt, Over.id_left] at e
      rw [Category.id_comp, e, val_pull hJ, val_inv, Category.id_comp, _root_.mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, _root_.mul_one]
    let eO' := LB.pullGen D.toPre.P.L _ _ (LB.invGen D.toPre.P.L _ _ (eO α)) (trO hϖ hv m⁻¹).left
    have hM : ∀ {Y : Scheme.{0}} (φ : D.toPre.P.A.left ⟶ Y), (trO hϖ hv m⁻¹).left ≫ (trO hϖ hv m ≫ snd _ _).left ≫ φ =
        (snd (TO hϖ hv) D.toPre.P.A).left ≫ φ := fun φ => by
      rw [← Category.assoc, ← Over.comp_left, ← Category.assoc, hOO, Category.id_comp]
    obtain ⟨qc, hqc⟩ : ∃ qc : ℚ, v (t α * lam) = qc := ⟨q α + ql, by rw [AddValuation.map_mul, hq α, hql, ← WithTop.coe_add]⟩
    have h2 := vge_moveO hϖ hv hTW hk (h := (DegPre.trPt D.toPre F p.g.b⁻¹).left) (H := (trO hϖ hv m⁻¹).left)
      (by rw [← Over.comp_left, tr_fst])
      (by rw [← Over.comp_left, ← Over.comp_left, jO_trO hϖ hv p.g.b⁻¹ m⁻¹ hb1])
      u' hrel' eO' (pullGen_isGen _ _ _ _ (invGen_isGen _ _ _ _ (heO α)) _)
      (fun U _ h => by
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, neg_neg, Finset.prod_inv_distrib, hM,
          Category.assoc]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
      (t α * lam)⁻¹ (fun y J hJ => by
        have e := hcg α _ (DegPre.trPt D.toPre F p.g.b⁻¹) y J hJ
        have f1 : (DegPre.trPt D.toPre F p.g.b⁻¹ ≫ fst (TF (R := V) F) D.toPre.P.A).left =
            (fst (TF (R := V) F) D.toPre.P.A).left := by rw [tr_fst]
        have f2 : (DegPre.trPt D.toPre F p.g.b⁻¹ ≫ jO hϖ hv).left = (jO hϖ hv).left ≫ (trO hϖ hv m⁻¹).left := by
          rw [← jO_trO hϖ hv p.g.b⁻¹ m⁻¹ hb1]; rfl
        rw [f1, f2] at e
        rw [hgF, val_pull hJ, val_inv, val_pull hJ, val_inv, Category.id_comp]
        have hgg : gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (t α * lam)) *
            gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (t α * lam)⁻¹) = 1 := by
          rw [← gs_mul _ y ⊤ trivial, ← map_mul, mul_inv_cancel₀ (mul_ne_zero (ht0 α) hlam0), map_one]
          have h1 := gs_unit (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ trivial 1
          rwa [Units.val_one, map_one, Units.val_one] at h1
        have hAi := Units.inv_mul (val (u α) (DegPre.trPt D.toPre F p.g.b⁻¹).left y J)
        have hEi := Units.inv_mul (val (eO α) ((jO hϖ hv).left ≫ (trO hϖ hv m⁻¹).left) y J)
        linear_combination (-(((val (u α) (DegPre.trPt D.toPre F p.g.b⁻¹).left y J)⁻¹ : _ˣ).val)) * hgg +
          (-(((val (u α) (DegPre.trPt D.toPre F p.g.b⁻¹).left y J)⁻¹ : _ˣ).val *
            gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (t α * lam)) *
            gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (t α * lam)⁻¹))) * hEi +
          (gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (t α * lam)⁻¹) *
            ((val (eO α) ((jO hϖ hv).left ≫ (trO hϖ hv m⁻¹).left) y J)⁻¹ : _ˣ).val *
            ((val (u α) (DegPre.trPt D.toPre F p.g.b⁻¹).left y J)⁻¹ : _ˣ).val) * (-1 : _) * e +
          (gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (t α * lam)⁻¹) *
            ((val (eO α) ((jO hϖ hv).left ≫ (trO hϖ hv m⁻¹).left) y J)⁻¹ : _ˣ).val) * hAi)
      (r := r + (qz + ql - (Q p.y : ℚ) / k) + (Q (α + p.y) : ℚ) / k + -qz) (q := -qc)
      (le_of_eq (v_inv_coe (v := v) (mul_ne_zero (ht0 α) hlam0) hqc).symm)
      h1
    refine VGe.mono h2 (le_of_eq ?_)
    have hqc' : qc = q α + ql := by
      have e : ((qc : ℚ) : WithTop ℚ) = ((q α + ql : ℚ) : WithTop ℚ) := by
        rw [← hqc, AddValuation.map_mul, hq α, hql, ← WithTop.coe_add]
      exact_mod_cast e
    rw [hqc']
    linarith [shift α]

theorem exists_finite (hUU : UUStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ) (hQ : IsQ D.toPre ϖ Q)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ))
    (hv : ValOver ϖ F v) (k : ℕ) (hk : 1 ≤ k) :
    ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ ¬ NuGe D Q F v k s 1 := by
  classical
  obtain ⟨b, hli, hb, hUU'⟩ := hUU V ϖ hϖ D Q hQ F v hv (Or.inl inferInstance) k hk
  let i₀ : Fin (k ^ (D.toPre.rank + D.toPre.P.g)) := ⟨0, Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))⟩
  refine ⟨b i₀, hb i₀, fun h1 => ?_⟩
  have hx : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)) = ((1 : ℚ) : WithTop ℚ) := by
    have := hv (algebraMap V (FractionRing V) ϖ) 1 ⟨1, by simp⟩
    simpa using this
  set x := algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ) with hxd
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at hx
    exact WithTop.top_ne_coe hx
  have hxi := v_inv_coe (v := v) hx0 hx
  have h2 := NuGe.smul Q (le_of_eq hxi.symm) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff x⁻¹ (b i₀) _).2 rfl) h1
  rw [add_neg_cancel] at h2
  obtain ⟨c, hc, he⟩ := (hUU' _).1 h2
  have h3 : (Pi.single i₀ x⁻¹ : _ → F) = c := by
    refine hli.fintypeLinearCombination_injective ?_
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, ← he,
      Finset.sum_eq_single i₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp),
      Pi.single_eq_same]
  have h4 := hc i₀
  rw [← h3, Pi.single_eq_same, hxi] at h4
  have h5 : (0 : ℚ) ≤ -1 := by exact_mod_cast h4
  norm_num at h5

theorem shift_zero (hL : Laws) (hUU : UUStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ) (hQ : IsQ D.toPre ϖ Q)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ))
    (hv : ValOver ϖ F v) (k : ℕ) (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (ζ : F) (hfin : FinOrd D F k p w ζ) (c : ℚ)
    (hc : ∀ s t s' : Fam D.toPre F k, PhiRel D.toPre F k p w s t → Fam.IsSmul D.toPre F ζ t s' →
      ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' (r + c)) : c = 0 := by
  obtain ⟨s, hs0, hs1⟩ := exists_finite hUU V ϖ hϖ D Q hQ F v hv k hk
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hL.globalFns V (maximalIdeal V) D F k hk p w hw
  let U : Fam D.toPre F k → Fam D.toPre F k := fun x => ζ • Φ x
  have hstep : ∀ x r, NuGe D Q F v k x r ↔ NuGe D Q F v k (U x) (r + c) := fun x r =>
    hc x (Φ x) (U x) ((hΦ x (Φ x)).2 rfl) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff ζ (Φ x) (U x)).2 rfl) r
  obtain ⟨M, hM1, hM⟩ := hfin
  have hcyc : ∀ x, U^[M] x = x := by
    intro x
    have h := hM (fun i => U^[i.val] x) (fun i => Φ (U^[i.val] x)) (fun i =>
      ⟨(hΦ _ _).2 rfl, (ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff ζ _ _).2 (by
        show U^[i.val + 1] x = ζ • Φ (U^[i.val] x)
        rw [Function.iterate_succ_apply'])⟩)
    exact ReciprocityTheory.ChartRestriction.G.DVR.fam_ext fun α j => h α j
  have hiter : ∀ (n : ℕ) (x : Fam D.toPre F k) (r : ℚ),
      NuGe D Q F v k x r ↔ NuGe D Q F v k (U^[n] x) (r + n * c) := by
    intro n
    induction n with
    | zero => intro x r; simp
    | succ n ih =>
      intro x r
      have e : r + ((n + 1 : ℕ) : ℚ) * c = r + n * c + c := by push_cast; ring
      rw [ih x r, hstep (U^[n] x) (r + n * c), ← e, Function.iterate_succ_apply']
  have hmono : ∀ r r' : ℚ, r' ≤ r → NuGe D Q F v k s r → NuGe D Q F v k s r' :=
    fun r r' h hs => NuGe.mono (h := hs) (hr := h)
  by_contra hc0
  have hd : (M : ℚ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast (show M ≠ 0 by omega)) hc0
  have hper : ∀ r, NuGe D Q F v k s r ↔ NuGe D Q F v k s (r + M * c) := fun r => by
    have := hiter M s r
    rw [hcyc s] at this
    exact this
  exact hs1 (all_of_periodic hmono hd hper 0 1 hs0)

theorem gs_const_inj {F : Type} [Field F] (z : Spec (CommRingCat.of F)) {c : F}
    (h : gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) = 1) : c = 1 := by
  let φ : F →+* (Spec (CommRingCat.of F)).presheaf.stalk z :=
    ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have e : φ c = 1 := by
    rw [gs_eq _ z ⊤ trivial] at h
    exact h
  exact φ.injective (e.trans (map_one φ).symm)

section Integral

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) {X : Scheme.{0}} {L : LB X}

theorem exists_ratio_int (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((TO hϖ hv).left ⟶ X)}
    {ε : K → ℤ} {φ' : K' → ((TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb L φ' ε')) (ht' : t'.IsGen) (hf : FormEq φ ε φ' ε') :
    ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ ∀ (z : (TF (R := V) F).left) (J), Good L z J →
      (val t (ιS hϖ hv).left z J).val =
        gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val t' (ιS hϖ hv).left z J).val := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TO hϖ hv).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const L hL (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ t')) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ ht'))
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hf U h, mul_inv_cancel])
  refine ⟨ιr (v := v) a, v_ιr a, fun z J hJ => ?_⟩
  have e := ha _ (ιS hϖ hv).left z J hJ
  have e2 : gs ((ιS hϖ hv).left ≫ 𝟙 _) z ⊤ a =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (ιr (v := v) a)) := by
    have e3 : gs (𝟙 _ ≫ (ιS hϖ hv).left) z ⊤ a = gs (𝟙 _) z ⊤ ((ιS hϖ hv).left.appTop.hom a) :=
      (gs_pull _ _ z ⊤ trivial a).symm
    rw [Category.id_comp] at e3
    rw [Category.comp_id, e3,
      show (ιS hϖ hv).left = Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) from rfl, appTop_specMap]
    rfl
  rw [val_mul hJ, val_inv, e2] at e
  rw [← e, Units.val_mul, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]

theorem exists_ratio_unit (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((TO hϖ hv).left ⟶ X)}
    {ε : K → ℤ} {φ' : K' → ((TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb L φ' ε')) (ht' : t'.IsGen) (hf : FormEq φ ε φ' ε') :
    ∃ c : F, v c = 0 ∧ ∀ (z : (TF (R := V) F).left) (J), Good L z J →
      (val t (ιS hϖ hv).left z J).val =
        gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val t' (ιS hϖ hv).left z J).val := by
  obtain ⟨c, hc0, hc⟩ := exists_ratio_int hϖ hv hL t ht t' ht' hf
  obtain ⟨d, hd0, hd⟩ := exists_ratio_int hϖ hv hL t' ht' t ht (fun U _ h => (hf U h).symm)
  refine ⟨c, ?_, hc⟩
  obtain ⟨z⟩ : Nonempty (TF (R := V) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  choose I hI using fun χ : (TF (R := V) F).left ⟶ X => Geo.Tor.exists_chart hL (χ z)
  have e := hc z I hI
  rw [hd z I hI, ← _root_.mul_assoc, ← gs_mul _ z ⊤ trivial, ← map_mul] at e
  have e1 : c * d = 1 := gs_const_inj z ((Units.mul_left_inj _).1 (e.symm.trans (_root_.one_mul _).symm))
  have e2 : v c + v d = 0 := by rw [← AddValuation.map_mul, e1, AddValuation.map_one]
  exact le_antisymm (le_zero_of_add_eq_zero_nonneg e2 hd0) hc0

end Integral

theorem valueAtZero_of_sectionValue {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (α : D.toPre.X)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) (x : F)
    (h : ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J →
      sval s (DegPre.zF D.toPre F).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) *
        (val (Z := (TF (R := V) F).left) D.toPre.rigK (jFK (R := V) F) z J ^ k).val) :
    Val0 D F k α s x := by
  have hL := D.toPre.P.isLB
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have a₂ : jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left :=
    (Category.assoc _ _ _).symm
  obtain ⟨τ, hτ, vτ⟩ := exists_gen hL
    (φ' := fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) (ε' := DegPre.famε k)
    (fun U _ g => by
      rw [prod_fam D.toPre F (DegPre.zF D.toPre F) α k g, z₂, _root_.mul_one (cP _ _ _), mul_inv_cancel_right,
        Fintype.prod_unique, a₂, zpow_sub_one, inv_mul_cancel_right]
      exact congrArg _ (_root_.mul_one _))
    (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k) (jFK (R := V) F))
    (DVR.pullGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.toPre.rig_gen _) k) _)
  refine ⟨τ, hτ, corr_of_val hL fun y J hJ => vτ _ _ y J hJ, fun j => fn_ext fun y hy => ?_⟩
  choose I hI using fun χ : (TF (R := V) F).left ⟶ D.toPre.P.A.left => Geo.Tor.exists_chart hL (χ y)
  have hI' : Good D.toPre.P.L y I := hI
  have hy' : (DegPre.zF D.toPre F).left y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j :=
    Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy i
  have T0 := sec_trans s (DegPre.zF D.toPre F).left y hy' (hI'.mem _ _)
  have T1 := gen_trans hτ (𝟙 _) y (j := j) hy (hI'.mem _ (𝟙 _))
  have T2 : val τ (𝟙 _) y I = val (Z := (TF (R := V) F).left) D.toPre.rigK (jFK (R := V) F) y I ^ k := by
    rw [vτ _ _ y I hI', val_pull hI', Category.id_comp]
    exact map_pow _ _ _
  have T3 : Geo.Tor.trF (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) (DegPre.famε k) (𝟙 _) y j
      (fun i => I (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i)) =
      Geo.Tor.trF (DegPre.famφ D.toPre F α) (DegPre.famε k) (DegPre.zF D.toPre F).left y j
        (fun i => I ((DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    show gm (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) y
      (D.toPre.P.L.U (j i) ⊓ D.toPre.P.L.U (I (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i)))
      (D.toPre.P.L.g (j i) (I (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))) ^ _ = _
    rw [Category.id_comp]
  refine ((gs_res _ y _ hy _).trans ((gs_pull (𝟙 _) (DegPre.zF D.toPre F).left y _ hy' _).trans ?_)).trans
    ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res _ y le_top hy _)
      ((gs_unit _ y _ hy _).trans (congrArg Units.val T1)))).symm
  rw [Category.id_comp, T3]
  refine T0.trans ?_
  have T4 := h y I hI'
  rw [← T2] at T4
  refine (congrArg (_ * ·) T4).trans ?_
  rw [Units.val_mul]
  exact mul_left_comm _ _ _

theorem main : Laws → TwistBCSpanStatement → TWM.VRatioGtStatement → UUStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))), w.IsGen → ∀ ζ : F, ζ ≠ 0 → FinOrd D F k p w ζ → ∀ s t h : Fam D.toPre F k, PhiRel D.toPre F k p w s t → Fam.IsSmul D.toPre F ζ t h → ∀ (α : D.toPre.X) (m : TWM.TO hϖ hv ⟶ D.toPre.P.A), TWM.ιS hϖ hv ≫ m = p.g.b → ∀ r : ℚ, (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m).left ≫ DegPre.famφB D.toPre (α) i) (DegPre.famε (k))), G₀.IsGen ∧ ∃ x : F, v x = ((r : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s.s α) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) → ∃ x : F, Val0 D F k (α + p.y) (h.s (α + p.y)) x ∧ v x = ((r + ((Q (α + p.y) : ℚ) - Q α) / k : ℚ) : WithTop ℚ) := by
  intro hLaws hTW hVR hUU V _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk p w hw ζ hζ hfin s t' s' hst hts α m hm r
    ⟨G₁, hG₁, x, hx, hsx⟩
  have hG := hLaws.globalFns
  have hL := D.toPre.P.isLB
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  obtain ⟨W₀, hW₀⟩ := exists_gen_of_local D.toPre.P.L hL (lineφO hϖ hv m) (DegPre.lineε k)
  obtain ⟨G₀, hG₀⟩ := exists_gen_of_local D.toPre.P.L hL (gtφO hϖ hv m α) DegPre.gtε
  have hl : ∀ i, DegPre.lineφ D.toPre F p.g.b i = (ιS hϖ hv).left ≫ lineφO hϖ hv m i := by
    intro i; fin_cases i
    · show (DegPre.zeroF D.toPre F).left = (ιS hϖ hv).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left
      rw [← Over.comp_left, MonObj.comp_one]; rfl
    · show p.g.b.left = (ιS hϖ hv).left ≫ m.left
      rw [← Over.comp_left, hm]
  have hg : ∀ i, DegPre.gtφ D.toPre F p.g.b α i = (ιS hϖ hv).left ≫ gtφO hϖ hv m α i := by
    intro i; fin_cases i
    · show (padd D.toPre.P.A (DegPre.cF D.toPre F α) p.g.b).left = (ιS hϖ hv).left ≫ (cP D.toPre _ α * m).left
      rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hm]; rfl
    · show (DegPre.cF D.toPre F α).left = (ιS hϖ hv).left ≫ (cP D.toPre _ α).left
      rw [← Over.comp_left, comp_cP]; rfl
    · show p.g.b.left = (ιS hϖ hv).left ≫ m.left
      rw [← Over.comp_left, hm]
    · show (DegPre.zeroF D.toPre F).left = (ιS hϖ hv).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left
      rw [← Over.comp_left, MonObj.comp_one]; rfl
  obtain ⟨lam, hlam0, hlam⟩ := exists_ratio hL w hw (LB.pullGen D.toPre.P.L _ _ W₀ (ιS hϖ hv).left)
    (DVR.pullGen_isGen _ _ _ _ hW₀ _) (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hl])
  obtain ⟨t, ht0, ht⟩ := exists_ratio hL (p.g.s α) (p.g.isGen α)
    (LB.pullGen D.toPre.P.L _ _ G₀ (ιS hϖ hv).left) (DVR.pullGen_isGen _ _ _ _ hG₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hg])
  have ht' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (val G₀ (r ≫ (ιS hϖ hv).left) z J).val := fun Z r z J hJ => by
    rw [ht Z r z J hJ, val_pull hJ]
  have hlam' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val w r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom lam) *
        (val W₀ (r ≫ (ιS hϖ hv).left) z J).val := fun Z r z J hJ => by
    rw [hlam Z r z J hJ, val_pull hJ]
  obtain ⟨q, hq, hkq⟩ := hVR V ϖ hϖ D Q hQ F v hv k hk p m hm α G₀ hG₀ t ht'
  obtain ⟨qz, hqz⟩ := wt_coe_of_ne (v := v) hζ
  obtain ⟨ql, hql⟩ := wt_coe_of_ne (v := v) hlam0
  have hc0 : qz + ql - (Q p.y : ℚ) / k = 0 :=
    shift_zero hLaws hUU V ϖ hϖ D Q hQ F v hv k hk p w hw ζ hfin _
      (shift_explicit hG hTW hVR V ϖ hϖ D Q hQ F v hv k hk p w hw ζ hζ m hm W₀ hW₀ lam hlam0 hlam' qz ql hqz hql)
  obtain ⟨c, hc, hcv⟩ := exists_ratio_unit hϖ hv hL
    (LB.mulGen D.toPre.P.L _ _ _ _ G₁ (LB.mulGen D.toPre.P.L _ _ _ _ G₀ W₀))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hG₁ (DVR.mulGen_isGen _ _ _ _ _ _ _ hG₀ hW₀))
    (GeneratorPullback.powGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig
      (toUnit (TO hϖ hv)).left) k)
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.toPre.rig_gen _) k)
    (fun U _ h => by
      have p₁ := prod_famB D.toPre m α k h
      have p₂ : cQ D.toPre (TO hϖ hv) α = cP D.toPre (TO hϖ hv) α := rfl
      rw [p₂, mul_comm m] at p₁
      have p₃ : ∏ i, h (gtφO hϖ hv m α i) ^ DegPre.gtε i =
          h (cP D.toPre _ α * m).left ^ (-1 : ℤ) * h (cP D.toPre _ α).left ^ (1 : ℤ) * h m.left ^ (1 : ℤ) *
            h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ (-1 : ℤ) := Fin.prod_univ_four _
      have p₄ : ∏ i, h (lineφO hϖ hv m i) ^ DegPre.lineε k i =
          h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ (k : ℤ) * h m.left ^ (-(k : ℤ)) := Fin.prod_univ_two _
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 2) (U := U) _ p₁
        (prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := U) _ p₃ p₄)) ?_
      rw [Fintype.prod_unique]
      show _ = h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ ((k : ℤ) * 1)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
  refine ⟨ζ * x * t * lam * c, valueAtZero_of_sectionValue D F k _ _ _ fun z J hJ => ?_, ?_⟩
  · have C : IsCub (th D.toPre (T := TF (R := V) F) z J) := isCub_cubV D.toPre.cub hJ
    have z₁ : DegPre.zF D.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
    have z₃ : DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F p.g.b = lift (𝟙 (TF (R := V) F)) (ιS hϖ hv ≫ m) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, tr_fst, z₁, lift_fst]
      · rw [lift_snd, Category.assoc, hm]
        refine (congrArg (DegPre.zF D.toPre F ≫ ·) (tr_pr D.toPre F p.g.b)).trans ?_
        rw [MonObj.comp_mul, z₂, _root_.one_mul, ← Category.assoc, z₁, Category.id_comp]
    have e₁ := (phiRel_iff hG p w hw s t').1 hst α _ rfl _ (DegPre.zF D.toPre F) z J hJ
    rw [uVal, z₂, z₁, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul, z₃, hsx z J hJ, val_mul hJ,
      Units.val_mul, ht' _ _ z J hJ, hlam' _ _ z J hJ, Over.id_left, Category.id_comp] at e₁
    have e₂ := sval_smul ζ t' (α + p.y) (DegPre.zF D.toPre F).left z hJ
    rw [← (ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff ζ t' s').1 hts, ← Over.comp_left, z₁, Over.id_left, e₁] at e₂
    have e₃ := hcv z J hJ
    have e₄ : val (GeneratorPullback.powGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A)
        (fun _ => 1) D.toPre.rig (toUnit (TO hϖ hv)).left) k) (ιS hϖ hv).left z J =
        val (Z := (TF (R := V) F).left) D.toPre.rigK (jFK (R := V) F) z J ^ k := by
      refine (map_pow _ _ _).trans (congrArg (· ^ k) ?_)
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      have e : (ιS hϖ hv).left ≫ (toUnit (TO hϖ hv)).left = jFK (R := V) F ≫ (toUnit (TK V)).left := by
        rw [← Over.comp_left, toUnit_unique (ιS hϖ hv ≫ toUnit _) (toUnit _)]
        simp
      rw [e]
    rw [e₄, val_mul hJ, val_mul hJ, Units.val_mul, Units.val_mul] at e₃
    rw [e₂]
    simp only [map_mul, gs_mul _ z ⊤ trivial]
    rw [_root_.mul_assoc _ (gs _ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c)), ← e₃]
    ring
  · rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hc, hx, hq, hqz, hql,
      add_zero, ← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add]
    congr 1
    have hq' : q = ((Q (p.y + α) : ℚ) - Q p.y - Q α) / k := by
      rw [eq_div_iff hk0]
      simp only [bOf] at hkq
      push_cast at hkq
      linarith
    have : qz = (Q p.y : ℚ) / k - ql := by linarith
    rw [this, hq', add_comm α p.y]
    ring

end GlobalTheory.PhiValue
