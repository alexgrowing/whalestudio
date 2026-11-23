import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfValEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjDualPartsKilledOfPerfectPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointLocallyConstantGeomPoinStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ESDual

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}

def kerPts {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] (T : Over S) : Subgroup (T ⟶ A) where
  carrier := {g | g ≫ ψ = 1}
  one_mem' := MonObj.one_comp ψ
  mul_mem' {x y} hx hy := by
    change (x * y) ≫ ψ = 1
    rw [MonObj.mul_comp, hx, hy, _root_.mul_one]
  inv_mem' {x} hx := by
    change x⁻¹ ≫ ψ = 1
    have h : (x⁻¹ * x) ≫ ψ = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
    rwa [MonObj.mul_comp, hx, _root_.mul_one] at h

def kerAct {s : S ⟶ Sp R} {o o' : Obj b N s} (ψ : o.A ⟶ o'.A) [IsMonHom ψ]
    (h : ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) (T : Over S) (a : D.O) : kerPts ψ T →* kerPts ψ T :=
  MonoidHom.mk' (fun g => ⟨g.1 ≫ o.act.act a, by
      haveI := o'.act.hom a
      change (g.1 ≫ o.act.act a) ≫ ψ = 1
      rw [Category.assoc, h, ← Category.assoc, show g.1 ≫ ψ = 1 from g.2, MonObj.one_comp]⟩)
    fun x y => Subtype.ext (by
      haveI := o.act.hom a
      exact MonObj.mul_comp _ _ _)

open GlobalTheory.CechPic in

theorem val_act {s : S ⟶ Sp R} (o : Obj b N s) (a : D.O) {T : Over S} (x y : T ⟶ o.A) :
    BirigidPow.val o.isLB (x ≫ o.act.act a) y = BirigidPow.val o.isLB x (y ≫ o.act.act (D.star a).unop) := by
  have e := (cls_eq_iff (pull_isLB o.isLB _) (pull_isLB o.isLB _)).2 (o.rosati a)
  rw [cls_pull o.isLB _ (pull_isLB o.isLB _), cls_pull o.isLB _ (pull_isLB o.isLB _)] at e
  have e' := congrArg (pull (lift x y).left) e
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_snd,
    lift_fst, lift_snd_assoc] at e'
  exact e'

open GlobalTheory.TranslChar GlobalTheory.CechPic in

theorem exists_pairing {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} [IsMonHom ψ]
    (hψ : IsPIsog c o o' ψ) {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₁ : ψ ≫ ψ' = (𝟙 o.A) ^ c)
    (h₂ : ψ' ≫ ψ = (𝟙 o'.A) ^ c) (hl : ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a)
    (hl' : ∀ a : D.O, o'.act.act a ≫ ψ' = ψ' ≫ o.act.act a)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) :
    ∃ e : kerPts ψ' (Over.mk x) →* kerPts ψ (Over.mk x) →* Γ((Over.mk x).left, ⊤)ˣ, Function.Injective e ∧
      ∀ a g y, e (kerAct ψ' hl' _ a g) y = e g (kerAct ψ hl _ (D.star a).unop y) := by
  set T : Over S := Over.mk x with hTdef
  have hL := o'.isLB
  let φ₀ : (T ⟶ o'.A) → ((o'.A ⊗ T).left ⟶ (G2 o'.A).left) := fun g => (lift (snd o'.A T ≫ g) (fst o'.A T)).left
  let φ : (T ⟶ o'.A) → ((o.A ⊗ T).left ⟶ (G2 o'.A).left) := fun g => (lift (snd o.A T ≫ g) (fst o.A T ≫ ψ)).left
  have hφ : ∀ g, (ψ ▷ T).left ≫ φ₀ g = φ g := fun g => by
    simp only [φ₀, φ]
    rw [← Over.comp_left, comp_lift, whiskerRight_snd_assoc, whiskerRight_fst]
  have hex : ∀ g : kerPts ψ' T, ∃ σ : (o'.P.pull (φ g.1)).Gen, σ.IsGen := fun g => by
    refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
    rw [cls_pull hL _ (pull_isLB hL _)]
    change BirigidPow.val hL _ _ = 0
    rw [val_adj hψ h₂, Category.assoc, show g.1 ≫ ψ' = 1 from g.2, MonObj.comp_one,
      BirigidPow.val_one_left _ o.rig₁]
  choose σ hσ using hex
  have htr : ∀ y : kerPts ψ T, tr y.1 ≫ ψ ▷ T = ψ ▷ T := fun y => by
    rw [tr_whisker, show y.1 ≫ ψ = 1 from y.2, tr_one, Category.comp_id]
  have hch : ∀ (g : kerPts ψ' T) (y : kerPts ψ T), ∃ u, Ch (σ g) y.1 u := fun g y =>
    exists_ch o.ab hL (σ g) (hσ g) y.1 fun _ => by
      change _ ≫ φ g.1 = φ g.1
      rw [← hφ, ← Category.assoc, ← Over.comp_left, htr]
  choose u hu using hch
  have hinv : ∀ {K : Type} [Fintype K] {θ : K → ((o'.A ⊗ T).left ⟶ (G2 o'.A).left)} {ε : K → ℤ}
      (t : LB.Gen (LB.LinComb o'.P θ ε)) (y : kerPts ψ T), Ch (LB.pullGen _ _ _ t (ψ ▷ T).left) y.1 1 := by
    intro K _ θ ε t y
    refine Ch.pull ψ ?_
    rw [show y.1 ≫ ψ = 1 from y.2]
    exact Ch.one t
  have m₂ : ∀ g y y', u g (y * y') = u g y * u g y' := fun g y y' =>
    (hu g (y * y')).unique hL ((hu g y).comp (hu g y'))
  have m₁ : ∀ g g' y, u (g * g') y = u g y * u g' y := by
    intro g g' y
    obtain ⟨t, ht⟩ := (Biadditive.biadditive_of_triv_axes GlobalTheory.laws_without_cohomology.1 S o'.A _ o'.ab
      (pull_isLB hL _) o'.ample o'.P hL o'.rig₁ o'.rig₂ (o'.A ⊗ T) (snd o'.A T ≫ g.1) (snd o'.A T ≫ g'.1)
      (fst o'.A T)).1
    have h := (hinv t y).mul ((hu g y).mul (hu g' y))
    rw [_root_.one_mul] at h
    refine (hu (g * g') y).unique hL (h.of_formEq o.ab hL (fun U _ f => ?_) (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.mulGen_isGen _ _ _ _ _ _ _ (hσ g) (hσ g'))) (hσ _))
    have e₁ := hφ (g.1 * g'.1)
    have e₂ := hφ g.1
    have e₃ := hφ g'.1
    simp only [φ₀, MonObj.comp_mul] at e₁ e₂ e₃
    simp only [Fintype.prod_sum_type, Fin.prod_univ_three, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, e₁, e₂, e₃, zpow_one, zpow_neg, Subgroup.coe_mul]
    rw [_root_.mul_assoc, _root_.mul_assoc, mul_left_comm (f (φ g'.1))⁻¹, inv_mul_cancel, _root_.mul_one,
      inv_mul_cancel, _root_.mul_one]
  refine ⟨MonoidHom.mk' (fun g => MonoidHom.mk' (u g) (m₂ g)) fun g g' => MonoidHom.ext (m₁ g g'), ?_,
    fun a g y => ?_⟩
  · refine (injective_iff_map_eq_one _).2 fun g hg => ?_
    have hg1 : ∀ y, u g y = 1 := fun y => DFunLike.congr_fun hg y
    have hc := hψ.pos
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.KthRoot.finite_flat_surjective_mulN_any S o'.A o'.ab c hc
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow] at h1 h2 h3
    have hp : IsPullback (pullback.fst o'.A.hom T.hom) (((𝟙 o'.A) ^ c) ▷ T).left ((𝟙 o'.A) ^ c).left
        (pullback.fst o'.A.hom T.hom) := by
      refine (IsPullback.of_right (h₁₁ := (((𝟙 o'.A) ^ c) ▷ T).left) (v₁₁ := pullback.fst o'.A.hom T.hom)
        (h₂₁ := ((𝟙 o'.A) ^ c).left) (v₁₂ := pullback.fst o'.A.hom T.hom) ?_ (Over.whiskerRight_left_fst _)
        (IsPullback.of_hasPullback o'.A.hom T.hom).flip).flip
      rw [Over.whiskerRight_left_snd, Over.w]
      exact (IsPullback.of_hasPullback o'.A.hom T.hom).flip
    have h4 : IsAffineHom ((𝟙 o'.A) ^ c).left := inferInstance
    have hw : ((𝟙 o'.A) ^ c) ▷ T = ψ' ▷ T ≫ ψ ▷ T := by rw [← h₂, comp_whiskerRight]
    have hw' : (((𝟙 o'.A) ^ c) ▷ T).left ≫ φ₀ g.1 = (ψ' ▷ T).left ≫ φ g.1 := by
      rw [hw, Over.comp_left, Category.assoc, hφ]
    obtain ⟨τ, hτ, hv⟩ := exists_gen hL (φ' := fun _ : PUnit => (((𝟙 o'.A) ^ c) ▷ T).left ≫ φ₀ g.1)
      (ε' := fun _ => 1) (fun U _ f => by rw [hw']) (LB.pullGen _ _ _ (σ g) (ψ' ▷ T).left)
      (DVR.pullGen_isGen _ _ _ _ (hσ g) _)
    have hτ1 : ∀ y : T ⟶ o'.A, y ^ c = 1 → Ch τ y 1 := by
      intro y hy
      have hy' : (y ≫ ψ') ≫ ψ = 1 := by rw [Category.assoc, h₂, MonObj.comp_pow, Category.comp_id, hy]
      have h := hu g ⟨y ≫ ψ', hy'⟩
      rw [hg1] at h
      exact (Ch.pull ψ' h).of_formEq o'.ab hL (fun U _ f => by rw [hw']) (DVR.pullGen_isGen _ _ _ _ (hσ g) _) hτ
    have htriv := exists_gen_of_val_eq hL _ (MorphismProperty.of_isPullback (P := @Flat) hp h2)
      (MorphismProperty.of_isPullback (P := @Surjective) hp h3)
      (MorphismProperty.of_isPullback (P := @IsAffineHom) hp h4) (φ₀ g.1) τ hτ (by
        intro Z g₁ g₂ hgg z J hJ
        obtain ⟨a, ha⟩ := exists_ratio hL τ hτ g₂ g₁ (fun _ => by rw [reassoc_of% hgg])
        have ha1 : a = 1 := by
          refine unit_ext fun w _ => ?_
          have hw₀ : (((𝟙 o'.A) ^ c) ▷ T).left ≫ (o'.A ⊗ T).hom = (o'.A ⊗ T).hom := Over.w _
          let FinalForm : Over S := Over.mk (g₁ ≫ (o'.A ⊗ T).hom)
          let G₁ : FinalForm ⟶ o'.A ⊗ T := Over.homMk g₁ rfl
          let G₂ : FinalForm ⟶ o'.A ⊗ T := Over.homMk g₂ (by
            change g₂ ≫ (o'.A ⊗ T).hom = g₁ ≫ (o'.A ⊗ T).hom
            rw [← hw₀, ← Category.assoc, ← hgg, Category.assoc])
          have hG : G₁ ≫ ((𝟙 o'.A) ^ c) ▷ T = G₂ ≫ ((𝟙 o'.A) ^ c) ▷ T := Over.OverMorphism.ext hgg
          have ht : G₁ ≫ snd o'.A T = G₂ ≫ snd o'.A T := by
            have := congrArg (· ≫ snd o'.A T) hG
            simpa using this
          have hb : (G₁ ≫ fst o'.A T) ^ c = (G₂ ≫ fst o'.A T) ^ c := by
            have := congrArg (· ≫ fst o'.A T) hG
            simp only [Category.assoc, whiskerRight_fst] at this
            rw [← Category.assoc, ← Category.assoc, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
              Category.comp_id] at this
            exact this
          have hz : ((G₁ ≫ fst o'.A T)⁻¹ * (G₂ ≫ fst o'.A T)) ^ c = 1 := by
            rw [mul_pow, inv_pow, hb, inv_mul_cancel]
          obtain ⟨V, i, y, w', hi, rfl, hy, hiz⟩ := GlobalTheory.T.abelianScheme_torsionPoint_locally_constant_geomPoint S o'.A o'.ab k x c (Nat.cast_ne_zero.2 hc.ne') FinalForm
            (G₁ ≫ snd o'.A T) _ hz w
          have hV : i ≫ G₂ = (i ≫ G₁) ≫ tr y := by
            apply CartesianMonoidalCategory.hom_ext
            · rw [Category.assoc _ (tr y), tr_fst, MonObj.comp_mul, Category.assoc i G₁ (snd _ _ ≫ y),
                ← Category.assoc G₁, ← hiz, Category.assoc i G₁, ← MonObj.comp_mul, mul_inv_cancel_left,
                Category.assoc]
            · rw [Category.assoc _ (tr y), tr_snd, Category.assoc, Category.assoc, ht]
          have hV' : i.left ≫ g₂ = (i.left ≫ g₁) ≫ (tr y).left := congrArg (fun q => q.left) hV
          choose J' hJ' using fun χ : V.left ⟶ (G2 o'.A).left => exists_chart hL (χ w')
          have e := ha _ i.left w' J' hJ'
          rw [hV', hτ1 y hy _ _ _ _ hJ', map_one] at e
          rw [map_one]
          exact gm_id_eq_one i.left w' a (mul_right_cancel e).symm
        have := ha _ (𝟙 Z) z J hJ
        rw [ha1, map_one, _root_.one_mul, Category.id_comp, Category.id_comp] at this
        exact this.symm)
    obtain ⟨n, hn, hker⟩ := o'.kerP
    have e₁ : g.1 ^ n = 1 := hker T g.1 htriv
    have e₂ : g.1 ^ c = 1 := by
      rw [← Category.comp_id g.1, ← MonObj.comp_pow, ← h₂, ← Category.assoc, show g.1 ≫ ψ' = 1 from g.2,
        MonObj.one_comp]
    obtain ⟨m, rfl⟩ := hψ.1
    have := pow_gcd_eq_one.2 ⟨e₁, e₂⟩
    rw [(hn.pow_right m).gcd_eq_one, pow_one] at this
    exact Subtype.ext this
  · haveI := o.act.hom (D.star a).unop
    have hz : (LB.LinComb o'.P (K := Fin 2) ![φ₀ (g.1 ≫ o'.act.act a),
        (lift (snd o'.A T ≫ g.1) (fst o'.A T ≫ o'.act.act (D.star a).unop)).left] ![1, -1]).IsLB :=
      LB.isLB_linComb hL _ _
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff hz).1 (by
      rw [cls_linComb hL _ _ hz, Fin.sum_univ_two]
      have := val_act o' a (snd o'.A T ≫ g.1) (fst o'.A T)
      rw [Category.assoc] at this
      change (1 : ℤ) • BirigidPow.val hL _ _ + (-1 : ℤ) • BirigidPow.val hL _ _ = 0
      rw [this, one_zsmul, neg_one_zsmul, add_neg_cancel])
    have h := (hinv t y).mul (Ch.pull (o.act.act (D.star a).unop) (hu g (kerAct ψ hl _ (D.star a).unop y)))
    rw [_root_.one_mul] at h
    refine (hu _ y).unique hL (h.of_formEq o.ab hL (fun U _ f => ?_) (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ (hσ g) _)) (hσ _))
    have e₁ := hφ (g.1 ≫ o'.act.act a)
    have e₂ : (ψ ▷ T).left ≫ (lift (snd o'.A T ≫ g.1) (fst o'.A T ≫ o'.act.act (D.star a).unop)).left =
        (o.act.act (D.star a).unop ▷ T).left ≫ φ g.1 := by
      simp only [φ]
      rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, whiskerRight_snd_assoc, whiskerRight_snd_assoc,
        whiskerRight_fst_assoc, whiskerRight_fst_assoc, hl]
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, e₁, e₂, zpow_one, zpow_neg]
    rw [inv_mul_cancel_right]
    rfl

theorem bar_bar (D : Datum p) (a : 𝓞 D.F) : D.bar (D.bar a) = a := by
  apply Subtype.ext
  have h1 := D.bar_eq (D.bar a)
  rw [D.bar_eq a, IsCMField.complexConj_apply_apply] at h1
  exact h1

theorem uIdeal_conj (D : Datum p) (r : ℤ) : uIdeal D (D.tr - r) = (uIdeal D r).map (D.bar : 𝓞 D.F →+* 𝓞 D.F) := by
  rw [uIdeal, uIdeal, Ideal.map_span, Set.image_pair]
  have e : D.ω - ((D.tr - r : ℤ) : 𝓞 D.F) = -((D.bar : 𝓞 D.F →+* 𝓞 D.F) (D.ω - r)) := by
    have := D.tr_eq
    rw [map_sub, map_intCast]
    push_cast
    change _ = -(D.bar D.ω - r)
    linear_combination this
  rw [e, map_natCast, Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_neg]

theorem map_bar_map_bar (D : Datum p) (w : Ideal (𝓞 D.F)) :
    (w.map (D.bar : 𝓞 D.F →+* 𝓞 D.F)).map (D.bar : 𝓞 D.F →+* 𝓞 D.F) = w := by
  rw [Ideal.map_map]
  have : (D.bar : 𝓞 D.F →+* 𝓞 D.F).comp D.bar = RingHom.id _ := RingHom.ext (bar_bar D)
  rw [this, Ideal.map_id]

theorem uIdeal_sup_map (D : Datum p) (r : ℤ) :
    uIdeal D r ⊔ (uIdeal D r).map (D.bar : 𝓞 D.F →+* 𝓞 D.F) = ⊤ := by
  rw [← uIdeal_conj, Ideal.eq_top_iff_one]
  set I := uIdeal D r ⊔ uIdeal D (D.tr - r)
  have h₀ : (p : 𝓞 D.F) ∈ I := Ideal.mem_sup_left (p_mem_uIdeal D r)
  have h₁ := I.add_mem (Ideal.mem_sup_left (sub_mem_uIdeal D r)) (Ideal.mem_sup_right (sub_mem_uIdeal D (D.tr - r)))
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 D.disc_p
  have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
  have htr := D.tr_eq
  have hnm := D.nm_eq
  have h₂ := I.add_mem (I.mul_mem_left (x : 𝓞 D.F) h₀) (I.mul_mem_left (y * (2 * D.ω - D.tr)) h₁)
  convert h₂ using 1
  push_cast at h ⊢
  linear_combination -h + 4 * y * hnm - 4 * y * D.ω * htr

theorem uIdeal_mul_map_le (D : Datum p) {r : ℤ} {w : Ideal (𝓞 D.F)} (hw : w ≠ ⊤) (hu : uIdeal D r ≤ w) :
    uIdeal D r * (uIdeal D r).map (D.bar : 𝓞 D.F →+* 𝓞 D.F) ≤ Ideal.span {(p : 𝓞 D.F)} := by
  have htr := D.tr_eq
  have hnm := D.nm_eq
  have e : (D.ω - r) * (D.ω - ((D.tr - r : ℤ) : 𝓞 D.F)) = ((-(r ^ 2 - D.tr * r + D.nm) : ℤ) : 𝓞 D.F) := by
    push_cast
    linear_combination D.ω * htr - hnm
  have hd : (p : ℤ) ∣ -(r ^ 2 - D.tr * r + D.nm) := by
    by_contra hn
    have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
    obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 hn
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, ← e, Int.cast_one, Int.cast_natCast] at h
    refine hw ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← h]
    exact w.add_mem (w.mul_mem_left _ (hu (p_mem_uIdeal D r)))
      (w.mul_mem_left _ (w.mul_mem_right _ (hu (sub_mem_uIdeal D r))))
  rw [← uIdeal_conj, uIdeal, uIdeal, Ideal.span_pair_mul_span_pair, Ideal.span_le]
  have hp : (p : 𝓞 D.F) ∈ Ideal.span {(p : 𝓞 D.F)} := Ideal.mem_span_singleton_self _
  rintro z (rfl | rfl | rfl | rfl)
  · exact Ideal.mul_mem_right _ _ hp
  · exact Ideal.mul_mem_right _ _ hp
  · exact Ideal.mul_mem_left _ _ hp
  · obtain ⟨m, hm⟩ := hd
    rw [e, hm, Int.cast_mul, Int.cast_natCast]
    exact Ideal.mul_mem_right _ _ hp

theorem absNorm_map_bar (D : Datum p) (w : Ideal (𝓞 D.F)) :
    Ideal.absNorm (w.map (D.bar : 𝓞 D.F →+* 𝓞 D.F)) = Ideal.absNorm w := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv w _ D.bar rfl).toEquiv).symm

section
variable {s : S ⟶ Sp R} {o o' : Obj b N s} (ψ : o.A ⟶ o'.A) [IsMonHom ψ]
  (h : ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) (T : Over S)

theorem kerAct_one (y : kerPts ψ T) : kerAct ψ h T (algebraMap (𝓞 D.F) D.O 1) y = y :=
  Subtype.ext (by
    change y.1 ≫ _ = _
    rw [map_one, o.act.one, Category.comp_id])

theorem kerAct_mul (a a' : 𝓞 D.F) (y : kerPts ψ T) : kerAct ψ h T (algebraMap (𝓞 D.F) D.O (a * a')) y =
    kerAct ψ h T (algebraMap (𝓞 D.F) D.O a) (kerAct ψ h T (algebraMap (𝓞 D.F) D.O a') y) :=
  Subtype.ext (by
    change y.1 ≫ _ = (y.1 ≫ _) ≫ _
    rw [map_mul, o.act.mul, Category.assoc])

theorem kerAct_add (a a' : 𝓞 D.F) (y : kerPts ψ T) : kerAct ψ h T (algebraMap (𝓞 D.F) D.O (a + a')) y =
    kerAct ψ h T (algebraMap (𝓞 D.F) D.O a) y * kerAct ψ h T (algebraMap (𝓞 D.F) D.O a') y :=
  Subtype.ext (by
    change y.1 ≫ _ = (y.1 ≫ _) * (y.1 ≫ _)
    rw [map_add, o.act.add, MonObj.comp_mul])

theorem kerAct_natCast (n : ℕ) (y : kerPts ψ T) : kerAct ψ h T (algebraMap (𝓞 D.F) D.O n) y = y ^ n := by
  induction n with
  | zero =>
    have := kerAct_add ψ h T 0 0 y
    rw [add_zero] at this
    rw [Nat.cast_zero, pow_zero]
    exact mul_eq_left.1 this.symm
  | succ n ih => rw [Nat.cast_succ, kerAct_add, ih, kerAct_one, pow_succ]

theorem kerAct_eq_one {c : ℕ} {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₁ : ψ ≫ ψ' = (𝟙 o.A) ^ c) {a : 𝓞 D.F}
    (ha : a ∈ Ideal.span {(c : 𝓞 D.F)}) (y : kerPts ψ T) : kerAct ψ h T (algebraMap (𝓞 D.F) D.O a) y = 1 := by
  obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.1 ha
  have : y ^ c = 1 := Subtype.ext (by
    change y.1 ^ c = 1
    rw [← Category.comp_id y.1, ← MonObj.comp_pow, ← h₁, ← Category.assoc, show y.1 ≫ ψ = 1 from y.2,
      MonObj.one_comp])
  rw [kerAct_mul, kerAct_natCast, this, map_one]

theorem kerAct_iff (v : Ideal (𝓞 D.F)) (y : kerPts ψ T) :
    (∀ a ∈ v, kerAct ψ h T (algebraMap (𝓞 D.F) D.O a) y = 1) ↔ KilledBy o v y.1 :=
  forall₂_congr fun _ _ => Subtype.ext_iff

theorem card_kerAct (v : Ideal (𝓞 D.F)) :
    Nat.card {y : kerPts ψ T // ∀ a ∈ v, kerAct ψ h T (algebraMap (𝓞 D.F) D.O a) y = 1} =
      Nat.card {g : T ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o v g} :=
  Nat.card_congr ((Equiv.subtypeEquivRight (kerAct_iff ψ h T v)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun g : T ⟶ o.A => g ≫ ψ = 1) (fun g => KilledBy o v g)))

end

theorem isTj_dual {r : ℤ} {w : Ideal (𝓞 D.F)} (hw : w.IsMaximal) (hu : uIdeal D r ≤ w)
    {j c : ℕ} {s : S ⟶ Sp R} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (hψ : IsPIsog c o o' ψ) (hT : IsTj r w j o o' ψ)
    {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₁ : ψ ≫ ψ' = (𝟙 o.A) ^ c) (h₂ : ψ' ≫ ψ = (𝟙 o'.A) ^ c) :
    IsTj (D.tr - r) (w.map (D.bar : 𝓞 D.F →+* 𝓞 D.F)) j o' o ψ' := by
  intro k _ _ _ x
  obtain ⟨e, rfl⟩ := hψ.1
  haveI := hψ.2.1
  have hl := hψ.2.2.1
  obtain ⟨hl', c₂, c₃⟩ := dual_clauses hψ h₁ h₂
  have hψ' : IsPIsog (p ^ e) o' (scale o e rfl) ψ' := ⟨⟨e, rfl⟩, ‹_›, hl', c₂, c₃, ψ, ‹_›, h₂, h₁⟩
  obtain ⟨ε, hε, aε⟩ := exists_pairing hψ h₁ h₂ hl hl' k x
  obtain ⟨ε', hε', aε'⟩ := @exists_pairing p _ D R _ b N S s _ o' (scale o e rfl) ψ' hψ'.2.1 hψ' ψ hψ.2.1 h₂ h₁
    hl' hl k _ _ _ x
  haveI : IsDomain Γ((Over.mk x).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain k
  have hst : ∀ a : 𝓞 D.F, (D.star (algebraMap (𝓞 D.F) D.O a)).unop = algebraMap (𝓞 D.F) D.O (D.bar a) :=
    fun a => by rw [D.star_F, MulOpposite.unop_op]
  have h0 : Ideal.absNorm w ≠ 0 := fun h0 => by
    have hp := hu (p_mem_uIdeal D r)
    rw [Ideal.absNorm_eq_zero_iff.1 h0, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hp
  have hle : (uIdeal D r * (uIdeal D r).map (D.bar : 𝓞 D.F →+* 𝓞 D.F)) ^ e ≤
      Ideal.span {((p ^ e : ℕ) : 𝓞 D.F)} := by
    rw [Nat.cast_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono (uIdeal_mul_map_le D hw.ne_top hu) e
  obtain ⟨H₁, H₂⟩ := GlobalTheory.T.conj_dual_parts_killed_of_perfect_pairing (𝓞 D.F) (D.bar : 𝓞 D.F →+* 𝓞 D.F) Γ((Over.mk x).left, ⊤)
    (kerPts ψ (Over.mk x)) (kerPts ψ' (Over.mk x))
    (fun a => kerAct ψ hl _ (algebraMap (𝓞 D.F) D.O a)) (fun a => kerAct ψ' hl' _ (algebraMap (𝓞 D.F) D.O a))
    (kerAct_one ψ hl _) (kerAct_mul ψ hl _) (kerAct_add ψ hl _)
    (kerAct_one ψ' hl' _) (kerAct_mul ψ' hl' _) (kerAct_add ψ' hl' _) (bar_bar D) ε ε' hε hε'
    (fun a g y => (aε _ g y).trans (by rw [hst]; rfl)) (fun a g y => (aε' _ g y).trans (by rw [hst]; rfl))
    (uIdeal D r) w e hu (uIdeal_sup_map D r)
    (fun a ha => ⟨kerAct_eq_one ψ hl _ h₁ (hle ha), kerAct_eq_one ψ' hl' _ h₂ (hle ha)⟩)
    (fun y ⟨m, hm⟩ => (kerAct_iff ψ hl _ w y).2 ((hT k x).1 y.1 y.2 ⟨m, (kerAct_iff ψ hl _ _ y).1 hm⟩))
    (Nat.finite_of_card_ne_zero (by rw [card_kerAct, (hT k x).2]; exact pow_ne_zero _ h0))
  refine ⟨fun g hg ⟨m, hm⟩ => (kerAct_iff ψ' hl' _ _ ⟨g, hg⟩).1 (H₁ _ ⟨m, (kerAct_iff ψ' hl' _ _ ⟨g, hg⟩).2 ?_⟩), ?_⟩
  · rwa [uIdeal_conj] at hm
  · rw [← card_kerAct ψ' hl', H₂, card_kerAct, (hT k x).2, absNorm_map_bar]

def relevel {S₁ S₂ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {f : S₁ ⟶ S₂}
    (m : ObjMap o₁ o₂ f) (e : ℕ) {s₁' : S₁ ⟶ Sp R} {s₂' : S₂ ⟶ Sp R} (h₁ : s₁ = s₁') (h₂ : s₂ = s₂') :
    ObjMap (scale o₁ e h₁) (scale o₂ e h₂) f :=
  ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, fun _ => m.eta _⟩

def toScale {s s' s'' : S ⟶ Sp R} (o : Obj b N s) {e f : ℕ} (h : s = s') (h' : s' = s'')
    (hef : p ^ (e + f) ≡ 1 [MOD N]) : ObjMap o (scale (scale o e h) f h') (𝟙 S) :=
  ⟨(idMap o).φ, (idMap o).φ₂, (idMap o).cart, (idMap o).sq, (idMap o).act, (idMap o).pol, fun y => by
    have : (scale (scale o e h) f h').eta y = o.eta y := by
      show o.eta (p ^ e • p ^ f • y) = _
      rw [smul_smul, ← pow_add, eta_congr o hef (pow_pos (Fact.out : p.Prime).pos _)]
    rw [this]
    exact (idMap o).eta y⟩

def toBase {s s' : S ⟶ Sp R} (o : Obj b N s) (h : s = s') : ObjMap o (scale o 0 h) (𝟙 S) :=
  ⟨(idMap o).φ, (idMap o).φ₂, (idMap o).cart, (idMap o).sq, (idMap o).act, (idMap o).pol, fun y => by
    have : (scale o 0 h).eta y = o.eta y := by
      show o.eta (p ^ 0 • y) = _
      rw [pow_zero, one_smul]
    rw [this]
    exact (idMap o).eta y⟩

def ofBase {S₁ S₂ : Scheme.{0}} {s₁ s₁' : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {f : S₁ ⟶ S₂} (m : ObjMap o₁ o₂ f) (h : s₁ = s₁') : ObjMap (scale o₁ 0 h) o₂ f :=
  ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, fun y => by
    have : (scale o₁ 0 h).eta y = o₁.eta y := by
      show o₁.eta (p ^ 0 • y) = _
      rw [pow_zero, one_smul]
    rw [this]
    exact m.eta y⟩

def castMap {S₁ S₂ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {f g : S₁ ⟶ S₂} (m : ObjMap o₁ o₂ f) (h : f = g) : ObjMap o₁ o₂ g :=
  ⟨m.φ, m.φ₂, h ▸ m.cart, m.sq, m.act, m.pol, h ▸ m.eta⟩

theorem square_comp {A B A' B' A'' B'' : Scheme.{0}} {a : A ⟶ A'} {a' : A' ⟶ A''} {c : B ⟶ B'} {c' : B' ⟶ B''}
    {ψ : A ⟶ B} {χ : A' ⟶ B'} {θ : A'' ⟶ B''} (h' : a' ≫ θ = χ ≫ c') (h : a ≫ χ = ψ ≫ c) :
    ((𝟙 _ ≫ a) ≫ a') ≫ θ = ψ ≫ ((𝟙 _ ≫ c) ≫ 𝟙 _) ≫ c' := by
  simp [h', reassoc_of% h]

theorem square_comp' {A B A' B' A'' B'' : Scheme.{0}} {a : A ⟶ A'} {a' : A' ⟶ A''} {c : B ⟶ B'} {c' : B' ⟶ B''}
    {ψ : A ⟶ B} {χ : A' ⟶ B'} {θ : A'' ⟶ B''} (h' : a' ≫ θ = χ ≫ c') (h : a ≫ χ = ψ ≫ c) :
    (((𝟙 _ ≫ a) ≫ 𝟙 _) ≫ a') ≫ θ = ψ ≫ (𝟙 _ ≫ c) ≫ c' := by
  simp [h', reassoc_of% h]

theorem finite_etale_target : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (M : Model b N) (Y : Scheme.{0}) (s t : Y ⟶ M.X), s ≫ M.s = t ≫ M.s → ∀ (o o' : Obj b N (s ≫ M.s)) (ms : ObjMap o M.univ s) (mt : ObjMap o' M.univ t) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → IsTj r w j o o' ψ → IsFinite s → Etale s → (∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y, y ≫ s = x ∧ ∃ (m₀ : ObjMap o₁ o y) (m₁ : ObjMap o₁' o' y), m₀.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ) → IsFinite t ∧ Etale t := by
  intro p _ D R _ _ b N hN hNp hp r w j c hw hu hj hc hm M Y s t hst o o' ms mt ψ hψ hT _ _ univ
  obtain ⟨e, rfl, he⟩ := hc
  obtain ⟨f, hef⟩ := exists_inv_exp (p := p) (by omega : 0 < N) hNp e
  have hc0 : 0 < p ^ e := hψ.pos
  have hw' : (w.map (D.bar : 𝓞 D.F →+* 𝓞 D.F)).IsMaximal := by
    haveI := hw
    exact Ideal.map_isMaximal_of_equiv D.bar
  have hu' : uIdeal D (D.tr - r) ≤ w.map (D.bar : 𝓞 D.F →+* 𝓞 D.F) := by
    rw [uIdeal_conj]; exact Ideal.map_mono hu
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y', o₀, m₀, o₂, χ, hfin, het, hχ, hχT, univ'⟩ := GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable p D R b N hN hNp hp (D.tr - r) _ j (p ^ e)
    hw' hu' hj ⟨e, rfl, he⟩ hm M.X M.s M.univ
  obtain ⟨ψ', hψ', a₁, a₂⟩ := hψ.2.2.2.2.2
  obtain ⟨χ', hχ', b₁, b₂⟩ := hχ.2.2.2.2.2
  obtain ⟨c₁, c₂, c₃⟩ := dual_clauses hψ a₁ a₂
  obtain ⟨d₁, d₂, d₃⟩ := dual_clauses hχ b₁ b₂
  have tψ := isTj_dual hw hu hψ hT a₁ a₂
  have tχ := isTj_dual hw' hu' hχ hχT b₁ b₂
  rw [map_bar_map_bar, sub_sub_cancel] at tχ

  obtain ⟨y, ⟨hy, n₀, n₁, sqy⟩, -⟩ := univ' Y t (scale o' 0 hst) (scale o e hst) (ofBase mt hst) ψ'
    ⟨⟨e, rfl⟩, hψ', c₁, fun x => by
      show o.eta (p ^ e • x) = o'.eta (p ^ 0 • x) ≫ ψ'
      rw [pow_zero, one_smul, c₂], c₃, ψ, hψ.2.1, a₂, a₁⟩ tψ

  obtain ⟨x, ⟨hx, ⟨mx⟩⟩, -⟩ := M.rep _ _ (scale o₂ f rfl)
  obtain ⟨z, ⟨hz, l₀, l₁, sqz⟩, -⟩ := univ Y'.left x (scale o₂ f hx.symm) (scale o₀ 0 hx.symm)
    ⟨mx.φ, mx.φ₂, mx.cart, mx.sq, mx.act, mx.pol, mx.eta⟩ χ'
    ⟨⟨e, rfl⟩, hχ', d₁, fun x => by
      show o₀.eta (p ^ 0 • x) = o₂.eta (p ^ f • x) ≫ χ'
      rw [pow_zero, one_smul, ← d₂, smul_smul, ← pow_add, eta_congr o₀ hef (pow_pos (Fact.out : p.Prime).pos _)],
      d₃, χ, hχ.2.1, b₂, b₁⟩ tχ
  have sqy' : n₁.φ ≫ χ'.left = ψ.left ≫ n₀.φ := square_dual n₀.cart o.ab n₁.φ hc0 b₁ a₂ a₁ sqy
  have sqz' : l₁.φ ≫ ψ'.left = χ.left ≫ l₀.φ := square_dual l₀.cart o₀.ab l₁.φ hc0 a₁ b₂ b₁ sqz
  have hyz : y ≫ z = 𝟙 Y := by
    let u₀ : ObjMap o (scale o₂ f hx.symm) y :=
      castMap (compMap (toScale o hst rfl hef) (relevel n₁ f rfl hx.symm)) (Category.id_comp _)
    let u₁ : ObjMap o' (scale o₀ 0 hx.symm) y :=
      castMap (compMap (castMap (compMap (toBase o' hst) n₀) (Category.id_comp _)) (toBase o₀ hx.symm))
        (Category.comp_id _)
    refine (univ Y s o o' ms ψ hψ hT).unique ⟨?_, compMap u₀ l₀, compMap u₁ l₁, ?_⟩
      ⟨Category.id_comp _, idMap o, idMap o', ?_⟩
    · refine (M.rep _ _ o).unique ⟨?_, ⟨?_⟩⟩ ⟨rfl, ⟨ms⟩⟩
      · rw [Category.assoc, Category.assoc, ← Category.assoc z, hz, hx, ← Category.assoc, hy, hst]
      · exact compMap (compMap u₀ l₀) ms
    · exact square_comp sqz sqy'
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hzy : z ≫ y = 𝟙 Y'.left := by
    let u₀ : ObjMap o₀ (scale o' 0 hst) z :=
      castMap (compMap (castMap (compMap (toBase o₀ hx.symm) l₁) (Category.id_comp _)) (toBase o' hst))
        (Category.comp_id _)
    let u₁ : ObjMap o₂ (scale o e hst) z :=
      castMap (compMap (toScale o₂ hx.symm rfl (by rwa [add_comm])) (relevel l₀ e rfl hst)) (Category.id_comp _)
    refine (univ' Y'.left Y'.hom o₀ o₂ m₀ χ hχ hχT).unique ⟨?_, compMap u₀ n₀, compMap u₁ n₁, ?_⟩
      ⟨Category.id_comp _, idMap o₀, idMap o₂, ?_⟩
    · refine (M.rep _ _ o₀).unique ⟨?_, ⟨?_⟩⟩ ⟨rfl, ⟨m₀⟩⟩
      · rw [Category.assoc z, hy, Category.assoc, ← hst, ← Category.assoc, hz, hx]
      · exact compMap (compMap u₀ n₀) m₀
    · exact square_comp' sqy sqz'
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  haveI : IsIso y := ⟨z, hyz, hzy⟩
  rw [← hy]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.UPel.HT.ESDual
