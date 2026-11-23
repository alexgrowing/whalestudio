import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RValue
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullExp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

lemma const_pull {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (pY : Y ⟶ Spec (CommRingCat.of V)) (pZ : Z ⟶ Spec (CommRingCat.of V))
    (hφ : φ ≫ pZ = pY) (r : V) {U : Z.Opens} {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) :
    rs h ((φ.app U).hom (resTop U (scal pZ r))) = resTop W (scal pY r) := by
  subst hφ
  simp only [rs, resTop, scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have key := congrArg (fun f => (CommRingCat.Hom.hom f) ((pZ.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)))
    (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at key
  rw [key, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

section Scale

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma const_pull' {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (pY : Y ⟶ Spec (CommRingCat.of R)) (pZ : Z ⟶ Spec (CommRingCat.of R))
    (hφ : φ ≫ pZ = pY) (r : R) {U : Z.Opens} {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) :
    (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom (resTop U (scal pZ r))) = resTop W (scal pY r) := by
  subst hφ
  simp only [rs, resTop, scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have key := congrArg (fun f => (CommRingCat.Hom.hom f) ((pZ.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
    (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at key
  rw [key, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem expandsAt_scale (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (r : R) (h : U.ExpandsAt e k σ f) :
    U.ExpandsAt e k (SecOps.secScale (scal G.hom r) σ)
      (fun α => SecOps.secScale (scal D.toPre.P.A.hom r) (f α)) := by
  obtain ⟨S, hvan, hid⟩ := h
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt h1 hcoh => ?_⟩
  · show ((U.gt e).pG.left.app _).hom (resTop _ (scal D.toPre.P.A.hom r) * (f α).f j) = 0
    rw [map_mul, hvan α hα j, mul_zero]
  · have e0 := hid p j₁ jf jt h1 hcoh
    set W := U.expW e p j₁ S jf jt
    have hG : (fstG I e G).left ≫ G.hom = ((Over.map (thick R I e)).obj (thickObj R I e G)).hom := Over.w _
    have hB : (U.gt e).pG.left ≫ D.toPre.P.A.hom = ((Over.map (thick R I e)).obj (thickObj R I e G)).hom :=
      Over.w _
    have e1 := congrArg (fun x => resTop W (scal ((Over.map (thick R I e)).obj (thickObj R I e G)).hom r) * x) e0
    simp only [Finset.mul_sum] at e1
    convert e1 using 1
    · simp only [SecOps.secScale]
      erw [map_mul, map_mul, const_pull' (fstG I e G).left _ G.hom (Over.w _) r (U := U.LG.L.wchart (fun _ => 𝟙 G.left) j₁)]
      exact mul_left_comm _ _ _
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      simp only [SecOps.secScale]
      erw [map_mul, map_mul, const_pull' (U.gt e).pG.left _ D.toPre.P.A.hom (Over.w _) r (U := D.toPre.P.L.wchart (D.toPre.famφB α.1) (jf α.1))]
      exact mul_assoc _ _ _

end Scale

theorem b_units_const (hGF : GlobalFnsSt) (D : DegData V (maximalIdeal V)) (f : Γ(D.toPre.P.A.left, ⊤)ˣ) :
    ∃ c : Γ(Spec (CommRingCat.of V), ⊤)ˣ, f = Units.map (D.toPre.P.A.hom.appTop).hom.toMonoidHom c := by
  have hbij := @hGF _ D.toPre.P.A D.toPre.P.grp D.toPre.P.isAb
  obtain ⟨c0, hc0⟩ := hbij.2 (f : Γ(D.toPre.P.A.left, ⊤))
  obtain ⟨c1, hc1⟩ := hbij.2 ((f⁻¹ : Γ(D.toPre.P.A.left, ⊤)ˣ) : Γ(D.toPre.P.A.left, ⊤))
  have h01 : c0 * c1 = 1 := hbij.1 (by rw [map_mul, hc0, hc1, Units.mul_inv, map_one])
  refine ⟨⟨c0, c1, h01, by rw [mul_comm]; exact h01⟩, ?_⟩
  ext
  exact hc0.symm

open scoped Classical in

theorem gen_one_of_zero (hGF : GlobalFnsSt) (D : DegData V (maximalIdeal V)) {K : Type} [Fintype K]
    (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ht : t.IsGen) (h0 : fsum φ ε = 0)
    (hv : LB.Gen.Corr D.toPre.P.L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim
      (LB.pullGen D.toPre.P.L φ ε t (eSec D.toPre.P.A)) (LB.oneGen D.toPre.P.L)) :
    ∀ j, LB.Coh D.toPre.P.L φ j → t.s j = 1 := by
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  have hs0 : LB.SameSum φ ε (K' := PEmpty) PEmpty.elim PEmpty.elim := by
    rw [sameSum_iff_fsum, h0, fsum_empty]
  obtain ⟨te, -, c2⟩ := gen_transport hL hs0 t ht
  let j0 : PEmpty → D.toPre.P.L.ι := PEmpty.elim
  let f : Γ(D.toPre.P.A.left, ⊤)ˣ := res (le_of_eq (wchart_empty j0).symm) (te.s j0)
  obtain ⟨c, hc⟩ := b_units_const hGF D f
  have hte : te.s j0 = res (fun _ _ => trivial :
      (LB.LinComb D.toPre.P.L (Y := D.toPre.P.A.left) (K := PEmpty) PEmpty.elim PEmpty.elim).U j0 ≤
      D.toPre.P.A.hom ⁻¹ᵁ ⊤) (pullU D.toPre.P.A.hom ⊤ c) := by
    have e1 : te.s j0 = res (le_of_eq (wchart_empty j0)) f := by
      simp only [f]
      exact (res_back _ _ _).symm
    rw [e1, hc, units_map_eq_res]
    erw [res_res']
    rfl
  have hzp : eSec D.toPre.P.A ≫ D.toPre.P.A.hom = 𝟙 _ := by
    exact Over.w η[D.toPre.P.A]
  have key : (LB.pullGen D.toPre.P.L _ _ te (eSec D.toPre.P.A)).s j0 = res le_top c := by
    show res _ (pullU _ _ (te.s j0)) = _
    rw [hte]
    exact pull_pull_id _ _ hzp _ _ c
  have hz1 : LB.Gen.Corr D.toPre.P.L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim
      (LB.pullGen D.toPre.P.L _ _ te (eSec D.toPre.P.A)) (LB.oneGen D.toPre.P.L) :=
    corr_trans hL (corr_pullGen (corr_symm c2) _) hv
  have hc1 : c = 1 := by
    have e := hz1 j0 j0 (fun k => k.elim) (fun k => k.elim) (fun k => k.elim)
    rw [key] at e
    change res _ (res _ c) = res _ (1 : Γ(Spec (CommRingCat.of V), _)ˣ) at e
    rw [map_one] at e
    erw [res_res'] at e
    exact eq_one_of_res_top _ (by ext y; simp [LB.wchart]) c e
  have hte1 : te.s j0 = 1 := by rw [hte, hc1, map_one, map_one]
  intro j hj
  have e := c2 j j0 hj (fun k => k.elim) (fun _ k => k.elim)
  rw [hte1] at e
  erw [map_one] at e
  have hle : LB.wchart D.toPre.P.L φ j ≤ LB.wchart D.toPre.P.L φ j ⊓ LB.wchart D.toPre.P.L PEmpty.elim j0 :=
    le_inf le_rfl (by rw [wchart_empty]; exact le_top)
  have e2 := congrArg (res hle) e
  erw [map_one, res_res', res_refl'] at e2
  exact e2

theorem exists_uR (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
    (oa : D.toPre.OAct O) (a : O) :
    ∃ uR : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε),
      uR.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uR (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L) := by
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  have hA := oa.onB.rosati (star a)
  rw [star_star] at hA
  obtain ⟨u0, hu0⟩ := gen_of_local_base hL (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε hA
  have hzp : zero2 D.toPre.P.A ≫ (toUnit (D.toPre.P.A ⊗ D.toPre.P.A)).left = 𝟙 _ := by
    simp only [zero2, ← Over.comp_left]
    rw [show _ ≫ toUnit (D.toPre.P.A ⊗ D.toPre.P.A) = 𝟙 _ from toUnit_unique _ _]
    rfl
  have hone : (LB.oneGen D.toPre.P.L (Y := (𝟙_ (Over (Spec (CommRingCat.of V)))).left)).IsGen := by
    intro i j
    show res _ 1 = _ * res _ 1
    rw [map_one, map_one, _root_.mul_one]
    simp [LB.LinComb]
    rfl
  refine exists_normalized_to hL _ _ u0 hu0 _ _ hzp _ _ _ hone ?_
  haveI := oa.onB.hom (star a)
  haveI := oa.onB.hom a
  have e : (fun k => zero2 D.toPre.P.A ≫ rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a) k) =
      fun _ => (η[D.toPre.P.A]).left := by
    funext i
    have h1 : (η[D.toPre.P.A] : 𝟙_ _ ⟶ D.toPre.P.A) = 1 := by rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have hm : (1 : 𝟙_ _ ⟶ D.toPre.P.A) * 1 = 1 := _root_.mul_one _
    fin_cases i
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫
        (padd D.toPre.P.A (fst _ _ ≫ oa.onB.act (star a)) (snd _ _)).left = _
      rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, lift_fst_assoc, lift_snd, IsMonHom.one_hom, h1, hm]
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫ (fst _ _ ≫ oa.onB.act (star a)).left = _
      rw [← Over.comp_left, lift_fst_assoc, IsMonHom.one_hom]
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫ (snd D.toPre.P.A D.toPre.P.A).left = _
      rw [← Over.comp_left, lift_snd]
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫
        (padd D.toPre.P.A (fst _ _) (snd _ _ ≫ oa.onB.act a)).left = _
      rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, lift_fst, lift_snd_assoc, IsMonHom.one_hom, h1, hm]
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫ (fst D.toPre.P.A D.toPre.P.A).left = _
      rw [← Over.comp_left, lift_fst]
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫ (snd _ _ ≫ oa.onB.act a).left = _
      rw [← Over.comp_left, lift_snd_assoc, IsMonHom.one_hom]
  rw [fsum_empty, e]
  simp [fsum, Fin.sum_univ_six, rosatiε, ← Finsupp.single_add]

lemma scal_pull {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (pY : Y ⟶ Spec (CommRingCat.of V)) (pZ : Z ⟶ Spec (CommRingCat.of V))
    (hφ : φ ≫ pZ = pY) (r : V) : φ.appTop.hom (scal pZ r) = scal pY r := by
  subst hφ
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

lemma scal_mul {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of V)) (r r' : V) : scal p (r * r') = scal p r * scal p r' := by
  simp only [scal, map_mul]

lemma resTop_mul {Y : Scheme.{0}} (W : Y.Opens) (c c' : Γ(Y, ⊤)) : resTop W (c * c') = resTop W c * resTop W c' :=
  map_mul _ _ _

lemma app_resTop {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (U : Z.Opens) {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) (c : Γ(Z, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom (resTop U c)) = resTop W (φ.appTop.hom c) := by
  simp only [resTop]
  have key := congrArg (fun f => (CommRingCat.Hom.hom f) c) (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at key
  rw [key, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma secScal_scale {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (hs : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (c' : Γ(Y, ⊤)) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ (SecOps.secScale c' s₂) h (h.appTop.hom c' * c) := by
  intro j₁ j₂ hj
  have e := hs j₁ j₂ hj
  show _ = _ * _
  erw [map_mul, map_mul, e, app_resTop, resTop_mul]
  exact (_root_.mul_assoc _ _ _).symm

lemma sec_eq_of_coh {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s t : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, LB.Coh L φ j → s.f j = t.f j) : ∀ j, s.f j = t.f j := by
  intro (j : K → L.ι)
  apply sec_ext_cover (LB.wchart L φ j) (fun ρ => LB.wchart L φ j ⊓ piece L φ φ ρ) (fun _ => inf_le_left)
    (le_iSup_piece L φ φ hL _)
  intro ρ
  have hV : LB.wchart L φ j ⊓ piece L φ φ ρ ≤ LB.wchart L φ j ⊓ LB.wchart L φ (ρ ∘ φ) :=
    fun _ hy => ⟨hy.1, hy.2.1⟩
  have hc : LB.Coh L φ (ρ ∘ φ) := fun k₁ k₂ e => by simp only [Function.comp, e]
  have es := sec_compat_rs s j (ρ ∘ φ) hV
  have et := sec_compat_rs t j (ρ ∘ φ) hV
  erw [es, et, h _ hc]

section BackK

variable {G : Over (Spec (CommRingCat.of V))}

lemma scal_unit_K (lam : V) (hlam : lam ≠ 0) {W : (pullback G.hom (jK V)).Opens} :
    IsUnit (resTop W (scal (pullback.snd G.hom (jK V) ≫ jK V) lam)) := by
  have hK : IsUnit (algebraMap V (FractionRing V) lam) := by
    have h0 : algebraMap V (FractionRing V) lam ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap V (FractionRing V))]
      exact (IsFractionRing.injective V (FractionRing V)).ne hlam
    exact h0.isUnit
  have e : scal (pullback.snd G.hom (jK V) ≫ jK V) lam =
      (pullback.snd G.hom (jK V)).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) lam)) := by
    simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    congr 1
    have := congrArg (fun f => (CommRingCat.Hom.hom f) lam)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  rw [e]
  exact (hK.map _).map _ |>.map _

lemma rs_resTop {Y : Scheme.{0}} {W W' : Y.Opens} (h : W' ≤ W) (c : Γ(Y, ⊤)) : rs h (resTop W c) = resTop W' c :=
  SecOps.resTop_res h c

lemma app_rs_alt {Y Z : Scheme.{0}} (φ : Y ⟶ Z) {U U' : Z.Opens} {W : Y.Opens} (o : U ≤ U') (w : W ≤ φ ⁻¹ᵁ U)
    (w' : W ≤ φ ⁻¹ᵁ U') (z : Γ(Z, U')) : rs w ((φ.app U).hom (rs o z)) = rs w' ((φ.app U').hom z) := by
  simp only [rs, ← CommRingCat.comp_apply]
  rw [Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
  rfl

lemma comp_app_rs {X Y Z : Scheme.{0}} (φ : Y ⟶ Z) (ψ : Z ⟶ X) {U : X.Opens} {W : Y.Opens}
    (w : W ≤ (φ ≫ ψ) ⁻¹ᵁ U) (w' : W ≤ φ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) (z : Γ(X, U)) :
    rs w (((φ ≫ ψ).app U).hom z) = rs w' ((φ.app (ψ ⁻¹ᵁ U)).hom ((ψ.app U).hom z)) := by
  rw [Scheme.Hom.comp_app]
  rfl

lemma app_congr_rs {Y Z : Scheme.{0}} (φ ψ : Y ⟶ Z) (e : φ = ψ) {U : Z.Opens} {W : Y.Opens} (w : W ≤ φ ⁻¹ᵁ U)
    (w' : W ≤ ψ ⁻¹ᵁ U) (z : Γ(Z, U)) : rs w ((φ.app U).hom z) = rs w' ((ψ.app U).hom z) := by
  subst e
  rfl

lemma app_resTop_alt {Y Z : Scheme.{0}} (φ : Y ⟶ Z) {U : Z.Opens} {W : Y.Opens} (w : W ≤ φ ⁻¹ᵁ U) (c : Γ(Z, ⊤)) :
    rs w ((φ.app U).hom (resTop U c)) = resTop W (φ.appTop.hom c) := app_resTop φ U w c

lemma shape_cross {Y Y' : Scheme.{0}} (h : Y' ⟶ Y) (e : Y' ⟶ Y') (fl : Y ⟶ Y) (he : e ≫ h = h ≫ fl)
    (c : Fin 2 → Γ(Y', ⊤)) (hce : ∀ i, e.appTop.hom (c i) = c i)
    {Ua Ub O : Y.Opens} {Sa Sb Wa Wb W : Y'.Opens}
    (oa : O ≤ Ua) (ob : O ≤ fl ⁻¹ᵁ Ub) (hWa : Wa ≤ h ⁻¹ᵁ Ua) (hWa' : Wa ≤ Sa) (hWb : Wb ≤ h ⁻¹ᵁ Ub) (hWb' : Wb ≤ Sb)
    (wO : W ≤ h ⁻¹ᵁ O) (wa : W ≤ Wa) (wSa : W ≤ Sa) (wb : W ≤ e ⁻¹ᵁ Wb) (wSb : W ≤ e ⁻¹ᵁ Sb)
    (hunit : ∀ i, IsUnit (resTop W (c i)))
    (σ : Fin 2 → Γ(Y, Ua)) (τ : Fin 2 → Γ(Y, Ub)) (x : Fin 2 → Γ(Y', Sa)) (y : Fin 2 → Γ(Y', Sb))
    (hC : rs oa (σ 0) * rs ob ((fl.app Ub).hom (τ 1)) = rs oa (σ 1) * rs ob ((fl.app Ub).hom (τ 0)))
    (hσ : ∀ i, rs hWa ((h.app Ua).hom (σ i)) = resTop Wa (c i) * rs hWa' (x i))
    (hτ : ∀ i, rs hWb ((h.app Ub).hom (τ i)) = resTop Wb (c i) * rs hWb' (y i)) :
    rs wSa (x 0) * rs wSb ((e.app Sb).hom (y 1)) = rs wSa (x 1) * rs wSb ((e.app Sb).hom (y 0)) := by

  have h1 := congrArg (rs wO) (congrArg (h.app O).hom hC)
  rw [map_mul, map_mul, rs_mul, rs_mul] at h1

  have fσ : ∀ i, rs wO ((h.app O).hom (rs oa (σ i))) = resTop W (c i) * rs wSa (x i) := by
    intro i
    have := congrArg (rs wa) (hσ i)
    rw [rs_mul, rs_resTop, rs_rs, rs_rs] at this
    rw [app_rs_alt h oa wO (wa.trans hWa)]
    exact this
  have fτ : ∀ i, rs wO ((h.app O).hom (rs ob ((fl.app Ub).hom (τ i)))) =
      resTop W (c i) * rs wSb ((e.app Sb).hom (y i)) := by
    intro i
    have w1 : W ≤ h ⁻¹ᵁ (fl ⁻¹ᵁ Ub) := fun p hp => ob (wO hp)
    have w2 : W ≤ (e ≫ h) ⁻¹ᵁ Ub := fun p hp => by
      have := w1 hp
      show p ∈ (e ≫ h) ⁻¹ᵁ Ub
      rw [he]
      exact this
    have w3 : W ≤ e ⁻¹ᵁ (h ⁻¹ᵁ Ub) := w2
    rw [app_rs_alt h ob wO w1, ← comp_app_rs h fl w1 w1, app_congr_rs (h ≫ fl) (e ≫ h) he.symm w1 w2,
      comp_app_rs e h w2 w3, ← app_rs_alt e hWb wb w3, hτ i, map_mul, rs_mul, app_resTop_alt, hce,
      app_rs_alt e hWb' wb wSb]
  rw [fσ, fσ, fτ, fτ] at h1
  obtain ⟨u0, hu0⟩ := hunit 0
  obtain ⟨u1, hu1⟩ := hunit 1
  rw [← hu0, ← hu1] at h1
  have h2 : (↑u0 * ↑u1) * (rs wSa (x 0) * rs wSb ((e.app Sb).hom (y 1))) =
      (↑u0 * ↑u1) * (rs wSa (x 1) * rs wSb ((e.app Sb).hom (y 0))) := by
    linear_combination h1
  exact (Units.mul_right_inj (u0 * u1)).1 (by simpa [Units.val_mul] using h2)

theorem cross_to_K (LG : LB G.left) (hLG : LG.IsLB) (f : G ⟶ G) (k m : ℕ)
    (σ : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (m : ℤ))))
    (τ : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (s'' : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (m : ℤ))))
    (s : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ))))
    (lam : Fin 2 → V) (hlam : ∀ i, lam i ≠ 0)
    (hσ : ∀ i, GeneratorPullback.SecScal LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (m : ℤ)) (s'' i)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (m : ℤ)) (σ i) (pullback.fst G.hom (jK V))
      (scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i)))
    (hτ : ∀ i, GeneratorPullback.SecScal LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) (s i)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) (τ i) (pullback.fst G.hom (jK V))
      (scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i)))
    (hC : ∀ j, (mulSec LG _ _ _ _ (σ 0) (pullSec LG _ _ (τ 1) f.left)).f j =
      (mulSec LG _ _ _ _ (σ 1) (pullSec LG _ _ (τ 0) f.left)).f j) :
    ∀ j, (mulSec LG _ _ _ _ (s'' 0) (pullSec LG _ _ (s 1) (endK f))).f j =
      (mulSec LG _ _ _ _ (s'' 1) (pullSec LG _ _ (s 0) (endK f))).f j := by
  apply sec_eq_of_coh hLG
  intro J _
  have he : endK f ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ f.left := by
    unfold endK
    exact pullback.lift_fst _ _ _
  have hce : ∀ i, (endK f).appTop.hom (scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i)) =
      scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i) := fun i =>
    scal_pull (endK f) _ _ (by unfold endK; rw [← Category.assoc, pullback.lift_snd, Category.comp_id]) (lam i)
  have hCJ := hC J
  simp only [mulSec, pullSec] at hCJ ⊢
  erw [rs_rs, rs_rs] at hCJ
  erw [rs_rs, rs_rs]
  have hbase : ∀ p, (endK f ≫ pullback.fst G.hom (jK V)).base p = (pullback.fst G.hom (jK V) ≫ f.left).base p :=
    fun p => by rw [he]
  have mW : ∀ p ∈ LB.wchart LG (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK V))
      (fun _ : Fin 1 => endK f ≫ pullback.fst G.hom (jK V))) J,
      (pullback.fst G.hom (jK V)).base p ∈ LG.U (J (Sum.inl 0)) ∧
      (pullback.fst G.hom (jK V) ≫ f.left).base p ∈ LG.U (J (Sum.inr 0)) := fun p hp =>
    ⟨Set.mem_iInter.1 hp (Sum.inl 0), hbase p ▸ Set.mem_iInter.1 hp (Sum.inr 0)⟩
  have f1 : ∀ (q : Fin 1), q = 0 := fun q => Subsingleton.elim _ _
  have key := shape_cross (pullback.fst G.hom (jK V)) (endK f) f.left he
    (fun i => scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i)) hce
    (Ua := LB.wchart LG (fun _ : Fin 1 => 𝟙 G.left) (J ∘ Sum.inl))
    (Ub := LB.wchart LG (fun _ : Fin 1 => 𝟙 G.left) (J ∘ Sum.inr))
    (O := LB.wchart LG (Sum.elim (fun _ : Fin 1 => 𝟙 G.left) (fun _ : Fin 1 => f.left ≫ 𝟙 G.left)) J)
    (Sa := LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (J ∘ Sum.inl))
    (Sb := LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (J ∘ Sum.inr))
    (Wa := LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (J ∘ Sum.inl) ⊓
      LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V) ≫ 𝟙 G.left) (J ∘ Sum.inl))
    (Wb := LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (J ∘ Sum.inr) ⊓
      LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V) ≫ 𝟙 G.left) (J ∘ Sum.inr))
    (W := LB.wchart LG (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK V))
      (fun _ : Fin 1 => endK f ≫ pullback.fst G.hom (jK V))) J)
    _ _ _ _ _ _
    (fun p hp => Set.mem_iInter.2 fun q => by
      rcases q with q | q <;> rw [f1 q]
      · exact (mW p hp).1
      · exact (mW p hp).2)
    (fun p hp => ⟨Set.mem_iInter.2 fun q => by rw [f1 q]; exact (mW p hp).1,
      Set.mem_iInter.2 fun q => by rw [f1 q]; exact (mW p hp).1⟩)
    (fun p hp => Set.mem_iInter.2 fun q => by rw [f1 q]; exact (mW p hp).1)
    (fun p hp => ⟨Set.mem_iInter.2 fun q => by rw [f1 q]; exact Set.mem_iInter.1 hp (Sum.inr 0),
      Set.mem_iInter.2 fun q => by rw [f1 q]; exact Set.mem_iInter.1 hp (Sum.inr 0)⟩)
    (fun p hp => Set.mem_iInter.2 fun q => by rw [f1 q]; exact Set.mem_iInter.1 hp (Sum.inr 0))
    (fun i => scal_unit_K (lam i) (hlam i))
    (fun i => (σ i).f (J ∘ Sum.inl)) (fun i => (τ i).f (J ∘ Sum.inr))
    (fun i => (s'' i).f (J ∘ Sum.inl)) (fun i => (s i).f (J ∘ Sum.inr)) hCJ
    (fun i => hσ i _ _ (fun k₁ k₂ _ => by rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> congr 1 <;> exact Subsingleton.elim _ _))
    (fun i => hτ i _ _ (fun k₁ k₂ _ => by rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> congr 1 <;> exact Subsingleton.elim _ _))
  exact key

end BackK

section Integral

variable (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end Integral

end ReciprocityTheory.ChartRestriction.G.DVR
