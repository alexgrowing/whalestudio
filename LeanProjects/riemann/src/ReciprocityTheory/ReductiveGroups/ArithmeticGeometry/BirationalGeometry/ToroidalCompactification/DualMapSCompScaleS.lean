import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSOfIdToRingHom

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

theorem toAlgHom_restrict {S : Type} [CommRing S] (R : Type) [CommRing R] [Algebra S R] (A A' : Type) [CommRing A]
    [Algebra S A] [Algebra R A] [IsScalarTower S R A] [CommRing A'] [Algebra S A'] [Algebra R A'] [IsScalarTower S R A']
    [Algebra A A'] [IsScalarTower R A A'] [IsScalarTower S A A'] :
    (IsScalarTower.toAlgHom R A A').restrictScalars S = IsScalarTower.toAlgHom S A A' := AlgHom.ext fun _ => rfl

section Wrap

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] {s : S} (C : Chart (Gs G s))
  [Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U)]
  {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A]
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A'] [IsScalarTower S (Localization.Away s) A']
  [Algebra A A'] [IsScalarTower (Localization.Away s) A A'] [IsScalarTower S A A']
  (M : Submonoid (Localization.Away s)) [IsLocalization (Algebra.algebraMapSubmonoid A M) A']

include C in
theorem tanS_lift {y' : sp (R₀ := S) (DualNumber A') ⟶ G} (hy' : TanS y') :
    ∃ m ∈ M, ∃ y : sp (R₀ := S) (DualNumber A) ⟶ G, TanS y ∧
      spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y =
        spMap (scaleS (S := S) (algebraMap (Localization.Away s) A' m)) ≫ y' := by
  obtain ⟨h', hh', rfl⟩ := tanS_chart C hy'
  have hh'' : IsTanAt ((IsScalarTower.toAlgHom (Localization.Away s) A A').comp (epsA C A)) h' := by
    intro b
    rw [hh' b]
    show algebraMap (Localization.Away s) A' (eps C b) = algebraMap A A' (algebraMap (Localization.Away s) A (eps C b))
    exact IsScalarTower.algebraMap_apply _ _ _ _
  obtain ⟨m, hm, h, hh, he⟩ := tan_lift (epsA C A) M h' hh''
  refine ⟨m, hm, pushR G (pt C h), chart_tanS C h hh, ?_⟩
  rw [← toAlgHom_restrict (Localization.Away s) A A', chart_map, he, chart_scale]

include C in
theorem tanS_uniq {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h₁ : TanS y₁) (h₂ : TanS y₂)
    (he : spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y₁ = spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y₂) :
    ∃ m ∈ M, spMap (scaleS (S := S) (algebraMap (Localization.Away s) A m)) ≫ y₁ =
      spMap (scaleS (S := S) (algebraMap (Localization.Away s) A m)) ≫ y₂ := by
  obtain ⟨g₁, t₁, rfl⟩ := tanS_chart C h₁
  obtain ⟨g₂, t₂, rfl⟩ := tanS_chart C h₂
  rw [← toAlgHom_restrict (Localization.Away s) A A', chart_map, chart_map] at he
  obtain ⟨m, hm, hc⟩ := tan_uniq (epsA C A) M g₁ g₂ t₁ t₂ (chart_inj C he)
  exact ⟨m, hm, by rw [chart_scale, chart_scale, hc]⟩

end Wrap

section Scale

variable {S : Type} [CommRing S]

private theorem dualMapS_fst' {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A']
    (j : A →ₐ[S] A') (y : DualNumber A) : (dualMapS j y).fst = j y.fst := by
  simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]

private theorem dualMapS_snd' {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A']
    (j : A →ₐ[S] A') (y : DualNumber A) : (dualMapS j y).snd = j y.snd := by
  simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]

private theorem scaleS_fst' {A : Type} [CommRing A] [Algebra S A] (c : A) (y : DualNumber A) :
    (scaleS (S := S) c y).fst = y.fst := by
  simp [scaleS]

private theorem scaleS_snd' {A : Type} [CommRing A] [Algebra S A] (c : A) (y : DualNumber A) :
    (scaleS (S := S) c y).snd = c * y.snd := by
  simp [scaleS]

theorem scaleS_comp {A : Type} [CommRing A] [Algebra S A] (a b : A) :
    (scaleS (S := S) a).comp (scaleS b) = scaleS (a * b) := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [scaleS] <;> ring

theorem dualMapS_comp_scaleS {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (j : A →ₐ[S] A')
    (c : A) : (dualMapS j).comp (scaleS c) = (scaleS (j c)).comp (dualMapS j) := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_fst', scaleS_fst', scaleS_fst',
      dualMapS_fst']
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_snd', scaleS_snd', scaleS_snd',
      dualMapS_snd', map_mul]

theorem dualMapS_comp {A A' A'' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] [CommRing A'']
    [Algebra S A''] (j : A →ₐ[S] A') (j' : A' →ₐ[S] A'') : (dualMapS j').comp (dualMapS j) = dualMapS (j'.comp j) := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · rw [AlgHom.comp_apply, dualMapS_fst', dualMapS_fst', dualMapS_fst', AlgHom.comp_apply]
  · rw [AlgHom.comp_apply, dualMapS_snd', dualMapS_snd', dualMapS_snd', AlgHom.comp_apply]

theorem scaleS_one {A : Type} [CommRing A] [Algebra S A] : scaleS (S := S) (1 : A) = AlgHom.id S _ := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [scaleS]

variable {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem res_scale {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (j : A →ₐ[S] A') (c : A)
    (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (dualMapS j) ≫ spMap (scaleS c) ≫ y = spMap (scaleS (j c)) ≫ spMap (dualMapS j) ≫ y := by
  rw [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, dualMapS_comp_scaleS]

theorem scale_scale {A : Type} [CommRing A] [Algebra S A] (a b : A) (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (scaleS (S := S) a) ≫ spMap (scaleS b) ≫ y = spMap (scaleS (a * b)) ≫ y := by
  rw [← Category.assoc, spMap_comp, scaleS_comp]

theorem res_res {A A' A'' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] [CommRing A'']
    [Algebra S A''] (j : A →ₐ[S] A') (j' : A' →ₐ[S] A'') (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (dualMapS j') ≫ spMap (dualMapS j) ≫ y = spMap (dualMapS (j'.comp j)) ≫ y := by
  rw [← Category.assoc, spMap_comp, dualMapS_comp]

end Scale

section Over

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

abbrev Qv (s t : S) : Type := Localization.Away (algebraMap S (Localization.Away s) t)

abbrev qL (s t : S) : Localization.Away s →ₐ[S] Qv s t := IsScalarTower.toAlgHom S _ _

theorem isUnit_qv (s t : S) : IsUnit (algebraMap S (Qv s t) t) := by
  rw [IsScalarTower.algebraMap_apply S (Localization.Away s) (Qv s t)]
  exact IsLocalization.Away.algebraMap_isUnit _

def qR (s t : S) : Localization.Away t →ₐ[S] Qv s t :=
  { IsLocalization.Away.lift t (isUnit_qv s t) with
    commutes' := fun r => IsLocalization.Away.lift_eq t (isUnit_qv s t) r }

theorem dualMapR_comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A') (g : A' →+* A'') :
    dualMapR (g.comp f) = (dualMapR g).comp (dualMapR f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMapR]

theorem glue_tan' {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G) (hw : ∀ k, TanS (w k))
    (hQ : ∀ k l, spMap (dualMapS (qL (s k) (s l))) ≫ w k = spMap (dualMapS (qR (s k) (s l))) ≫ w l) :
    ∃ v : sp (R₀ := S) (DualNumber S) ⟶ G, TanS v ∧
      ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := by
  refine glue_tan s hs w hw ?_
  intro k l T α β hαβ
  have hin : ∀ x : S, α (TrivSqZeroExt.inl (algebraMap S (Localization.Away (s k)) x)) =
      β (TrivSqZeroExt.inl (algebraMap S (Localization.Away (s l)) x)) := by
    intro x
    have h1 := RingHom.congr_fun hαβ (TrivSqZeroExt.inl x)
    simpa [dAway, dualMapR] using h1
  have heps : α (TrivSqZeroExt.inr 1) = β (TrivSqZeroExt.inr 1) := by
    have h1 := RingHom.congr_fun hαβ (TrivSqZeroExt.inr 1)
    simpa [dAway, dualMapR] using h1
  have hu : IsUnit (α (TrivSqZeroExt.inl (algebraMap S (Localization.Away (s k)) (s l)))) := by
    rw [hin]
    exact (IsLocalization.Away.algebraMap_isUnit (s l)).map (β.comp (TrivSqZeroExt.inlHom _ _))
  obtain ⟨g0, hg0⟩ : ∃ g0 : Qv (s k) (s l) →+* T, ∀ a,
      g0 (algebraMap (Localization.Away (s k)) (Qv (s k) (s l)) a) = α (TrivSqZeroExt.inl a) :=
    ⟨IsLocalization.Away.lift _ (g := α.comp (TrivSqZeroExt.inlHom _ _)) hu,
      fun a => IsLocalization.Away.lift_eq _ (g := α.comp (TrivSqZeroExt.inlHom _ _)) hu a⟩
  have he2 : α (TrivSqZeroExt.inr 1) * α (TrivSqZeroExt.inr 1) = 0 := by
    rw [← map_mul]; simp
  obtain ⟨gm, hgm⟩ : ∃ gm : DualNumber (Qv (s k) (s l)) →+* T, ∀ x,
      gm x = g0 x.fst + g0 x.snd * α (TrivSqZeroExt.inr 1) :=
    ⟨{ toFun := fun x => g0 x.fst + g0 x.snd * α (TrivSqZeroExt.inr 1)
       map_one' := by simp
       map_mul' := fun x y => by
         simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
           op_smul_eq_mul, map_add, map_mul]
         linear_combination (-(g0 x.snd * g0 y.snd)) * he2
       map_zero' := by simp
       map_add' := fun x y => by
         simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]
         ring }, fun _ => rfl⟩
  have hdec : ∀ {R : Type} [CommRing R] (x : DualNumber R),
      x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * TrivSqZeroExt.inr 1 := by
    intro R _ x
    ext <;> simp
  have hR : g0.comp (qR (s k) (s l)).toRingHom = β.comp (TrivSqZeroExt.inlHom _ _) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (s l))
    ext x
    show g0 (qR (s k) (s l) (algebraMap S _ x)) = β (TrivSqZeroExt.inl (algebraMap S _ x))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply S (Localization.Away (s k)) (Qv (s k) (s l)),
      hg0, hin]
  have hR' : ∀ a, g0 (qR (s k) (s l) a) = β (TrivSqZeroExt.inl a) := fun a => RingHom.congr_fun hR a
  have hα : α = gm.comp (dualMapS (qL (s k) (s l))).toRingHom := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, hgm]
    conv_lhs => rw [hdec x]
    rw [map_add, map_mul]
    simp [dualMapS_fst', dualMapS_snd', hg0]
  have hβ : β = gm.comp (dualMapS (qR (s k) (s l))).toRingHom := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, hgm]
    conv_lhs => rw [hdec x]
    rw [map_add, map_mul]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dualMapS_fst', dualMapS_snd', hR', heps]
  have hk := congrArg (fun f => f.left) (hQ k l)
  simp only [Over.comp_left, spMap, Over.homMk_left] at hk
  rw [hα, hβ, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, hk]

set_option backward.isDefEq.respectTransparency false in

theorem tan_ext_cover {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    {v₁ v₂ : sp (R₀ := S) (DualNumber S) ⟶ G}
    (h : ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v₁ =
      spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v₂) : v₁ = v₂ := by
  have hs' : Ideal.span (Set.range (fun k => (TrivSqZeroExt.inl (s k) : DualNumber S))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom S S)) hs
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber S)) _ hs').openCover
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : Fin n) => ?_
  have e : 𝒰.f k = Spec.map (CommRingCat.ofHom (toL (s k))) ≫ Spec.map (CommRingCat.ofHom (dAway (s k))) := by
    show Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k)))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← toL_comp]
  rw [e, Category.assoc, Category.assoc]
  congr 1
  exact congrArg (fun q => Over.Hom.left q) (h k)

end Over

end ReciprocityTheory.ChartRestriction.G.Chart
