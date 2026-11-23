import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechComplexTrivialLineBundleNotAcyclicStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PicardGroupOfFieldTrivialStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOfSectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOutsideFiniteSetStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVarietyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
open GlobalTheory.CompanionTheory.PointSurjectivity
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

section Lemmas

variable {k : Type} [Field k] {A T : Over (Sp k)} {M : LB (A ⊗ T).left}

theorem pull_evc_const (hM : M.IsLB) (t₀ : 𝟙_ (Over (Sp k)) ⟶ T) {Y : Over (Sp k)} (a : Y ⟶ A) :
    GlobalTheory.CechPic.pull a.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) = evc hM a (toUnit Y ≫ t₀) := by
  rw [pull_evc, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem pull_mul_evc_const [GrpObj A] (hM : M.IsLB) (hadd : IsAdditive M) (t₀ : 𝟙_ (Over (Sp k)) ⟶ T)
    {Y : Over (Sp k)} (a a' : Y ⟶ A) :
    GlobalTheory.CechPic.pull (a * a').left (evc hM (𝟙 A) (toUnit A ≫ t₀)) =
      GlobalTheory.CechPic.pull a.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) +
        GlobalTheory.CechPic.pull a'.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) := by
  rw [pull_evc_const, pull_evc_const, pull_evc_const]
  exact (isAdditive_iff hM).1 hadd Y a a' _

end Lemmas

set_option maxHeartbeats 2000000 in

theorem pointSurj_pf : (∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, ∀ hM : M.IsLB, (∀ (Y : Over (Sp k)) (a a' : Y ⟶ A), GlobalTheory.CechPic.pull (a * a').left (cls M hM) = GlobalTheory.CechPic.pull a.left (cls M hM) + GlobalTheory.CechPic.pull a'.left (cls M hM)) → ¬ Triv M → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB A.hom M D).Acyclic) → PointSurj := by
  intro hAA k _ _ A B _ _ hA hB P hP hadd hadd' hfin M hM haddM
  by_contra hno
  push Not at hno
  have : IsCommMonObj A := hA.comm
  have : IsCommMonObj B := hB.comm
  have hpA : IsProjBy A.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k A hA
  have hpB : IsProjBy B.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have hpq : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  have hsw : (swap P).IsLB := pull_isLB hP _
  obtain ⟨G, hG, eG⟩ := cls_surj
    (GlobalTheory.CechPic.pull (lift (fst A B) (toUnit (A ⊗ B))).left (cls M hM) - cls P hP)
  have cst : ∀ {X : Over (Sp k)} (x : 𝟙_ (Over (Sp k)) ⟶ X) (Y : Over (Sp k)),
      (toUnit Y ≫ x).left = Y.hom ≫ x.left := fun x Y =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit Y)))

  have sl₁ : ∀ y' : 𝟙_ (Over (Sp k)) ⟶ B, cls _ (pull_isLB hG (lift (𝟙 A) (toUnit A ≫ y')).left) =
      evc hM (𝟙 A) (toUnit A ≫ 𝟙 _) - evc hP (𝟙 A) (toUnit A ≫ y') := fun y' => by
    rw [cls_pull hG, eG, map_sub, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, comp_toUnit,
      Category.comp_id]
    rfl

  have sl₂ : ∀ x' : 𝟙_ (Over (Sp k)) ⟶ A, cls _ (pull_isLB hG (lift (toUnit B ≫ x') (𝟙 B)).left) =
      - evc hsw (𝟙 B) (toUnit B ≫ x') := fun x' => by
    rw [cls_pull hG, eG, map_sub, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, comp_toUnit]
    have e₁ : GlobalTheory.CechPic.pull (lift (toUnit B ≫ x') (toUnit B)).left (cls M hM) = 0 := by
      have e := pull_evc hM (toUnit B) x' (𝟙 _)
      rw [Category.comp_id, GlobalTheory.T.picard_group_of_field_trivial k (evc hM x' (𝟙 _)), map_zero] at e
      exact e.symm
    rw [e₁, zero_sub, evc_swap hP hsw]
    rfl
  have fibB : ∀ (y : Sp k ⟶ B.left) (σ : A.left ⟶ (A ⊗ B).left), y ≫ B.hom = 𝟙 _ →
      σ ≫ (fst A B).left = 𝟙 _ → σ ≫ (snd A B).left = A.hom ≫ y → FibAc A.hom (G.pull σ) := by
    intro y σ hy h₁ h₂
    let y' : 𝟙_ (Over (Sp k)) ⟶ B := Over.homMk y hy
    have hσ : σ = (lift (𝟙 A) (toUnit A ≫ y')).left := by
      refine hpq.hom_ext ?_ ?_
      · rw [h₁, ← Over.comp_left, lift_fst]
        rfl
      · rw [h₂, ← Over.comp_left, lift_snd, cst]
        rfl
    subst hσ
    intro κ _ _ D hD hc
    refine hAA k A hA _ (pull_isLB hG _) (fun Y a a' => ?_) (fun ht => ?_) κ D hD hc
    · rw [sl₁ y', map_sub, map_sub, map_sub, pull_mul_evc_const hM haddM, pull_mul_evc_const hP hadd]
      abel
    · have h0 := (cls_eq_zero_iff (pull_isLB hG _)).2 ht
      rw [sl₁ y', sub_eq_zero] at h0
      refine hno y' ((cls_eq_iff hM (pull_isLB hP _)).1 ?_)
      have e := congrArg (GlobalTheory.CechPic.pull (fst A (𝟙_ (Over (Sp k)))).left) h0
      rw [pull_evc, pull_evc, Category.comp_id, Category.comp_id,
        ← Category.assoc (fst A _) (toUnit A) y',
        toUnit_unique (fst A (𝟙_ (Over (Sp k))) ≫ toUnit A) (snd A _)] at e
      refine Eq.trans ?_ (e.trans (cls_ev hP _ _ _).symm)
      rw [evc, lift_fst_snd, Over.id_left, pull_id]
  have htot : FibAc ((fst A B).left ≫ A.hom) G :=
    GlobalTheory.T.fibre_acyclicity_of_sections A.hom B.hom (fst A B).left (snd A B).left hpq hpA G hG fibB
  let F' : Set (Sp k ⟶ A.left) :=
    (fun x : 𝟙_ (Over (Sp k)) ⟶ A => x.left) '' {x | Triv (ev P (toUnit B ≫ x) (𝟙 B))}
  have fibA : ∀ (y : Sp k ⟶ A.left) (σ : B.left ⟶ (A ⊗ B).left), y ≫ A.hom = 𝟙 _ →
      σ ≫ (snd A B).left = 𝟙 _ → σ ≫ (fst A B).left = B.hom ≫ y → y ∉ F' → FibAc B.hom (G.pull σ) := by
    intro y σ hy h₁ h₂ hyF
    let x' : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk y hy
    have hσ : σ = (lift (toUnit B ≫ x') (𝟙 B)).left := by
      refine hpq.hom_ext ?_ ?_
      · rw [h₂, ← Over.comp_left, lift_fst, cst]
        rfl
      · rw [h₁, ← Over.comp_left, lift_snd]
        rfl
    subst hσ
    intro κ _ _ D hD hc
    refine hAA k B hB _ (pull_isLB hG _) (fun Y a a' => ?_) (fun ht => ?_) κ D hD hc
    · rw [sl₂ x', map_neg, map_neg, map_neg, pull_mul_evc_const hsw hadd']
      abel
    · have h0 := (cls_eq_zero_iff (pull_isLB hG _)).2 ht
      rw [sl₂ x', neg_eq_zero, evc_swap hP hsw] at h0
      exact hyF ⟨x', (triv_ev_iff hP _ _).2 h0, rfl⟩
  have htot' : FibAc ((snd A B).left ≫ B.hom) G := hpq.w ▸ htot
  have hη : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  obtain ⟨m, D, hD, hc, hac⟩ := GlobalTheory.T.exists_affine_cover_cech_acyclic_of_fibAc_off_finite B.hom A.hom (snd A B).left (fst A B).left hpq.flip hpB G hG F'
    (hfin.image _) fibA htot' η[A].left (lift (toUnit B ≫ η[A]) (𝟙 B)).left hη
    (by rw [← Over.comp_left, lift_snd]; rfl) (by rw [← Over.comp_left, lift_fst, cst])
  have : Nonempty B.left := ⟨η[B].left (IsLocalRing.closedPoint k)⟩
  refine GlobalTheory.T.cech_complex_trivial_line_bundle_not_acyclic B.hom _ (pull_isLB hG _) ?_ (Fin m) D hc hac
  refine (cls_eq_zero_iff (pull_isLB hG _)).1 ?_
  rw [sl₂, evc_swap hP hsw, ← Hom.one_def, IsAdditive.evc_one hP hadd, neg_zero]

end CompanionTheory.PfDual
