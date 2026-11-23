import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EndLoc.HomGlue

theorem pmap_hom_ext {S Z Y : Scheme.{0}} (A : Over S) (𝒰 : Z.OpenCover) (t : Z ⟶ S)
    {g₁ g₂ : pullback A.hom t ⟶ Y} (h : ∀ i, pmap A t (𝒰.f i) ≫ g₁ = pmap A t (𝒰.f i) ≫ g₂) : g₁ = g₂ := by
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ (pullback.snd A.hom t)) _ _ fun (i : 𝒰.I₀) => ?_
  have w : (pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t) ≫ A.hom =
      pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ 𝒰.f i ≫ t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
  have e : pullback.fst (pullback.snd A.hom t) (𝒰.f i) = pullback.lift _ _ w ≫ pmap A t (𝒰.f i) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.condition]
  show pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ g₁ = pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ g₂
  rw [e, Category.assoc, Category.assoc, h]

theorem over_hom_ext_cover {Z : Scheme.{0}} (𝒰 : Z.OpenCover) {X Y : Over Z} {g₁ g₂ : X ⟶ Y}
    (h : ∀ i, (Over.pullback (𝒰.f i)).map g₁ = (Over.pullback (𝒰.f i)).map g₂) : g₁ = g₂ := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ X.hom) _ _ fun (i : 𝒰.I₀) => ?_
  have e1 : ((Over.pullback (𝒰.f i)).map g₁).left ≫ pullback.fst Y.hom (𝒰.f i) =
      pullback.fst X.hom (𝒰.f i) ≫ g₁.left := pullback.lift_fst _ _ _
  have e2 : ((Over.pullback (𝒰.f i)).map g₂).left ≫ pullback.fst Y.hom (𝒰.f i) =
      pullback.fst X.hom (𝒰.f i) ≫ g₂.left := pullback.lift_fst _ _ _
  show pullback.fst X.hom (𝒰.f i) ≫ g₁.left = pullback.fst X.hom (𝒰.f i) ≫ g₂.left
  rw [← e1, ← e2, h i]

theorem isMonHom_of_cover {Z : Scheme.{0}} (𝒰 : Z.OpenCover) {G H : Over Z} [MonObj G] [MonObj H] (f : G ⟶ H)
    (hf : ∀ i, IsMonHom ((Over.pullback (𝒰.f i)).map f)) : IsMonHom f := by
  constructor
  · refine over_hom_ext_cover 𝒰 fun i => ?_
    have h := (hf i).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at h
    rw [Functor.map_comp, h]
  · refine over_hom_ext_cover 𝒰 fun i => ?_
    have h := (hf i).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.LaxMonoidal.μ_natural_assoc, Category.assoc,
      cancel_epi] at h
    rw [Functor.map_comp, Functor.map_comp, h]

theorem lbIso_pull_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Y' ⟶ Y) :
    LBIso ((L.pull a).pull b) (L.pull (b ≫ a)) :=
  LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
    fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _))

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem wit_w {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} (g : Z' ⟶ Z)
    (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f)) :
    pmap A t g ≫ f ≫ B.hom = pmap A t g ≫ pullback.snd A.hom t ≫ t := by
  obtain ⟨A', B', _, _, φA, φB, Φ, hA, hB, -, -, e, e1, e2, e3⟩ := h
  haveI : IsIso e := by
    have : e = hA.1.isoPullback.hom :=
      pullback.hom_ext (by rw [e1, IsPullback.isoPullback_hom_fst]) (by rw [e2, IsPullback.isoPullback_hom_snd])
    rw [this]
    infer_instance
  rw [← cancel_epi e]
  calc e ≫ pmap A t g ≫ f ≫ B.hom = (e ≫ pmap A t g ≫ f) ≫ B.hom := by simp only [Category.assoc]
    _ = A'.hom ≫ g ≫ t := by rw [e3, Category.assoc, hB.1.w, Over.w_assoc]
    _ = e ≫ pmap A t g ≫ pullback.snd A.hom t ≫ t := by
        rw [pullback.lift_snd_assoc, Category.assoc, reassoc_of% e2]

theorem isMonHom_pull_of_wit {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} (g : Z' ⟶ Z)
    (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f)) (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B)
    (hΦ : Φ.left ≫ pullback.fst B.hom t = f) : IsMonHom ((Over.pullback g).map Φ) := by
  obtain ⟨A', B', _, _, φA, φB, Φ', hA, hB, hΦ', -, e, e1, e2, e3⟩ := h
  have hPA := (isGrpPullback_pullback ((Over.pullback t).obj A) g).comp (isGrpPullback_pullback A t)
  have hPB := (isGrpPullback_pullback ((Over.pullback t).obj B) g).comp (isGrpPullback_pullback B t)
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hPA hA
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hB hPB
  have key : a.hom.left ≫ e ≫ pmap A t g = pullback.fst _ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, e1, ha']
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, reassoc_of% e2, Over.w_assoc a.hom]
      exact pullback.condition.symm
  have hmap : ((Over.pullback g).map Φ).left ≫ pullback.fst _ g = pullback.fst _ g ≫ Φ.left :=
    pullback.lift_fst _ _ _
  have eq : (Over.pullback g).map Φ = a.hom ≫ Φ' ≫ b.hom := by
    apply Over.OverMorphism.ext
    apply hPB.1.hom_ext
    · have lhs : ((Over.pullback g).map Φ).left ≫ pullback.fst _ g ≫ pullback.fst B.hom t =
          pullback.fst _ g ≫ f := by
        rw [← Category.assoc, hmap, Category.assoc, hΦ]
      have rhs : (a.hom ≫ Φ' ≫ b.hom).left ≫ pullback.fst _ g ≫ pullback.fst B.hom t =
          pullback.fst _ g ≫ f := by
        simp only [Over.comp_left, Category.assoc]
        rw [hb', ← e3, ← key]
        simp only [Category.assoc]
      exact lhs.trans rhs.symm
    · exact (Over.w _).trans (Over.w _).symm
  rw [eq]
  infer_instance

theorem local_iso (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left}
    (g : Z' ⟶ Z) [IsOpenImmersion g] (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f))
    (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B) (hΦ : Φ.left ≫ pullback.fst B.hom t = f) :
    LBIso ((L.pull (pullback.fst A.hom t)).pull (((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange).ι)
      (((M.pull (pullback.fst B.hom t)).pull Φ.left).pull
        (((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange).ι) := by
  obtain ⟨A', B', _, _, φA, φB, Φ', hA, hB, -, hI, e, e1, e2, e3⟩ := h
  set U := ((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange with hU
  have hr : Set.range ⇑(U.ι ≫ pullback.snd A.hom t) ⊆ Set.range ⇑g := by
    rintro _ ⟨x, rfl⟩
    have hx : U.ι x ∈ (U : Set _) := Scheme.Opens.range_ι U ▸ ⟨x, rfl⟩
    exact Scheme.Hom.mem_opensRange.1 hx
  have hl : IsOpenImmersion.lift g _ hr ≫ g = U.ι ≫ pullback.snd A.hom t := IsOpenImmersion.lift_fac _ _ _
  have wl : (U.ι ≫ pullback.fst A.hom t) ≫ A.hom = IsOpenImmersion.lift g _ hr ≫ g ≫ t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ t) hl.symm).trans (Category.assoc _ _ _)
  have he' : pullback.lift _ _ wl ≫ pmap A t g = U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hl]
  have he : hA.1.isoPullback.inv ≫ e = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, e1, IsPullback.isoPullback_inv_fst, Category.id_comp]
    · rw [Category.assoc, e2, IsPullback.isoPullback_inv_snd, Category.id_comp]
  obtain ⟨E, hE⟩ : ∃ E, E ≫ e = pullback.lift _ _ wl :=
    ⟨pullback.lift _ _ wl ≫ hA.1.isoPullback.inv, by rw [Category.assoc, he, Category.comp_id]⟩
  have h2 : LBIso (L.pull (U.ι ≫ pullback.fst A.hom t)) ((M.pull (pullback.fst B.hom t)).pull (U.ι ≫ Φ.left)) := by
    refine lbIso_pull hL hM E ?_ ?_ hI
    · rw [← e1, ← Category.assoc, hE, pullback.lift_fst]
    · rw [Category.assoc, hΦ, ← e3, ← Category.assoc, hE, ← Category.assoc, he']
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
    (lbIso_pull_pull hL _ _) (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _)
      (pull_isLB (pull_isLB (pull_isLB hM _) _) _) h2 (lbIso_pull_pull (pull_isLB hM _) _ _).symm)

theorem glue_wit : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → ∀ (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left), (∀ i, HomGlue.Wit A B L M (𝒰.f i ≫ t) (HomGlue.pmap A t (𝒰.f i) ≫ f)) → HomGlue.Wit A B L M t f := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB Z 𝒰 t f hw
  have w : f ≫ B.hom = pullback.snd A.hom t ≫ t :=
    pmap_hom_ext A 𝒰 t fun i => wit_w (𝒰.f i) (hw i)
  let Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B :=
    Over.homMk (pullback.lift f (pullback.snd A.hom t) w) (pullback.lift_snd _ _ _)
  have hΦf : Φ.left ≫ pullback.fst B.hom t = f := pullback.lift_fst _ _ _
  have hΦ : IsMonHom Φ := isMonHom_of_cover 𝒰 Φ fun i => isMonHom_pull_of_wit (𝒰.f i) (hw i) Φ hΦf
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj t B hB
  haveI : IsCommMonObj ((Over.pullback t).obj A) := hA'.comm
  haveI : IsCommMonObj ((Over.pullback t).obj B) := hB'.comm
  have hI : LBIso (L.pull (pullback.fst A.hom t)) ((M.pull (pullback.fst B.hom t)).pull Φ.left) :=
    hiso Z _ _ _ _ Φ hΦ hA' hB' (pull_isLB hL _) (pull_isLB hM _)
      (GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback A t) hrA)
      (GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback B t) hrB)
      fun z => ⟨(𝒰.f (𝒰.idx z)).opensRange, Scheme.Hom.mem_opensRange.2 (𝒰.covers z),
        local_iso hL hM (𝒰.f (𝒰.idx z)) (hw _) Φ hΦf⟩
  exact ⟨_, _, inferInstance, inferInstance, _, _, Φ, isGrpPullback_pullback A t, isGrpPullback_pullback B t, hΦ,
    hI, 𝟙 _, Category.id_comp _, Category.id_comp _, (Category.id_comp _).trans hΦf.symm⟩

end GlobalTheory.EndLoc.HomGlue
