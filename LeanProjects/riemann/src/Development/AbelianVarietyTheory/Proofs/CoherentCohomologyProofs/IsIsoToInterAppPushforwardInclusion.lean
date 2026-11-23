import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapFOneInjectiveOfSectionsSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CohomologyPresheafFunctorMapAppApply

open CategoryTheory Limits Opposite TopologicalSpace

universe w u v' u'

noncomputable section

namespace GlobalTheory
namespace Kempf

variable {X : TopCat.{u}}

section Inter

def interFunctor (W : Opens X) : Opens X ⥤ Opens X where
  obj B := B ⊓ W
  map i := homOfLE (inf_le_inf_right W i.le)

@[simp] lemma interFunctor_obj (W B : Opens X) : (interFunctor W).obj B = B ⊓ W := rfl

def interFunctorIso (W : Opens X) :
    Opens.map W.inclusion' ⋙ W.isOpenEmbedding.functor ≅ interFunctor W :=
  NatIso.ofComponents (fun B ↦ eqToIso (Opens.functor_map_eq_inf W B))
    (fun _ ↦ Subsingleton.elim _ _)

instance isContinuous_interFunctor (W : Opens X) :
    (interFunctor W).IsContinuous (Opens.grothendieckTopology X) (Opens.grothendieckTopology X) :=
  haveI := W.isOpenEmbedding.functor_isContinuous
  Functor.isContinuous_of_iso (interFunctorIso W) _ _

variable (A : Type u') [Category.{v'} A]

def interSheaf (W : Opens X) : X.Sheaf A ⥤ X.Sheaf A :=
  (interFunctor W).sheafPushforwardContinuous A _ _

def toInter (W : Opens X) : 𝟭 (X.Sheaf A) ⟶ interSheaf A W where
  app F := ObjectProperty.homMk
    { app B := F.obj.map (homOfLE (inf_le_left : B.unop ⊓ W ≤ B.unop)).op
      naturality B B' i :=
        (F.obj.map_comp _ _).symm.trans (F.obj.map_comp
          (homOfLE (inf_le_left : B.unop ⊓ W ≤ B.unop)).op ((interFunctor W).op.map i)) }
  naturality F G f := by
    apply Sheaf.hom_ext
    ext B : 2
    exact (f.hom.naturality _).symm

variable {A}

@[simp] lemma interSheaf_obj_obj_obj (W : Opens X) (F : X.Sheaf A) (B : Opens X) :
    ((interSheaf A W).obj F).obj.obj (op B) = F.obj.obj (op (B ⊓ W)) := rfl

@[simp] lemma interSheaf_obj_obj_map (W : Opens X) (F : X.Sheaf A) {B B' : Opens X}
    (i : B' ⟶ B) : ((interSheaf A W).obj F).obj.map i.op =
      F.obj.map (homOfLE (inf_le_inf_right W i.le)).op := rfl

@[simp] lemma interSheaf_map_hom_app (W : Opens X) {F G : X.Sheaf A} (f : F ⟶ G) (B : Opens X) :
    ((interSheaf A W).map f).hom.app (op B) = f.hom.app (op (B ⊓ W)) := rfl

@[simp] lemma toInter_app_hom_app (W : Opens X) (F : X.Sheaf A) (B : Opens X) :
    ((toInter A W).app F).hom.app (op B) = F.obj.map (homOfLE inf_le_left).op := rfl

instance isFlasque_interSheaf (W : Opens X) (F : X.Sheaf A) [hF : F.IsFlasque] :
    ((interSheaf A W).obj F).IsFlasque where
  epi _ := hF.epi _

lemma isIso_toInter_app_of_isBasis {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅) (W : Opens X)
    (G : X.Sheaf A)
    (h : ∀ B ∈ 𝔅, IsIso (G.obj.map (homOfLE (inf_le_left : B ⊓ W ≤ B)).op)) :
    IsIso ((toInter A W).app G) :=
  TopCat.Sheaf.isIso_iff_isIso_basis (B := fun B : 𝔅 ↦ B.1) (by rwa [Subtype.range_coe])
    fun B ↦ h B.1 B.2

lemma isIso_toInter_app_pushforward {Y : TopCat.{u}} (j : Y ⟶ X) (W : Opens X)
    (hj : ∀ y, j y ∈ W) (G : Y.Sheaf A) :
    IsIso ((toInter A W).app ((TopCat.Sheaf.pushforward A j).obj G)) := by
  refine isIso_toInter_app_of_isBasis (𝔅 := Set.univ) ?_ W _ fun B _ ↦ ?_
  · exact Opens.isBasis_iff_nbhd.2 fun {U} _ hx ↦ ⟨U, trivial, hx, le_rfl⟩
  · have : IsIso ((Opens.map j).map (homOfLE (inf_le_left : B ⊓ W ≤ B))) :=
      ⟨homOfLE fun y hy ↦ ⟨hy, hj y⟩, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    exact inferInstanceAs (IsIso (G.obj.map
      ((Opens.map j).map (homOfLE (inf_le_left : B ⊓ W ≤ B))).op))

instance isIso_toInter_app_pushforward_inclusion' (W : Opens X)
    (G : ((Opens.toTopCat X).obj W).Sheaf A) :
    IsIso ((toInter A W).app ((TopCat.Sheaf.pushforward A W.inclusion').obj G)) :=
  isIso_toInter_app_pushforward W.inclusion' W (fun y ↦ y.2) G

lemma toInter_app_comp_map_comp_inv (W : Opens X) {F G : X.Sheaf A} (f : F ⟶ G)
    [IsIso ((toInter A W).app G)] :
    (toInter A W).app F ≫ (interSheaf A W).map f ≫ inv ((toInter A W).app G) = f := by
  rw [← (toInter A W).naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

end Inter

section Iso

variable (A : Type u') [Category.{u} A]

def interSheafIso (W : Opens X) :
    W.isOpenEmbedding.sheafPullback A ⋙ TopCat.Sheaf.pushforward A W.inclusion' ≅
      interSheaf A W :=
  haveI := W.isOpenEmbedding.functor_isContinuous
  Functor.sheafPushforwardContinuousComp' (interFunctorIso W) A _ _ _

def interSheafIsoPullback (W : Opens X) :
    TopCat.Sheaf.pullback AddCommGrpCat.{u} W.inclusion' ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} W.inclusion' ≅ interSheaf AddCommGrpCat.{u} W :=
  Functor.isoWhiskerRight (W.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}) _ ≪≫
    interSheafIso _ W

end Iso

section Abelian

instance (W : Opens X) : (interSheaf AddCommGrpCat.{u} W).Additive where

instance (W : Opens X) : (interSheaf AddCommGrpCat.{u} W).IsRightAdjoint :=
  inferInstanceAs ((interFunctor W).sheafPushforwardContinuous AddCommGrpCat.{u} _ _).IsRightAdjoint

variable {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}

lemma exact_map_interSheaf (hS : S.ShortExact) (W : Opens X) :
    (S.map (interSheaf AddCommGrpCat.{u} W)).Exact ∧
      Mono (S.map (interSheaf AddCommGrpCat.{u} W)).f :=
  ((Functor.preservesFiniteLimits_tfae (interSheaf AddCommGrpCat.{u} W)).out 1 3 rfl rfl).mpr
    inferInstance S ⟨hS.exact, hS.mono_f⟩

lemma shortExact_map_interSheaf (hS : S.ShortExact) {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅)
    (hinf : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ⊓ B' ∈ 𝔅)
    (hsurj : ∀ B ∈ 𝔅, Function.Surjective (S.g.hom.app (op B))) {W : Opens X} (hW : W ∈ 𝔅) :
    (S.map (interSheaf AddCommGrpCat.{u} W)).ShortExact := by
  refine ShortComplex.ShortExact.mk' (exact_map_interSheaf hS W).1 (exact_map_interSheaf hS W).2 ?_
  refine (TopCat.Sheaf.isLocallySurjective_iff_epi _).1
    ((TopCat.Presheaf.isLocallySurjective_iff _).2 fun U t x hx ↦ ?_)
  obtain ⟨B, hB, hxB, hBU⟩ := Opens.isBasis_iff_nbhd.1 h𝔅 hx
  exact ⟨B, hBU, hsurj (B ⊓ W) (hinf B hB W hW) _, hxB⟩

lemma exists_isBasis_lift (hS : S.ShortExact) {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅)
    {V : Opens X} (s : S.X₃.obj.obj (op V)) {x : X} (hx : x ∈ V) :
    ∃ W ∈ 𝔅, x ∈ W ∧ W ≤ V ∧ ∃ t : S.X₂.obj.obj (op (V ⊓ W)),
      S.g.hom.app (op (V ⊓ W)) t = S.X₃.obj.map (homOfLE inf_le_left).op s := by
  obtain ⟨U, hUV, ⟨t, ht⟩, hxU⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).1
    ((TopCat.Sheaf.isLocallySurjective_iff_epi S.g).2 hS.epi_g) V s x hx
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 h𝔅 hxU
  have hle : V ⊓ W ≤ U := inf_le_right.trans hWU
  refine ⟨W, hW, hxW, hWU.trans hUV, S.X₂.obj.map (homOfLE hle).op t, ?_⟩
  refine (ConcreteCategory.congr_hom (S.g.hom.naturality (homOfLE hle).op) t).trans ?_
  refine (congrArg (S.X₃.obj.map (homOfLE hle).op) ht).trans ?_
  exact (ConcreteCategory.congr_hom
    (S.X₃.obj.map_comp (homOfLE hUV).op (homOfLE hle).op) s).symm

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open SheafLES

lemma map_toInter_δ_eq_zero (hS : S.ShortExact) {V W : Opens X} (s : S.X₃.obj.obj (op V))
    (t : S.X₂.obj.obj (op (V ⊓ W)))
    (ht : S.g.hom.app (op (V ⊓ W)) t = S.X₃.obj.map (homOfLE inf_le_left).op s) :
    map.{w} ((toInter AddCommGrpCat.{u} W).app S.X₁) 1 V
      (δ hS 0 V ((equivZero S.X₃ V).symm s)) = 0 := by
  have := hS.epi_g
  let S' := S.map (interSheaf AddCommGrpCat.{u} W)
  have hS' : S'.Exact := (exact_map_interSheaf hS W).1
  have : Mono S'.f := (exact_map_interSheaf hS W).2
  let T : ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
    ShortComplex.mk S'.f (cokernel.π S'.f) (cokernel.condition _)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  let ι : T.X₃ ⟶ S'.X₃ := cokernel.desc S'.f S'.g S'.zero
  have hm : Mono ι := S'.exact_iff_mono_cokernel_desc.1 hS'
  have hι : T.g ≫ ι = S'.g := cokernel.π_desc _ _ _
  let η₁ : S.X₁ ⟶ T.X₁ := (toInter AddCommGrpCat.{u} W).app S.X₁
  let η₂ : S.X₂ ⟶ T.X₂ := (toInter AddCommGrpCat.{u} W).app S.X₂
  let η₃ : S.X₃ ⟶ S'.X₃ := (toInter AddCommGrpCat.{u} W).app S.X₃
  have h₁₂ : S.f ≫ η₂ = η₁ ≫ T.f := (toInter AddCommGrpCat.{u} W).naturality S.f
  have h₂₃ : S.g ≫ η₃ = η₂ ≫ S'.g := (toInter AddCommGrpCat.{u} W).naturality S.g
  have h0 : S.f ≫ η₂ ≫ T.g = 0 := by rw [reassoc_of% h₁₂, T.zero, comp_zero]
  let φ : S ⟶ T := ⟨η₁, η₂, hS.exact.desc (η₂ ≫ T.g) h0, h₁₂.symm, (hS.exact.g_desc _ h0).symm⟩
  have hφ : φ.τ₃ ≫ ι = η₃ := by
    rw [← cancel_epi S.g, ← φ.comm₂₃_assoc, hι, h₂₃]
  refine (δ_naturality hS hT φ 0 V _).trans ?_
  refine (exact₃ hT 0 V _).2 ⟨(equivZero T.X₂ V).symm t,
    @map_zero_injective_of_mono _ _ _ _ _ _ _ ι hm V _ _ ?_⟩
  refine (map_comp T.g ι 0 V _).symm.trans (Eq.trans ?_ (map_comp φ.τ₃ ι 0 V _))
  refine (congrArg (fun g ↦ map.{w} g 0 V ((equivZero T.X₂ V).symm t)) hι).trans
    (Eq.trans ?_ (congrArg (fun g ↦ map.{w} g 0 V ((equivZero S.X₃ V).symm s)) hφ).symm)
  refine (map_equivZero_symm S'.g V t).trans (Eq.trans ?_ (map_equivZero_symm η₃ V s).symm)
  exact congrArg _ ht

theorem exists_mem_map_toInter_eq_zero {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅)
    (hinf : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ⊓ B' ∈ 𝔅) (V : Opens X) (n : ℕ)
    (F : X.Sheaf AddCommGrpCat.{u})
    (hF : ∀ q, 0 < q → q < n + 1 → ∀ B ∈ 𝔅, Subsingleton (Sheaf.H'.{w} F q B))
    (α : Sheaf.H'.{w} F (n + 1) V) {x : X} (hx : x ∈ V) :
    ∃ W ∈ 𝔅, x ∈ W ∧ W ≤ V ∧
      map.{w} ((toInter AddCommGrpCat.{u} W).app F) (n + 1) V α = 0 := by
  induction n generalizing F with
  | zero =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    obtain ⟨β, rfl⟩ := δ_surjective_of_subsingleton.{w} hS 0 V
      (Flasque.subsingleton_H'_of_isFlasque _ 0 V) α
    obtain ⟨s, rfl⟩ := (equivZero _ V).symm.surjective β
    obtain ⟨W, hW, hxW, hWV, t, ht⟩ := exists_isBasis_lift hS h𝔅 s hx
    exact ⟨W, hW, hxW, hWV, map_toInter_δ_eq_zero hS s t ht⟩
  | succ n ih =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    obtain ⟨β, rfl⟩ := δ_surjective_of_subsingleton.{w} hS (n + 1) V
      (Flasque.subsingleton_H'_of_isFlasque _ (n + 1) V) α
    obtain ⟨W, hW, hxW, hWV, hβ⟩ := ih (Flasque.injectiveShortComplex F).X₃
      (fun q hq hqn B hB ↦ subsingleton₃.{w} hS q B
        (Flasque.subsingleton_H'_of_isFlasque_of_pos _ hq B)
        (hF (q + 1) q.succ_pos (by omega) B hB)) β
    have hT := shortExact_map_interSheaf hS h𝔅 hinf
      (fun B hB ↦ sections_surjective_of_subsingleton.{w} hS B (hF 1 one_pos (by omega) B hB)) hW
    refine ⟨W, hW, hxW, hWV, ?_⟩
    refine (δ_naturality hS hT
      ((Flasque.injectiveShortComplex F).mapNatTrans (toInter AddCommGrpCat.{u} W))
      (n + 1) V β).trans ?_
    exact (congrArg (δ hT (n + 1) V) hβ).trans (map_zero _)

lemma map_eq_zero_of_map_toInter_eq_zero {W : Opens X} {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) [IsIso ((toInter AddCommGrpCat.{u} W).app G)] {n : ℕ} {V : Opens X}
    {α : Sheaf.H'.{w} F n V} (h : map.{w} ((toInter AddCommGrpCat.{u} W).app F) n V α = 0) :
    map.{w} f n V α = 0 := by
  refine (congrArg (fun g ↦ map.{w} g n V α) (toInter_app_comp_map_comp_inv W f).symm).trans ?_
  refine (map_comp _ _ n V α).trans ?_
  exact (congrArg _ h).trans (map_zero _)

theorem exists_cover_map_toInter_eq_zero {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅)
    (hinf : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ⊓ B' ∈ 𝔅) (F : X.Sheaf AddCommGrpCat.{u}) (V : Opens X)
    {n : ℕ} (hn : 1 ≤ n)
    (hF : ∀ q, 0 < q → q < n → ∀ B ∈ 𝔅, Subsingleton (Sheaf.H'.{w} F q B))
    (α : Sheaf.H'.{w} F n V) :
    ∃ 𝔘 ⊆ 𝔅, sSup 𝔘 = V ∧
      ∀ W ∈ 𝔘, map.{w} ((toInter AddCommGrpCat.{u} W).app F) n V α = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  refine ⟨{W | W ∈ 𝔅 ∧ W ≤ V ∧ map.{w} ((toInter AddCommGrpCat.{u} W).app F) (n + 1) V α = 0},
    fun _ h ↦ h.1, le_antisymm (sSup_le fun _ h ↦ h.2.1) fun x hx ↦ ?_, fun _ h ↦ h.2.2⟩
  obtain ⟨W, hW, hxW, hWV, h⟩ := exists_mem_map_toInter_eq_zero h𝔅 hinf V n F hF α hx
  exact Opens.mem_sSup.2 ⟨W, ⟨hW, hWV, h⟩, hxW⟩

theorem exists_finite_cover_map_toInter_eq_zero {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅)
    (hinf : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ⊓ B' ∈ 𝔅) (F : X.Sheaf AddCommGrpCat.{u}) (V : Opens X)
    (hV : IsCompact (V : Set X)) {n : ℕ} (hn : 1 ≤ n)
    (hF : ∀ q, 0 < q → q < n → ∀ B ∈ 𝔅, Subsingleton (Sheaf.H'.{w} F q B))
    (α : Sheaf.H'.{w} F n V) :
    ∃ 𝔘 ⊆ 𝔅, 𝔘.Finite ∧ sSup 𝔘 = V ∧
      ∀ W ∈ 𝔘, map.{w} ((toInter AddCommGrpCat.{u} W).app F) n V α = 0 := by
  obtain ⟨𝔘, h𝔘, hsup, h0⟩ := exists_cover_map_toInter_eq_zero h𝔅 hinf F V hn hF α
  obtain ⟨𝔙, h𝔙, hfin, hcov⟩ := hV.elim_finite_subcover_image (b := 𝔘)
    (c := fun W : Opens X ↦ (W : Set X)) (fun W _ ↦ W.isOpen) fun x hx ↦ by
      obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.1 (hsup.ge hx)
      exact Set.mem_biUnion hW hxW
  refine ⟨𝔙, h𝔙.trans h𝔘, hfin, le_antisymm ((sSup_le_sSup h𝔙).trans hsup.le) fun x hx ↦ ?_,
    fun W hW ↦ h0 W (h𝔙 hW)⟩
  obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.1 (hcov hx)
  exact Opens.mem_sSup.2 ⟨W, hW, hxW⟩

end Abelian

end Kempf

end GlobalTheory
