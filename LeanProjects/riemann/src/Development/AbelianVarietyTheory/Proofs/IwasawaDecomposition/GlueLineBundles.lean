import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GlueLineBundle

variable {X W : Scheme.{0}}

def imU (j : W ⟶ X) [IsOpenImmersion j] (V : W.Opens) : Γ(W, V)ˣ →* Γ(X, j ''ᵁ V)ˣ :=
  Units.map (j.appIso V).inv.hom

theorem res_pull_imU (j : W ⟶ X) [IsOpenImmersion j] (V : W.Opens) (v : Γ(W, V)ˣ) :
    res (j.preimage_image_eq V).ge (pullU j _ (imU j V v)) = v := by
  apply Units.ext
  have h := congrArg (fun q => q.hom v.val) (j.appIso_inv_appLE (U := V) (V := V) (j.preimage_image_eq V).ge)
  have e : (homOfLE (le_refl V)) = 𝟙 V := rfl
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  refine h.trans ?_
  show (W.presheaf.map (𝟙 (Opposite.op V))).hom v.val = v.val
  rw [W.presheaf.map_id]; rfl

theorem gm_imU (j : W ⟶ X) [IsOpenImmersion j] {Y : Scheme.{0}} (f : Y ⟶ W) (y : Y) (V : W.Opens)
    (hy : f y ∈ V) (v : Γ(W, V)ˣ) : gm (f ≫ j) y (j ''ᵁ V) (imU j V v) = gm f y V v := by
  have h1 : j (f y) ∈ j ''ᵁ V := j.apply_mem_image_iff.2 hy
  rw [← gm_pull f j y _ h1, ← gm_res f y (j.preimage_image_eq V).ge hy, res_pull_imU]

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}}

theorem gm_id_val {O : X.Opens} {x : X} (hx : x ∈ O) (a : Γ(X, O)ˣ) :
    (gm (𝟙 X) x O a).val = X.presheaf.germ O x hx a.val := by
  rw [gm_val _ x O hx]; rfl

theorem unit_ext_imm {O : X.Opens} {a b : Γ(X, O)ˣ}
    (h : ∀ x ∈ O, ∃ (W : Scheme.{0}) (j : W ⟶ X) (_ : IsOpenImmersion j) (w : W), j w = x ∧
      gm j w O a = gm j w O b) : a = b := by
  apply unit_ext
  intro x hx
  obtain ⟨W, j, hj, w, rfl, e⟩ := h x hx
  apply Units.ext
  rw [gm_id_val hx, gm_id_val hx]
  have e' := congrArg Units.val e
  rw [gm_val j w O hx, gm_val j w O hx, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  exact (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.injective e'

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)

abbrev NU (p : Σ a, (M a).ι) : X.Opens := (V p.1).ι ''ᵁ (M p.1).U p.2

def GSpec (p q : Σ a, (M a).ι) (u : Γ(X, NU V M p ⊓ NU V M q)ˣ) : Prop :=
  ∀ (c : A) (Y : Scheme.{0}) (f : Y ⟶ (V c).toScheme) (y : Y) (j l : (M c).ι),
    (⟨c, j⟩ : Σ a, (M a).ι) = p → (⟨c, l⟩ : Σ a, (M a).ι) = q → f y ∈ (M c).U j → f y ∈ (M c).U l →
    gm (f ≫ (V c).ι) y (NU V M p ⊓ NU V M q) u = gm f y ((M c).U j ⊓ (M c).U l) ((M c).g j l)

theorem mem_of_mem_NU {p : Σ a, (M a).ι} {x : X} (hx : x ∈ NU V M p) : x ∈ V p.1 :=
  Scheme.Opens.ι_image_le _ _ hx

theorem exists_gSpec (p q : Σ a, (M a).ι) : ∃ u, GSpec V M p q u := by
  obtain ⟨a, i⟩ := p
  obtain ⟨b, k⟩ := q
  by_cases hab : a = b
  · subst hab
    have hle : (V a).ι ''ᵁ (M a).U i ⊓ (V a).ι ''ᵁ (M a).U k ≤ (V a).ι ''ᵁ ((M a).U i ⊓ (M a).U k) :=
      fun x hx => by
        obtain ⟨w, hw, rfl⟩ := hx.1
        exact (V a).ι.apply_mem_image_iff.2 ⟨hw, (V a).ι.apply_mem_image_iff.1 hx.2⟩
    refine ⟨res hle (imU (V a).ι _ ((M a).g i k)), ?_⟩
    intro c Y f y j l h1 h2 hj hl
    obtain ⟨rfl, h1'⟩ := Sigma.mk.inj_iff.1 h1
    obtain rfl := eq_of_heq h1'
    obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
    have hm : (f ≫ (V c).ι) y ∈ (V c).ι ''ᵁ (M c).U j ⊓ (V c).ι ''ᵁ (M c).U l :=
      ⟨(V c).ι.apply_mem_image_iff.2 hj, (V c).ι.apply_mem_image_iff.2 hl⟩
    exact (gm_res (f ≫ (V c).ι) y hle hm _).trans (gm_imU (V c).ι f y ((M c).U j ⊓ (M c).U l) ⟨hj, hl⟩ _)
  · refine ⟨1, ?_⟩
    intro c Y f y j l h1 h2
    exact absurd ((Sigma.mk.inj_iff.1 h1).1.symm.trans (Sigma.mk.inj_iff.1 h2).1) hab

def glue : LB X where
  ι := Σ a, (M a).ι
  U := NU V M
  g p q := Classical.choose (exists_gSpec V M p q)

theorem gm_glue_g (a : A) {Y : Scheme.{0}} (f : Y ⟶ (V a).toScheme) (y : Y) (i k : (M a).ι)
    (hi : f y ∈ (M a).U i) (hk : f y ∈ (M a).U k) :
    gm (f ≫ (V a).ι) y _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) :=
  Classical.choose_spec (exists_gSpec V M ⟨a, i⟩ ⟨a, k⟩) a Y f y i k rfl rfl hi hk

theorem gm_glue_g' (a : A) (w : (V a).toScheme) (i k : (M a).ι)
    (hi : w ∈ (M a).U i) (hk : w ∈ (M a).U k) :
    gm (V a).ι w _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm (𝟙 _) w ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by
  have := gm_glue_g V M a (𝟙 _) w i k hi hk
  rwa [Category.id_comp] at this

variable {V M}

theorem eq_of_mem (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) {a b : A} (w : (V a).toScheme) {k : (M b).ι}
    (h : (V a).ι w ∈ NU V M ⟨b, k⟩) : a = b :=
  hdisj a b _ w.2 (mem_of_mem_NU V M h)

theorem glue_isLB (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hcov : ∀ x, ∃ a, x ∈ V a)
    (hM : ∀ a, (M a).IsLB) : (glue V M).IsLB where
  cover := top_le_iff.1 fun x _ => by
    obtain ⟨a, ha⟩ := hcov x
    obtain ⟨w, rfl⟩ : ∃ w : (V a).toScheme, (V a).ι w = x := ⟨⟨x, ha⟩, rfl⟩
    obtain ⟨i, hi⟩ := exists_chart (hM a) w
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, i⟩, (V a).ι.apply_mem_image_iff.2 hi⟩
  g_self p := by
    obtain ⟨a, i⟩ := p
    apply unit_ext_imm
    intro x hx
    have hx2 : x ∈ (V a).ι ''ᵁ (M a).U i := hx
    obtain ⟨w, hw, rfl⟩ := hx2
    have hx' : (V a).ι w ∈ (glue V M).U ⟨a, i⟩ := hx
    refine ⟨_, (V a).ι, inferInstance, w, rfl, ?_⟩
    rw [gm_res (V a).ι w _ hx', map_one, gm_glue_g' V M a w i i hw hw]
    exact gm_self (hM a) (𝟙 _) w hw
  cocycle p q r := by
    obtain ⟨a, i⟩ := p
    obtain ⟨b, k⟩ := q
    obtain ⟨c, l⟩ := r
    apply unit_ext_imm
    intro x hx
    have h1 : x ∈ (V a).ι ''ᵁ (M a).U i := hx.1.1
    obtain ⟨w, hw, rfl⟩ := h1
    have h2 : (V a).ι w ∈ NU V M ⟨b, k⟩ := hx.1.2
    have h3 : (V a).ι w ∈ NU V M ⟨c, l⟩ := hx.2
    have hb := eq_of_mem hdisj w h2
    have hc := eq_of_mem hdisj w h3
    subst hb hc
    have hx' : (V a).ι w ∈ (glue V M).U ⟨a, i⟩ ⊓ (glue V M).U ⟨a, k⟩ ⊓ (glue V M).U ⟨a, l⟩ := hx
    have hk := (V a).ι.apply_mem_image_iff.1 h2
    have hl := (V a).ι.apply_mem_image_iff.1 h3
    refine ⟨_, (V a).ι, inferInstance, w, rfl, ?_⟩
    rw [map_mul, gm_res (V a).ι w _ hx', gm_res (V a).ι w _ hx', gm_res (V a).ι w _ hx', gm_glue_g' V M a w i k hw hk,
      gm_glue_g' V M a w k l hk hl, gm_glue_g' V M a w i l hw hl]
    exact gm_cocycle (hM a) (𝟙 _) w hw hk hl

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} {V : A → X.Opens} {M : ∀ a, LB (V a).toScheme}

theorem exists_isoUnit (a : A) (J : PUnit → (glue V M).ι) (k : (M a).ι) :
    ∃ u : Γ((V a).toScheme, ((glue V M).pull (V a).ι).U J ⊓ (M a).U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ (V a).toScheme) (y : Y) (i : (M a).ι),
        J PUnit.unit = (⟨a, i⟩ : Σ a, (M a).ι) → f y ∈ (M a).U i → f y ∈ (M a).U k →
        gm f y _ u = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by
  by_cases h : ∃ i' : (M a).ι, J PUnit.unit = (⟨a, i'⟩ : Σ a, (M a).ι)
  · obtain ⟨i', hi'⟩ := h
    have hle : ((glue V M).pull (V a).ι).U J ⊓ (M a).U k ≤ (M a).U i' ⊓ (M a).U k := fun w hw => by
      have h1 : (V a).ι w ∈ (glue V M).U (J PUnit.unit) := mem_pull.1 hw.1
      rw [hi'] at h1
      exact ⟨(V a).ι.apply_mem_image_iff.1 h1, hw.2⟩
    refine ⟨res hle ((M a).g i' k), fun Y f y i hJ hi hk => ?_⟩
    obtain rfl := sigma_mk_injective (hi'.symm.trans hJ)
    have hm : f y ∈ ((glue V M).pull (V a).ι).U J ⊓ (M a).U k := by
      refine ⟨mem_pull.2 ?_, hk⟩
      show (V a).ι (f y) ∈ (glue V M).U (J PUnit.unit)
      rw [hi']
      exact (V a).ι.apply_mem_image_iff.2 hi
    exact gm_res f y hle hm _
  · exact ⟨1, fun Y f y i hJ => absurd ⟨i, hJ⟩ h⟩

def isoGen (a : A) : LB.Iso (M a) ((glue V M).pull (V a).ι) :=
  ⟨fun p => Classical.choose (exists_isoUnit a p.1 p.2)⟩

theorem pgen_isoGen (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hM : ∀ a, (M a).IsLB) (a : A) :
    PGen (isoGen (V := V) (M := M) a) := by
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨b, i⟩ := j
  obtain ⟨b', i'⟩ := j'
  have hb : a = b := eq_of_mem hdisj (f y) hj
  have hb' : a = b' := eq_of_mem hdisj (f y) hj'
  subst hb hb'
  have hi : f y ∈ (M a).U i := (V a).ι.apply_mem_image_iff.1 hj
  have hi' : f y ∈ (M a).U i' := (V a).ι.apply_mem_image_iff.1 hj'
  have e1 : gw (isoGen a) f y ⟨a, i⟩ k = gm f y _ ((M a).g i k) :=
    Classical.choose_spec (exists_isoUnit (V := V) (M := M) a (fun _ => ⟨a, i⟩) k) Y f y i rfl hi hk
  have e2 : gw (isoGen a) f y ⟨a, i'⟩ k' = gm f y _ ((M a).g i' k') :=
    Classical.choose_spec (exists_isoUnit (V := V) (M := M) a (fun _ => ⟨a, i'⟩) k') Y f y i' rfl hi' hk'
  rw [e1, e2, gm_glue_g V M a f y i i' hi hi', mul_right_comm, gm_cocycle (hM a) f y hi hi' hk',
    ← gm_cocycle (hM a) f y hi hk hk', mul_inv_cancel_right]

end GlobalTheory.GlueLineBundle

open GlobalTheory.GlueLineBundle in

theorem GlobalTheory.glue_lineBundles : ∀ (X : Scheme.{0}) (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) → (∀ x, ∃ a, x ∈ V a) → ∀ (M : ∀ a, LB (V a).toScheme), (∀ a, (M a).IsLB) → ∃ N : LB X, N.IsLB ∧ ∀ a, LBIso (N.pull (V a).ι) (M a) := by
  intro X A V hdisj hcov M hM
  exact ⟨glue V M, glue_isLB hdisj hcov hM, fun a =>
    LBIso.symm ⟨isoGen a, (isGen_iff _).2 (pgen_isoGen hdisj hM a)⟩⟩
