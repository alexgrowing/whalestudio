import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelDominatedOfMapToBaseModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransitionMapRaisedModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDescentCoefficientField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelBaseChangeOverring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Models GlobalTheory.Models.Domination

namespace GlobalTheory.GlobalAllLevels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem dominates_of_above {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (b : O →+* O')
    {U₀ : Scheme.{0}} {F₀ O₀ : Type} [Field F₀] [CommRing O₀] {c₀ : U₀ ⟶ Sp F₀} {t₀ : SAB H U₀} {β₀ : O₀ →+* F₀}
    (C₀ : Cpt c₀ t₀ β₀) {b₀ : O₀ →+* O'} {r : Xo.XF c ⟶ U₀} {ν₀ : SABMap Y'.oF.t t₀ r}
    (a₀ : (ofModel Y').Above C₀ b₀ r ν₀) (ν' : SABMap Y.oF.t Y'.oF.t (𝟙 _))
    (hν' : ν'.φ ≫ Y'.m0.toSABMap.φ = Y.m0.toSABMap.φ)
    (f : pullback Y.s (spMap b) ⟶ C₀.X) (t : SAB H (pullback Y.s (spMap b)))
    (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t C₀.t f) (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    (hb : β'.comp b = β)
    (hf : ∀ g : Xo.XF c ⟶ pullback Y.s (spMap b), g ≫ pullback.fst _ _ = Y.j → g ≫ f = r ≫ C₀.j)
    (hφ : ∀ y : Y.oF.t.G.left ⟶ t.G.left, y ≫ m₁.φ = Y.m.φ → y ≫ m₂.φ = ν'.φ ≫ ν₀.φ ≫ C₀.m.φ) :
    Dominates Y Y' b := by
  have hrB : r ≫ C₀.j ≫ C₀.s = pullback.snd _ _ ≫ spMap (β'.comp b₀) := by
    rw [← Category.assoc, ← a₀.j_comm, Category.assoc, a₀.π_over, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc,
      ← spMap_comp]
  obtain ⟨ido, hid⟩ := ObjMaps.exists_sab_id Y.oF.t
  obtain ⟨C, a, hiso⟩ := GlobalTheory.Models.Cpt.exists_above_isIso_of_overring E H _ c.F O _ Y.oF.t β O' β' b (ofModel Y) ido hid
    hβ hβ' hb
  obtain ⟨e, π, mu, _, e₁, e₂, hj, hm⟩ : ∃ (e : C.X ⟶ pullback Y.s (spMap b)) (π : C.X ⟶ Y.X) (mu : SABMap C.t Y.t π),
      IsIso e ∧ e ≫ pullback.fst _ _ = π ∧ e ≫ pullback.snd _ _ = C.s ∧ C.j ≫ π = Y.j ∧ C.m.φ ≫ mu.φ = Y.m.φ :=
    ⟨pullback.lift a.π C.s a.π_over, a.π, a.mu, hiso, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      a.j_comm.trans (Category.id_comp _), a.φ_comm.trans (by rw [hid]; exact Category.id_comp _)⟩
  have hje : ∀ (S : Scheme.{0}) (u : S ⟶ pullback Y.s (spMap b)) (x : S ⟶ Xo.XF c),
      u ≫ pullback.fst _ _ = x ≫ Y.j → u = x ≫ C.j ≫ e := fun S u x h => by
    apply pullback.hom_ext
    · rw [h, Category.assoc, Category.assoc, e₁, hj]
    · rw [Category.assoc, Category.assoc, e₂, Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc]
      apply eq_of_overring hβ hβ' hb
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, h, Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) (Cpt.openImmersion_comp_structure_eq_generic (ofModel Y))
  have hjf : C.j ≫ e ≫ f = r ≫ C₀.j := by
    rw [← Category.assoc]
    exact hf _ (by rw [Category.assoc, e₁, hj])
  obtain ⟨κ, hκ⟩ := LevelCover.sab_cancel m₁ mu e e₁
  obtain ⟨κ₂, hκ₂⟩ := LevelCover.sab_comp κ m₂ rfl
  have hm₁ : (C.m.φ ≫ κ.φ) ≫ m₁.φ = Y.m.φ := by
    rw [Category.assoc, hκ, hm]
  have hover : (e ≫ f) ≫ C₀.s = C.s ≫ spMap ((RingHom.id O').comp b₀) := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ'
    letI := β'.toAlgebra
    obtain ⟨-, -, -, -, -, h3, -⟩ :=
      GlobalTheory.genericPart_dense_proOpen O' c.F C.X _ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
    have : IsDominant C.j := h3
    have : IsReduced C.X := by
      have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
        have := (C.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk _
    apply ext_of_isDominant C.j
    rw [← Category.assoc, hjf, Category.assoc, hrB, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]
  obtain ⟨h₀, κ₀, hh₀, -, -, hjh₀, hmh₀, -⟩ := Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C₀
    (ofModel Y') C b₀ (RingHom.id O') (RingHom.id c.F) r ν₀ a₀ (𝟙 _) ν' (e ≫ f) κ₂ hover hβ' rfl
    (by rw [LevelCover.spMap_id', Category.id_comp, Category.comp_id]) (by rw [hjf, Category.id_comp])
    (by rw [hκ₂, ← Category.assoc, hφ _ hm₁])
  obtain ⟨h, κ', hh, hjh, hmh⟩ : ∃ (h : C.X ⟶ Y'.X) (κ' : SABMap C.t Y'.t h), h ≫ Y'.s = C.s ∧ C.j ≫ h = Y'.j ∧
      C.m.φ ≫ κ'.φ = ν'.φ ≫ Y'.m.φ :=
    ⟨h₀, κ₀, hh₀.trans (by rw [LevelCover.spMap_id', Category.comp_id]), hjh₀.trans (Category.id_comp _), hmh₀⟩
  obtain ⟨idt, hid'⟩ := ObjMaps.exists_sab_id t
  obtain ⟨κi, hκi⟩ := LevelCover.sab_cancel κ idt (inv e) (IsIso.inv_hom_id e)
  obtain ⟨m₃, hm₃⟩ := LevelCover.sab_comp κi κ' rfl
  have hκκ : κ.φ ≫ κi.φ = 𝟙 _ := by
    apply κ.cart.1.hom_ext
    · change (κ.φ ≫ κi.φ) ≫ κ.φ = 𝟙 _ ≫ κ.φ
      rw [Category.assoc, hκi, hid', Category.comp_id, Category.id_comp]
    · have w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e := κ.cart.1.w
      have w₂ : κi.φ ≫ C.t.G.hom = t.G.hom ≫ inv e := κi.cart.1.w
      rw [Category.assoc, w₂, ← Category.assoc, w₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        Category.id_comp]
  refine ⟨inv e ≫ h, t, m₁, m₃, ?_, fun u hu => ?_, fun S g g₁ g₂ q₁ q₂ q₃ => ?_⟩
  · rw [Category.assoc, hh, ← e₂, IsIso.inv_hom_id_assoc]
  · rw [hje _ u (𝟙 _) (by rw [hu, Category.id_comp]), Category.id_comp, Category.assoc, IsIso.hom_inv_id_assoc, hjh]
  · have w₀ : ν'.φ ≫ Y'.oF.t.G.hom = Y.oF.t.G.hom := ν'.cart.1.w.trans (Category.comp_id _)
    have s₂ : g₂ = g₁ ≫ ν'.φ := by
      apply Y'.m0.toSABMap.cart.1.hom_ext
      · change g₂ ≫ Y'.m0.toSABMap.φ = (g₁ ≫ ν'.φ) ≫ Y'.m0.toSABMap.φ
        rw [Category.assoc, hν', q₂]
      · rw [Category.assoc, w₀, q₃]
    have s₁ : g = g₁ ≫ C.m.φ ≫ κ.φ := by
      apply m₁.cart.1.hom_ext
      · change g ≫ m₁.φ = (g₁ ≫ C.m.φ ≫ κ.φ) ≫ m₁.φ
        rw [Category.assoc, hm₁, q₁]
      · have w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e := κ.cart.1.w
        have w₂ : C.m.φ ≫ C.t.G.hom = Y.oF.t.G.hom ≫ C.j := C.m.cart.1.w
        have w₃ : m₁.φ ≫ Y.t.G.hom = t.G.hom ≫ pullback.fst _ _ := m₁.cart.1.w
        have w₄ : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := Y.m.cart.1.w
        rw [hje S (g ≫ t.G.hom) (g₁ ≫ Y.oF.t.G.hom) (by
          rw [Category.assoc, ← w₃, ← Category.assoc, q₁, Category.assoc, w₄, Category.assoc])]
        simp only [Category.assoc]
        rw [w₁, reassoc_of% w₂]
    rw [s₁, s₂, hm₃]
    simp only [Category.assoc]
    rw [reassoc_of% hκκ, hmh]

section Up

variable {l₁ l : Level H} {Xo₁ : Moduli D l₁} {Xo : Moduli D l} {c₁ : Coeff l₁} {c : Coeff l}

theorem sabMap_w {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    m.φ ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w

theorem above_of_isTransition {V₁ V : Type} [CommRing V₁] [CommRing V] {β₁ : V₁ →+* c₁.F} {β : V →+* c.F}
    {Y₁ : Model Xo₁ c₁ β₁} {Y : Model Xo c β} {e : V₁ →+* V} {π : Y.X ⟶ Y₁.X} (h : IsTransition Y₁ Y e π) :
    ∃ (r : Xo.XF c ⟶ Xo₁.XF c₁) (ν : SABMap Y.oF.t Y₁.oF.t r), LevComp Y.oF Y₁.oF r ν ∧
      Nonempty ((ofModel Y).Above (ofModel Y₁) e r ν) := by
  obtain ⟨π', mu, r, h₁, h₂, hfin, hj, hη, hηA⟩ := h
  obtain ⟨n, hn⟩ := LevelCover.sab_comp Y.m mu rfl
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel Y₁.m n r hj.symm
  have hπ : π ≫ Y₁.s = Y.s ≫ spMap e := by
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
  have hπ' : pullback.lift π Y.s hπ = π' := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, h₁]
    · rw [pullback.lift_snd, h₂]
  refine ⟨r, ν, ⟨fun a => LevelCover.sec_cancel ν Y₁.m _ _ ?_, fun a => LevelCover.sec_cancel ν Y₁.m _ _ ?_⟩,
    ⟨⟨π, hπ, hπ'.symm ▸ hfin, mu, hj, hn.symm.trans hν.symm⟩⟩⟩
  · rw [hν, hn]; exact hη a
  · rw [hν, hn]; exact hηA a

theorem dominates_up {O₁ O V₁ V : Type} [CommRing O₁] [CommRing O] [CommRing V₁] [CommRing V]
    {β₁ : O₁ →+* c₁.F} {β₁' : V₁ →+* c₁.F} {β : O →+* c.F} {β' : V →+* c.F}
    (Y₁ : Model Xo₁ c₁ β₁) (Y₁' : Model Xo₁ c₁ β₁') (Y : Model Xo c β) (Y' : Model Xo c β')
    (k : c₁.F →+* c.F) (b₀ : O₁ →+* O) (b₁ : O₁ →+* V₁) (b : O →+* V) (e : V₁ →+* V)
    (hβ₁ : IsDedFrac β₁) (hβ₁' : IsDedFrac β₁') (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    (hb₁ : β₁'.comp b₁ = β₁) (hb : β'.comp b = β) (he : β'.comp e = k.comp β₁') (hb₀ : β.comp b₀ = k.comp β₁)
    {r : Xo.XF c ⟶ Xo₁.XF c₁} {ν : SABMap Y.oF.t Y₁.oF.t r} (hr : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap k)
    (hl : LevComp Y.oF Y₁.oF r ν) (A : (ofModel Y).Above (ofModel Y₁) b₀ r ν) (hD : Dominates Y₁ Y₁' b₁)
    {π : Y'.X ⟶ Y₁'.X} (hT : IsTransition Y₁' Y' e π) : Dominates Y Y' b := by
  obtain ⟨L₁, L₂, L₃, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨r₀, ν₀, hl₀, ⟨a₀⟩⟩ := above_of_isTransition hT
  obtain ⟨f₁, t₁, p₁, p₂, -, hf₁, hφ₁⟩ := hD
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y'.m0.toSABMap Y.m0.toSABMap (𝟙 _) (Category.id_comp _)
  have η₁ : ∀ x, (Y.oF.eta x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.eta x).left := fun x =>
    LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by
      rw [hν', Category.id_comp]; exact (Y.m0.eta x).trans (Y'.m0.eta x).symm)
  have η₂ : ∀ x, (Y.oF.etaA x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.etaA x).left := fun x =>
    LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by
      rw [hν', Category.id_comp]; exact (Y.m0.etaA x).trans (Y'.m0.etaA x).symm)

  have hr₀ : r₀ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap k := by
    have := RaisedTransition.mono_spMap_of_isDedFrac hβ₁'
    obtain ⟨σ, q₁, q₂⟩ : ∃ σ : Y'.X ⟶ Y₁'.X, σ ≫ Y₁'.s = Y'.s ≫ spMap e ∧ Y'.j ≫ σ = r₀ ≫ Y₁'.j :=
      ⟨a₀.π, a₀.π_over, a₀.j_comm⟩
    have q₃ : Y₁'.j ≫ Y₁'.s = pullback.snd _ _ ≫ spMap β₁' := Cpt.openImmersion_comp_structure_eq_generic (ofModel Y₁')
    have q₄ : Y'.j ≫ Y'.s = pullback.snd _ _ ≫ spMap β' := Cpt.openImmersion_comp_structure_eq_generic (ofModel Y')
    rw [← cancel_mono (spMap β₁'), Category.assoc, ← q₃, ← Category.assoc, ← q₂, Category.assoc, q₁,
      ← Category.assoc, q₄, Category.assoc, Category.assoc, ← spMap_comp, ← spMap_comp, he]
  obtain ⟨νa, hνa⟩ := LevelCover.sab_comp ν Y₁.m0.toSABMap rfl
  obtain ⟨ν₁, hν₁⟩ := LevelCover.sab_comp ν' ν₀ (Category.id_comp r₀)
  obtain ⟨νb, hνb⟩ := LevelCover.sab_comp ν₁ Y₁'.m0.toSABMap rfl
  have hla : LevComp Y.oF Xo₁.univ _ νa := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hνa, ← Category.assoc, hl.1, Category.assoc, Category.assoc]
      exact congrArg _ (Y₁.m0.eta x)
    · rw [hνa, ← Category.assoc, hl.2, Category.assoc, Category.assoc]
      exact congrArg _ (Y₁.m0.etaA x)
  have hlb : LevComp Y.oF Xo₁.univ _ νb := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hνb, hν₁, ← Category.assoc, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₁ x), Category.id_comp, hl₀.1,
        Category.assoc, Category.assoc]
      exact congrArg _ (Y₁'.m0.eta x)
    · rw [hνb, hν₁, ← Category.assoc, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₂ x), Category.id_comp, hl₀.2,
        Category.assoc, Category.assoc]
      exact congrArg _ (Y₁'.m0.etaA x)
  have hred : IsReduced (Xo.XF c) := by
    have := Xo.smooth
    have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ (pullback.snd _ _)
      inferInstance).1
  obtain ⟨e₁, e₂⟩ := GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H D l₁ l Xo₁ _ _ _ _ Y.oF _ _ νa νb hred
    (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hr, reassoc_of% hr₀]) hla hlb
  obtain rfl : r = r₀ := pullback.hom_ext e₁ (hr.trans hr₀.symm)

  have hinj : Function.Injective β' := by
    letI := β'.toAlgebra
    have := hβ'.2.2
    exact IsFractionRing.injective V c.F
  have hbb : e.comp b₁ = b.comp b₀ := RingHom.ext fun x => hinj (by
    change (β'.comp e) (b₁ x) = (β'.comp b) (b₀ x)
    rw [he, hb]
    change k ((β₁'.comp b₁) x) = (β.comp b₀) x
    rw [hb₁, hb₀]
    rfl)
  obtain ⟨ρ, mu, hρ, hρj, hρφ⟩ : ∃ (ρ : Y.X ⟶ Y₁.X) (mu : SABMap Y.t Y₁.t ρ), ρ ≫ Y₁.s = Y.s ≫ spMap b₀ ∧
      Y.j ≫ ρ = r ≫ Y₁.j ∧ Y.m.φ ≫ mu.φ = ν.φ ≫ Y₁.m.φ := ⟨A.π, A.mu, A.π_over, A.j_comm, A.φ_comm⟩
  have w₀ : (pullback.fst Y.s (spMap b) ≫ ρ) ≫ Y₁.s = (pullback.snd _ _ ≫ spMap e) ≫ spMap b₁ := by
    rw [Category.assoc, hρ, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      ← spMap_comp, ← spMap_comp, hbb]
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : pullback Y.s (spMap b) ⟶ pullback Y₁.s (spMap b₁),
      g₀ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ρ := ⟨_, pullback.lift_fst _ _ w₀⟩
  obtain ⟨τ, ⟨n₁⟩⟩ : ∃ τ, Nonempty (SABMap τ Y.t (pullback.fst Y.s (spMap b))) := by
    obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull (pullback.fst Y.s (spMap b)) Y.t
    exact ⟨_, ⟨n₁⟩⟩
  obtain ⟨k₁, hk₁⟩ := LevelCover.sab_comp n₁ mu rfl
  obtain ⟨k₂, hk₂⟩ := LevelCover.sab_cancel p₁ k₁ g₀ hg₀
  obtain ⟨n₂, hn₂⟩ := LevelCover.sab_comp k₂ p₂ rfl
  have hj₁ : Y₁.j ≫ Y₁.s = pullback.snd _ _ ≫ spMap β₁ := Cpt.openImmersion_comp_structure_eq_generic (ofModel Y₁)
  have w₁ : Y₁.j ≫ Y₁.s = (pullback.snd _ _ ≫ spMap β₁') ≫ spMap b₁ := by
    rw [hj₁, Category.assoc, ← spMap_comp, hb₁]
  refine dominates_of_above Y Y' b (ofModel Y₁') a₀ ν' hν' (g₀ ≫ f₁) _ n₁ n₂ hβ hβ' hb (fun g hg => ?_) fun y hy => ?_
  · have hg₁ : (g ≫ g₀) ≫ pullback.fst _ _ = r ≫ Y₁.j := by
      rw [Category.assoc, hg₀, ← Category.assoc, hg, hρj]
    have : g ≫ g₀ = r ≫ pullback.lift _ _ w₁ := by
      apply pullback.hom_ext
      · rw [hg₁, Category.assoc, pullback.lift_fst]
      · rw [Category.assoc r, pullback.lift_snd, ← Category.assoc r]
        apply eq_of_overring hβ₁ hβ₁' hb₁
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, hg₁, Category.assoc, Category.assoc, hj₁]
    change g ≫ g₀ ≫ f₁ = r ≫ Y₁'.j
    rw [← Category.assoc, this, Category.assoc, hf₁ _ (pullback.lift_fst _ _ _)]
  · have := hφ₁ _ (y ≫ k₂.φ) ν.φ ν₁.φ (by rw [Category.assoc, hk₂, hk₁, ← Category.assoc, hy, hρφ])
      (hνa.symm.trans (e₂.trans hνb)) ((sabMap_w ν).trans (sabMap_w ν₁).symm)
    change y ≫ n₂.φ = ν'.φ ≫ ν₀.φ ≫ Y₁'.m.φ
    rw [hn₂, ← Category.assoc, this, hν₁, Category.assoc]

theorem exists_model_above (Xo : ∀ l : Level H, Moduli D l) (hN : ToroidalLevelCompatibility (H := H) (D := D)) (hd : l₁.Dvd l)
    (hc : c₁.F ≤ c.F) {O₁ O : Type} [CommRing O₁] [CommRing O] {β₁ : O₁ →+* c₁.F} (β : O →+* c.F)
    (Y₁ : Model (Xo l₁) c₁ β₁) (b₀ : O₁ →+* O) (hβ₁ : IsDedFrac β₁) (hβ : IsDedFrac β)
    (hb₀ : β.comp b₀ = (IntermediateField.inclusion hc).toRingHom.comp β₁) :
    ∃ (Y : Model (Xo l) c β) (r : (Xo l).XF c ⟶ (Xo l₁).XF c₁) (ν : SABMap Y.oF.t Y₁.oF.t r),
      r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom ∧
      LevComp Y.oF Y₁.oF r ν ∧ Nonempty ((ofModel Y).Above (ofModel Y₁) b₀ r ν) := by
  obtain ⟨L₁, L₂, L₃, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨oF, ⟨m0⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) (Xo l).X ((Xo l).XF c)
    (Xo l).s (pullback.fst _ _ ≫ (Xo l).s) (pullback.fst _ _) rfl rfl
    (by rw [LevelCover.spMap_id', Category.comp_id]) (Xo l).univ
  obtain ⟨k, r, ν, hr, hk, hl, hf, -⟩ := GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN l₁ l c oF m0 hd
  have hkk : k = (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c₁.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (hk x)
  obtain ⟨r', hr₁, hr₂⟩ : ∃ r' : (Xo l).XF c ⟶ (Xo l₁).XF c₁, r' ≫ pullback.fst _ _ = r ∧
      r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom :=
    ⟨pullback.lift r (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom)
      (by rw [hr, hkk, spMap_comp, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y₁.m0.toSABMap ν r' hr₁
  have hl' : LevComp oF Y₁.oF r' ν' :=
    ⟨fun x => LevelCover.sec_cancel ν' Y₁.m0.toSABMap _ _ (by
        rw [hν', hl.1, ← hr₁, Category.assoc]; exact congrArg _ (Y₁.m0.eta x).symm),
      fun x => LevelCover.sec_cancel ν' Y₁.m0.toSABMap _ _ (by
        rw [hν', hl.2, ← hr₁, Category.assoc]; exact congrArg _ (Y₁.m0.etaA x).symm)⟩
  have hnormF : Geo.Tor.IsNormalScheme ((Xo l).XF c) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
      (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).2.1
  have hf' : IsFinite (pullback.lift r' _ hr₂) := by
    subst hkk
    let m : pullback (pullback.snd (Xo l₁).s (spMap (IntermediateField.inclusion c₁.le).toRingHom))
        (spMap (IntermediateField.inclusion hc).toRingHom) ⟶ pullback (Xo l₁).s
          (spMap ((IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c₁.le).toRingHom)) :=
      pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, spMap_comp, Category.assoc])
    have hm : IsIso m := by
      have h₁ := (IsPullback.of_hasPullback (pullback.snd (Xo l₁).s (spMap (IntermediateField.inclusion c₁.le).toRingHom))
        (spMap (IntermediateField.inclusion hc).toRingHom)).paste_horiz
        (IsPullback.of_hasPullback (Xo l₁).s (spMap (IntermediateField.inclusion c₁.le).toRingHom))
      rw [← spMap_comp] at h₁
      have : m = h₁.isoPullback.hom := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
        · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
      rw [this]
      infer_instance
    have hc' : pullback.lift r' _ hr₂ ≫ m = pullback.lift r _ hr := by
      apply pullback.hom_ext
      · simp only [m, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hr₁]
      · simp only [m, Category.assoc, pullback.lift_snd]
    rw [← hc'] at hf
    exact IsFinite.of_comp _ m
  obtain ⟨C, ⟨A⟩⟩ := GlobalTheory.Models.Cpt.exists_above E H _ _ _ _ _ β₁ ((Xo l).XF c) _ _ (pullback.snd _ _) oF.t β
    (ofModel Y₁) b₀ (IntermediateField.inclusion hc).toRingHom r' hr₂ ν' hβ₁ hβ hb₀ hnormF hf'
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, oF, m0, C.m, C.ab_gen⟩,
    r', ν', hr₂, hl', ⟨A⟩⟩

end Up

def firstPart (l : Level H) : Level H := { l with A := 1, A_pos := Nat.one_pos }

theorem firstPart_dvd (l : Level H) : (firstPart l).Dvd l := ⟨dvd_rfl, le_rfl, one_dvd _⟩

def coeffFirst {l : Level H} (c : Coeff l) : Coeff (firstPart l) where
  F := c.F
  fin := c.fin
  conj := c.conj
  le := (levelField_le_of_dvd (l := firstPart l) (l₂ := l) (one_dvd _)).trans c.le
  zeta_mem := by
    change zeta (Nat.lcm l.M 1) ∈ c.F
    rw [Nat.lcm_one_right]
    obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
    have hM : l.M' ≠ 0 := (Nat.lcm_pos hM0 l.A_pos).ne'
    have hk0 : (k : ℂ) ≠ 0 := by
      rintro h
      rw [Nat.cast_eq_zero.1 h] at hk
      exact hM hk
    have : zeta l.M = zeta l.M' ^ k := by
      rw [zeta, zeta, ← Complex.exp_nat_mul, hk, Nat.cast_mul]
      congr 1
      field_simp
    exact this ▸ pow_mem c.zeta_mem k

theorem exists_sys_global_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    1 ≤ Dw.p + Dw.q → ∀ Xo : ∀ l : Level H, Moduli Dw l, ∃ s : GlobalTheory.ShFam.Sys Xo,
      ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p),
        ∃ Ygl : Model (Xo l) c (algebraMap (𝓞 c.F) c.F), (l.A = 1 → Ygl.Descends) ∧
          ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W),
            (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → Dominates Ygl (s.Y p W hp hW ⟨l, c, hg p hp⟩) b := by
  intro E _ _ _ H D hD Xo
  obtain ⟨Y, hY, h6⟩ := GlobalTheory.partI_closed.2 E H D hD Xo
  refine ⟨⟨Y, hY⟩, fun l c hg => ?_⟩
  by_cases hA : l.A = 1
  · obtain ⟨Z, h₁, h₂⟩ := h6 l c hg hA
    exact ⟨Z, fun _ => h₁, h₂⟩
  obtain ⟨Z₁, -, hZ₁⟩ := h6 (firstPart l) (coeffFirst c) hg rfl
  obtain ⟨hdO, -, -, hV⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  obtain ⟨Z, r, ν, hr, hl, ⟨A⟩⟩ := exists_model_above (c₁ := coeffFirst c) (c := c) Xo
    (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H D hD).1 (firstPart_dvd l) le_rfl (algebraMap (𝓞 c.F) c.F) Z₁
    (RingHom.id _) hdO hdO rfl
  refine ⟨Z, fun h => (hA h).elim, fun p W hp hW b hb => ?_⟩
  obtain ⟨-, π, hπ, -⟩ := (hY p W hp hW).1
  have hdV := (hV p W hp hW).1
  exact dominates_up Z₁ (Y p W hp hW ⟨firstPart l, coeffFirst c, hg p hp⟩) Z _ _ (RingHom.id _) b b (RingHom.id _)
    hdO hdV hdO hdV (RingHom.ext hb) (RingHom.ext hb) rfl rfl hr hl A (hZ₁ p W hp hW b hb)
    (hπ ⟨firstPart l, coeffFirst c, hg p hp⟩ ⟨l, c, hg p hp⟩ (firstPart_dvd l) le_rfl (RingHom.id _) fun _ => rfl)

end GlobalTheory.GlobalAllLevels
