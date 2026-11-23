import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyGtCoordOfIsGt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ExtUnique

variable {S : Scheme.{0}} {G G' B : Over S}

theorem exists_hom_of_rel (q : G ⟶ B) (q' : G' ⟶ B) [Flat q'.left] [Surjective q'.left] [QuasiCompact q'.left]
    (R : ∀ {Z : Over S}, (Z ⟶ G) → (Z ⟶ G') → Prop)
    (nat : ∀ {Z Z' : Over S} (h : Z' ⟶ Z) {g : Z ⟶ G} {g' : Z ⟶ G'}, R g g' → R (h ≫ g) (h ≫ g'))
    (base : ∀ {Z : Over S} {g : Z ⟶ G} {g' : Z ⟶ G'}, R g g' → g ≫ q = g' ≫ q')
    (uniq : ∀ {Z : Over S} {g : Z ⟶ G} {g₁ g₂ : Z ⟶ G'}, R g g₁ → R g g₂ → g₁ = g₂)
    (loc : ∀ {Z : Over S} (g : Z ⟶ G) (g' : Z ⟶ G'), g ≫ q = g' ≫ q' → ∃ g'', R g g'') :
    ∃ φ : G ⟶ G', R (𝟙 G) φ := by
  let P : Over S := Over.mk (pullback.fst q.left q'.left ≫ G.hom)
  let p₁ : P ⟶ G := Over.homMk (pullback.fst q.left q'.left) rfl
  let p₂ : P ⟶ G' := Over.homMk (pullback.snd q.left q'.left) (by
    change _ = pullback.fst q.left q'.left ≫ G.hom
    rw [← Over.w q, ← Over.w q', pullback.condition_assoc])
  obtain ⟨ψ, hψ⟩ := loc p₁ p₂ (Over.OverMorphism.ext pullback.condition)
  let p : P.left ⟶ G.left := pullback.fst q.left q'.left
  have : EffectiveEpi p := inferInstanceAs (EffectiveEpi (pullback.fst q.left q'.left))
  have hd : ∀ {T : Scheme.{0}} (a b : T ⟶ P.left), a ≫ p = b ≫ p → a ≫ ψ.left = b ≫ ψ.left := fun {T} a b e => by
    let a' : Over.mk (a ≫ P.hom) ⟶ P := Over.homMk a rfl
    let b' : Over.mk (a ≫ P.hom) ⟶ P := Over.homMk b (by
      change b ≫ p ≫ G.hom = a ≫ p ≫ G.hom
      rw [reassoc_of% e])
    have e' : a' ≫ p₁ = b' ≫ p₁ := Over.OverMorphism.ext e
    exact congrArg (·.left) (uniq (nat a' hψ) (e' ▸ nat b' hψ))
  have hf := EffectiveEpi.fac p ψ.left hd
  let φ : G ⟶ G' := Over.homMk (EffectiveEpi.desc p ψ.left hd) (by
    rw [← cancel_epi p, reassoc_of% hf]
    exact Over.w ψ)
  refine loc (𝟙 G) φ (Over.OverMorphism.ext ?_)
  rw [Category.id_comp, ← cancel_epi p]
  change p ≫ q.left = p ≫ EffectiveEpi.desc p ψ.left hd ≫ q'.left
  rw [reassoc_of% hf]
  exact congrArg (·.left) (base hψ)

section Frames

variable {κ : Type} (N : κ → LB B.left)

abbrev Frames (q : G ⟶ B) : Type := ∀ k j, Γ(G.left, q.left ⁻¹ᵁ (N k).U j)ˣ

variable {N} {q : G ⟶ B} {q' : G' ⟶ B}

def IsFrames (s : Frames N q) : Prop :=
  ∀ k (W : Scheme.{0}) (r : W ⟶ G.left) (w : W) j j', q.left (r w) ∈ (N k).U j → q.left (r w) ∈ (N k).U j' →
    gm r w _ (s k j') = gm (r ≫ q.left) w _ ((N k).g j j') * gm r w _ (s k j)

def Rel (s : Frames N q) (s' : Frames N q') {Z : Over S} (g : Z ⟶ G) (g' : Z ⟶ G') : Prop :=
  g ≫ q = g' ≫ q' ∧ ∀ k (W : Scheme.{0}) (r : W ⟶ Z.left) (w : W) j, (g ≫ q).left (r w) ∈ (N k).U j →
    gm (r ≫ g.left) w _ (s k j) = gm (r ≫ g'.left) w _ (s' k j)

variable {s : Frames N q} {s' : Frames N q'}

theorem Rel.symm {Z : Over S} {g : Z ⟶ G} {g' : Z ⟶ G'} (h : Rel s s' g g') : Rel s' s g' g :=
  ⟨h.1.symm, fun k W r w j hj => (h.2 k W r w j (h.1 ▸ hj)).symm⟩

theorem Rel.comp {Z Z' : Over S} (f : Z' ⟶ Z) {g : Z ⟶ G} {g' : Z ⟶ G'} (h : Rel s s' g g') :
    Rel s s' (f ≫ g) (f ≫ g') :=
  ⟨by rw [Category.assoc, h.1, Category.assoc], fun k W r w j hj => by
    have := h.2 k W (r ≫ f.left) w j hj
    rwa [Category.assoc, Category.assoc] at this⟩

theorem exists_ratio (hN : ∀ k, (N k).IsLB) (hs : IsFrames s) (hs' : IsFrames s') {Z : Over S} {g : Z ⟶ G}
    {g' : Z ⟶ G'} (e : g ≫ q = g' ≫ q') (k : κ) : ∃ ρ : Γ(Z.left, ⊤)ˣ, ∀ (W : Scheme.{0}) (r : W ⟶ Z.left) (w : W) j,
      (g ≫ q).left (r w) ∈ (N k).U j →
        gm (r ≫ g.left) w _ (s k j) = gm r w ⊤ ρ * gm (r ≫ g'.left) w _ (s' k j) := by
  have el : g.left ≫ q.left = g'.left ≫ q'.left := congrArg (·.left) e
  have m : ∀ {z : Z.left} {j}, (g ≫ q).left z ∈ (N k).U j → q'.left (g'.left z) ∈ (N k).U j := fun {z j} h =>
    (show (g' ≫ q').left z ∈ (N k).U j from e ▸ h)
  let O : (N k).ι → Z.left.Opens := fun j => g.left ⁻¹ᵁ (q.left ⁻¹ᵁ (N k).U j)
  have le : ∀ j, O j ≤ g'.left ⁻¹ᵁ (q'.left ⁻¹ᵁ (N k).U j) := fun j z hz => m hz
  let u : ∀ j, Γ(Z.left, O j)ˣ := fun j => pullU g.left _ (s k j) * (res (le j) (pullU g'.left _ (s' k j)))⁻¹
  have hu : ∀ (W : Scheme.{0}) (r : W ⟶ Z.left) (w : W) j, r w ∈ O j →
      gm r w _ (u j) = gm (r ≫ g.left) w _ (s k j) * (gm (r ≫ g'.left) w _ (s' k j))⁻¹ := fun W r w j hj =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull r g.left w _ hj _) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((gm_res r w (le j) hj _).trans (gm_pull r g'.left w _ (le j hj) _)))))
  obtain ⟨ρ, hρ⟩ := glue_unit ⊤ O (fun _ => le_top) (fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart (hN k) (q.left (g.left z))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩) u (fun j j' z hz => by
      rw [hu _ _ z j hz.1, hu _ _ z j' hz.2, hs k _ (𝟙 _ ≫ g.left) z j j' hz.1 hz.2,
        hs' k _ (𝟙 _ ≫ g'.left) z j j' (le j hz.1) (le j' hz.2), Category.assoc, Category.assoc, el, mul_inv,
        _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨ρ, fun W r w j hj => ?_⟩
  rw [← gm_res r w (le_top : O j ≤ ⊤) hj ρ, hρ, hu W r w j hj, inv_mul_cancel_right]

variable [GrpObj G'] {X : Type} [AddCommGroup X]

structure IsTorsor (i : splitTorus S X ⟶ G') (b : Module.Basis κ ℤ X) (s' : Frames N q') : Prop where
  fix : ∀ {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G'), ((t ≫ i) * g) ≫ q' = g ≫ q'
  trans : ∀ {Z : Over S} (g₁ g₂ : Z ⟶ G'), g₁ ≫ q' = g₂ ≫ q' → ∃ t : Z ⟶ splitTorus S X, g₁ = (t ≫ i) * g₂
  one : ∀ {Z : Over S}, (1 : Z ⟶ splitTorus S X) ≫ i = 1
  wt : ∀ {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G') k (W : Scheme.{0}) (r : W ⟶ Z.left) (w : W) j,
    (g ≫ q').left (r w) ∈ (N k).U j → gm (r ≫ ((t ≫ i) * g).left) w _ (s' k j) =
      gm (r ≫ t.left) w ⊤ (charUnit S X (b k)) * gm (r ≫ g.left) w _ (s' k j)

theorem gm_char {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) {W : Scheme.{0}} (r : W ⟶ Z.left) (w : W) :
    gm (r ≫ t.left) w ⊤ (charUnit S X χ) = gm r w ⊤ (splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ)) :=
  (gm_pull r t.left w ⊤ trivial _).symm.trans
    (congrArg (gm r w ⊤) (Units.ext (splitTorusPointsEquiv_val S X Z t χ).symm))

variable {i : splitTorus S X ⟶ G'} {b : Module.Basis κ ℤ X}

theorem IsTorsor.uniq (hN : ∀ k, (N k).IsLB) (H : IsTorsor i b s') {Z : Over S} {g : Z ⟶ G} {g₁ g₂ : Z ⟶ G'}
    (h₁ : Rel s s' g g₁) (h₂ : Rel s s' g g₂) : g₁ = g₂ := by
  obtain ⟨t, rfl⟩ := H.trans g₁ g₂ (h₁.1.symm.trans h₂.1)
  have key : ∀ k, splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd (b k)) = 1 := fun k => unit_ext fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart (hN k) ((g ≫ q).left z)
    have e := (h₂.2 k _ (𝟙 _) z j hj).symm.trans ((h₁.2 k _ (𝟙 _) z j hj).trans
      (H.wt t g₂ k _ (𝟙 _) z j (h₂.1 ▸ hj)))
    rw [← gm_char, map_one]
    exact mul_eq_right.1 e.symm
  have : t = 1 := (splitTorusPointsEquiv S X Z).injective (by
    rw [map_one]
    have := b.ext (f₁ := (MonoidHom.toAdditiveRight (splitTorusPointsEquiv S X Z t)).toIntLinearMap) (f₂ := 0) key
    exact MonoidHom.ext fun χ => LinearMap.congr_fun this χ.toAdd)
  rw [this, H.one, _root_.one_mul]

theorem IsTorsor.loc (hN : ∀ k, (N k).IsLB) (hs : IsFrames s) (hs' : IsFrames s') (H : IsTorsor i b s')
    {Z : Over S} (g : Z ⟶ G) (g' : Z ⟶ G') (e : g ≫ q = g' ≫ q') : ∃ g'', Rel s s' g g'' := by
  choose ρ hρ using exists_ratio hN hs hs' e
  obtain ⟨t, ht⟩ := (splitTorusPointsEquiv S X Z).surjective
    (AddMonoidHom.toMultiplicativeLeft (b.constr ℤ fun k => Additive.ofMul (ρ k)).toAddMonoidHom)
  refine ⟨(t ≫ i) * g', e.trans (H.fix t g').symm, fun k W r w j hj => ?_⟩
  rw [hρ k W r w j hj, H.wt t g' k W r w j (e ▸ hj), gm_char, ht]
  simp

omit [GrpObj G'] in

theorem nonempty_iso [GrpObj G] [GrpObj G'] {i : splitTorus S X ⟶ G'} {X₀ : Type} [AddCommGroup X₀]
    {i₀ : splitTorus S X₀ ⟶ G} {b₀ : Module.Basis κ ℤ X₀} [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    [Flat q'.left] [Surjective q'.left] [QuasiCompact q'.left] (hN : ∀ k, (N k).IsLB) (hs : IsFrames s)
    (hs' : IsFrames s') (H₀ : IsTorsor i₀ b₀ s) (H : IsTorsor i b s') : Nonempty (G ≅ G') := by
  obtain ⟨φ, hφ⟩ := exists_hom_of_rel q q' (Rel s s') Rel.comp And.left (H.uniq hN) (H.loc hN hs hs')
  obtain ⟨ψ, hψ⟩ := exists_hom_of_rel q' q (Rel s' s) Rel.comp And.left (H₀.uniq hN) (H₀.loc hN hs' hs)
  refine ⟨⟨φ, ψ, H₀.uniq hN (hψ.comp φ) ?_, H.uniq hN (hφ.comp ψ) ?_⟩⟩
  · rw [Category.comp_id]; exact hφ.symm
  · rw [Category.comp_id]; exact hψ.symm

end Frames

open WeightGen in

theorem exists_frames {E : SplitExt S} [GrpObj G] (d : E.GtDatum G) (β : E.B ≅ B) {κ : Type} (b : Module.Basis κ ℤ E.X)
    (N : κ → LB B.left) (h : ∀ k, HasGen (d.q ≫ β.hom).left (act d).left (snd (splitTorus S E.X) G).left (N k)
      (wt E.X G (b k))) : ∃ s : Frames N (d.q ≫ β.hom), IsFrames s ∧ IsTorsor d.i b s := by
  choose s s₁ s₂ using h
  have := d.q_hom
  have := d.i_hom
  have e₁ : ∀ {Z : Over S} (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G), lift t g ≫ act d = (t ≫ d.i) * g := fun t g => by
    rw [Hom.mul_def, comp_lift_assoc, lift_fst_assoc, lift_snd]
  refine ⟨s, s₁, fun t g => ?_, fun {Z} g₁ g₂ e => ?_, MonObj.one_comp _, fun t g k W r w j hj => ?_⟩
  · rw [← e₁, Category.assoc, ← Category.assoc (act d), act_q, Category.assoc, lift_snd_assoc]
  · have e' : g₁ ≫ d.q = g₂ ≫ d.q := by
      rw [← cancel_mono β.hom, Category.assoc, Category.assoc, e]
    have w : (g₁ * g₂⁻¹) ≫ d.q = toUnit Z ≫ η[E.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
      rfl
    exact ⟨d.isKernel.lift _ _ w, by rw [d.isKernel.lift_fst, inv_mul_cancel_right]⟩
  · have E₁ : (lift t g).left ≫ (act d).left = ((t ≫ d.i) * g).left := by rw [← Over.comp_left, e₁]
    have E₂ : (lift t g).left ≫ (snd (splitTorus S E.X) G).left = g.left := by rw [← Over.comp_left, lift_snd]
    have E₃ : (lift t g).left ≫ (fst (splitTorus S E.X) G).left = t.left := by rw [← Over.comp_left, lift_fst]
    have h₁ : (snd (splitTorus S E.X) G).left ((r ≫ (lift t g).left) w) = g.left (r w) :=
      congrArg (fun f => f (r w)) E₂
    have := s₂ k W (r ≫ (lift t g).left) w j (by rw [h₁]; exact hj)
    rwa [wt, Category.assoc, Category.assoc, Category.assoc, E₁, E₂, E₃] at this

open WeightGen in

theorem hasGen_of_pull {P Y A A' : Scheme.{0}} {q : Y ⟶ A} {a p : P ⟶ Y} {F : A ⟶ A'} {L : LB A'} {c : GermFn P}
    (e : a ≫ q = p ≫ q) (h : HasGen q a p (L.pull F) c) : HasGen (q ≫ F) a p L c := by
  obtain ⟨s, s₁, s₂⟩ := h
  have le : ∀ j, (q ≫ F) ⁻¹ᵁ L.U j ≤ q ⁻¹ᵁ (L.pull F).U (fun _ => j) := fun j y hy => mem_pull.2 hy
  refine ⟨fun j => res (le j) (s fun _ => j), fun Z r z j j' h₁ h₂ => ?_, fun Z r z j h₁ => ?_⟩
  · rw [gm_res r z (le j) h₁, gm_res r z (le j') h₂, s₁ Z r z _ _ (le j h₁) (le j' h₂)]
    refine congrArg (· * _) ((gm_pull_g L F (r ≫ q) z _ _ (le j h₁) (le j' h₂)).trans ?_)
    rw [Category.assoc]
  · have h₂ : (r ≫ a) z ∈ (q ≫ F) ⁻¹ᵁ L.U j :=
      (congrArg (fun x => F x ∈ L.U j) (pt_eq e (r z))).mpr h₁
    rw [gm_res (r ≫ p) z (le j) h₁, gm_res (r ≫ a) z (le j) h₂]
    exact s₂ Z r z _ (le j h₁)

theorem exists_iso_isMonHom [IsReduced S] [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (φ : G ≅ G') : ∃ i : G ≅ G', IsMonHom i.hom := by
  let c : ∀ Z : Over S, Z ⟶ G' := fun Z => toUnit Z ≫ η[G] ≫ φ.hom
  have hc : ∀ {Z Z' : Over S} (f : Z' ⟶ Z), f ≫ c Z = c Z' := fun f => comp_toUnit_assoc _ _
  refine ⟨⟨φ.hom * (c G)⁻¹, (𝟙 G' * c G') ≫ φ.inv, ?_, ?_⟩, isMonHom_of_isSemiAbelian hG hG' _ ?_⟩
  · rw [← Category.assoc, MonObj.comp_mul, hc, Category.comp_id, inv_mul_cancel_right, φ.hom_inv_id]
  · rw [MonObj.comp_mul, GrpObj.comp_inv, hc, Category.assoc, φ.inv_hom_id, Category.comp_id, mul_inv_cancel_right]
  · change η[G] ≫ (φ.hom * (c G)⁻¹) = η[G']
    rw [MonObj.comp_mul, GrpObj.comp_inv, hc, show c (𝟙_ _) = η[G] ≫ φ.hom by simp [c], mul_inv_cancel]
    simp [Hom.one_def]

open WeightGen in

theorem nonempty_iso_of_isGt {E E' : SplitExt S} [GrpObj G] [GrpObj G'] (β : E.B ≅ E'.B) (e : E.X ≃+ E'.X)
    (h : ∀ χ, LBIso (E.O χ).L ((E'.O (e χ)).L.pull β.hom.left)) (hG : E.IsGt G) (hG' : E'.IsGt G') :
    Nonempty (G ≅ G') := by
  obtain ⟨d⟩ := hG
  obtain ⟨d'⟩ := hG'
  let N := fun k => (E'.O (e (E.basis k))).L
  obtain ⟨s, s₁, s₂⟩ := exists_frames d β E.basis N fun k => by
    obtain ⟨w, hw⟩ := h (E.basis k)
    exact hasGen_of_pull (act_q_left d) ((hasGen d _).iso (act_q_left d) (exists_chart (E.O _).isLB) w hw)
  obtain ⟨s', s₁', s₂'⟩ := exists_frames d' (Iso.refl _) (E.basis.map e.toIntLinearEquiv) N fun k => by
    rw [Iso.refl_hom, Category.comp_id]
    exact hasGen d' _
  have := d.q_flat
  have := d.q_surjective
  have := d.q_affine
  have := d'.q_flat
  have := d'.q_surjective
  have := d'.q_affine
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget S).map β.hom))
  have : Flat (d.q ≫ β.hom).left := inferInstanceAs (Flat (d.q.left ≫ β.hom.left))
  have : Surjective (d.q ≫ β.hom).left := inferInstanceAs (Surjective (d.q.left ≫ β.hom.left))
  have : QuasiCompact (d.q ≫ β.hom).left := inferInstanceAs (QuasiCompact (d.q.left ≫ β.hom.left))
  have : Flat (d'.q ≫ (Iso.refl _).hom).left := inferInstanceAs (Flat (d'.q.left ≫ 𝟙 _))
  have : Surjective (d'.q ≫ (Iso.refl _).hom).left := inferInstanceAs (Surjective (d'.q.left ≫ 𝟙 _))
  have : QuasiCompact (d'.q ≫ (Iso.refl _).hom).left := inferInstanceAs (QuasiCompact (d'.q.left ≫ 𝟙 _))
  exact nonempty_iso (fun k => (E'.O _).isLB) s₁ s₁' s₂ s₂'

theorem exists_iso_isMonHom_of_isGt : ∀ (k : Type) [Field k] [IsAlgClosed k] (E E' : SplitExt (Sp k))
    (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] (β : E.B ≅ E'.B) (e : E.X ≃+ E'.X), IsMonHom β.hom →
    IsSemiAbelian G → IsSemiAbelian G' → (∀ χ, LBIso (E.O χ).L ((E'.O (e χ)).L.pull β.hom.left)) → E.IsGt G →
    E'.IsGt G' → ∃ i : G ≅ G', IsMonHom i.hom := by
  intro k _ _ E E' G G' _ _ β e _ hG hG' h d d'
  obtain ⟨φ⟩ := nonempty_iso_of_isGt β e h d d'
  exact exists_iso_isMonHom hG hG' φ

end GlobalTheory.ExtUnique
