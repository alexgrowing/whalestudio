import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperHasPowerFns
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

abbrev pb {A C : Scheme.{0}} (f : A ⟶ C) : Γ(C, ⊤)ˣ →* Γ(A, ⊤)ˣ := Units.map f.appTop.hom.toMonoidHom

theorem pb_comp {A C D : Scheme.{0}} (f : A ⟶ C) (g : C ⟶ D) (w : Γ(D, ⊤)ˣ) :
    pb (f ≫ g) w = pb f (pb g w) :=
  Units.ext (Rosenlicht.appTop_comp_apply f g w.val)

theorem pb_id {A : Scheme.{0}} (w : Γ(A, ⊤)ˣ) : pb (𝟙 A) w = w :=
  Units.ext (by simp)

variable {S : Scheme.{0}}

section Whisker

variable {X Y : Over S} (f : X ⟶ Y) (Z : Over S)

theorem isPullback_whiskerRight :
    IsPullback (f ▷ Z).left (fst X Z).left (fst Y Z).left f.left := by
  have h1 : IsPullback (fst Y Z).left (snd Y Z).left Y.hom Z.hom := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst X Z).left (snd X Z).left X.hom Z.hom := IsPullback.of_hasPullback _ _
  have e1 : (f ▷ Z).left ≫ (snd Y Z).left = (snd X Z).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have e2 : (f ▷ Z).left ≫ (fst Y Z).left = (fst X Z).left ≫ f.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  refine IsPullback.of_right (t := h1.flip) ?_ e2
  rw [e1, Over.w f]
  exact h2.flip

theorem isPullback_whiskerLeft :
    IsPullback (Z ◁ f).left (snd Z X).left (snd Z Y).left f.left := by
  have h1 : IsPullback (fst Z Y).left (snd Z Y).left Z.hom Y.hom := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst Z X).left (snd Z X).left Z.hom X.hom := IsPullback.of_hasPullback _ _
  have e1 : (Z ◁ f).left ≫ (fst Z Y).left = (fst Z X).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have e2 : (Z ◁ f).left ≫ (snd Z Y).left = (snd Z X).left ≫ f.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  refine IsPullback.of_right (t := h1) ?_ e2
  rw [e1, Over.w f]
  exact h2

end Whisker

theorem pb_act_eq {Ch : Type} [AddCommGroup Ch] [Module.Free ℤ Ch] (W : Over S) [IsIntegral W.left]
    (a : splitTorus S Ch ⊗ W ⟶ W) (ha : lift (1 : W ⟶ splitTorus S Ch) (𝟙 W) ≫ a = 𝟙 W)
    (e : splitTorus S Ch ⟶ W) (u : Γ(W.left, ⊤)ˣ)
    (h₁ : pb (lift (𝟙 _) e ≫ a).left u = 1) (h₂ : pb e.left u = 1) :
    pb a.left u = pb (snd (splitTorus S Ch) W).left u := by
  set ρ := pb a.left u * (pb (snd (splitTorus S Ch) W).left u)⁻¹ with hρ
  have hu : pb (GlobalTheory.BiextTriv.unitSec Ch W) ρ = 1 := by
    have c1 : pb (GlobalTheory.BiextTriv.unitSec Ch W) (pb a.left u) = u := by
      rw [← pb_comp, GlobalTheory.BiextTriv.unitSec, ← Over.comp_left, ha, Over.id_left, pb_id]
    have c2 : pb (GlobalTheory.BiextTriv.unitSec Ch W) (pb (snd (splitTorus S Ch) W).left u) = u := by
      rw [← pb_comp, GlobalTheory.BiextTriv.unitSec, ← Over.comp_left, lift_snd, Over.id_left, pb_id]
    rw [hρ, map_mul, map_inv, c1, c2, mul_inv_cancel]
  obtain ⟨χ, hχ⟩ := GlobalTheory.BiextTriv.exists_char (X := Ch) (Y := W) ρ (congrArg Units.val hu)
  have hχ' : ρ = pb (fst (splitTorus S Ch) W).left (charUnit S Ch χ) := Units.ext hχ
  have hc : charUnit S Ch χ = 1 := by
    have c0 : pb (lift (𝟙 _) e).left ρ = charUnit S Ch χ := by
      rw [hχ', ← pb_comp, ← Over.comp_left, lift_fst, Over.id_left, pb_id]
    rw [← c0, hρ, map_mul, map_inv, ← pb_comp, ← pb_comp, ← Over.comp_left, ← Over.comp_left, lift_snd, h₁, h₂]
    simp
  rw [hc, map_one] at hχ'
  exact mul_inv_eq_one.1 (hρ.symm.trans hχ')

section Orbit

variable {G B : Over S} [GrpObj G] [GrpObj B] {T : Over S} [GrpObj T]

theorem exists_orbit (q : G ⟶ B) [IsMonHom q] (i : T ⟶ G) (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B))
    {Z : Over S} (g g' : Z ⟶ G) (h : g ≫ q = g' ≫ q) : ∃ s : Z ⟶ T, g' = g * (s ≫ i) := by
  have e : (g⁻¹ * g') ≫ q = toUnit Z ≫ η := by
    rw [MonObj.mul_comp, ← h, ← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp, Hom.one_def]
  refine ⟨hk.lift (g⁻¹ * g') (toUnit Z) e, ?_⟩
  rw [hk.lift_fst, mul_inv_cancel_left]

end Orbit

section Act

variable {G T : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj T]

def act₁ (i : T ⟶ G) : T ⊗ (G ⊗ G) ⟶ G ⊗ G :=
  lift ((snd T (G ⊗ G) ≫ fst G G) * (fst T (G ⊗ G) ≫ i)) (snd T (G ⊗ G) ≫ snd G G)

def act₂ (i : T ⟶ G) : T ⊗ (G ⊗ G) ⟶ G ⊗ G :=
  lift (snd T (G ⊗ G) ≫ fst G G) ((snd T (G ⊗ G) ≫ snd G G) * (fst T (G ⊗ G) ≫ i))

theorem lift_act₁ (i : T ⟶ G) {Z : Over S} (s : Z ⟶ T) (y : Z ⟶ G ⊗ G) :
    lift s y ≫ act₁ i = lift ((y ≫ fst G G) * (s ≫ i)) (y ≫ snd G G) := by
  simp [act₁, MonObj.comp_mul]

theorem lift_act₂ (i : T ⟶ G) {Z : Over S} (s : Z ⟶ T) (y : Z ⟶ G ⊗ G) :
    lift s y ≫ act₂ i = lift (y ≫ fst G G) ((y ≫ snd G G) * (s ≫ i)) := by
  simp [act₂, MonObj.comp_mul]

end Act

section Act2

variable {G T : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj T] (i : T ⟶ G) [IsMonHom i]

theorem act₁_unit : lift (1 : G ⊗ G ⟶ T) (𝟙 _) ≫ act₁ i = 𝟙 _ := by
  rw [lift_act₁]
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp]

theorem act₂_unit : lift (1 : G ⊗ G ⟶ T) (𝟙 _) ≫ act₂ i = 𝟙 _ := by
  rw [lift_act₂]
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp]

theorem act₁_axis : lift (𝟙 T) (1 : T ⟶ G ⊗ G) ≫ act₁ i = i ≫ lift (𝟙 G) (1 : G ⟶ G) := by
  rw [lift_act₁]
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp, MonObj.comp_one]

theorem act₂_axis : lift (𝟙 T) (1 : T ⟶ G ⊗ G) ≫ act₂ i = i ≫ lift (1 : G ⟶ G) (𝟙 G) := by
  rw [lift_act₂]
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp, MonObj.comp_one]

end Act2

section Main

variable {G B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B] {Ch : Type} [AddCommGroup Ch] [Module.Free ℤ Ch]

theorem exists_descent (q : G ⟶ B) [IsMonHom q] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (i : splitTorus S Ch ⟶ G) [IsMonHom i] (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B))
    [IsIntegral (G ⊗ G).left] (u : Γ((G ⊗ G).left, ⊤)ˣ)
    (h0 : pb (lift (1 : G ⟶ G) (𝟙 G)).left u = 1) (h1 : pb (lift (𝟙 G) (1 : G ⟶ G)).left u = 1) :
    ∃ c : Γ((B ⊗ B).left, ⊤), (lift (fst G G ≫ q) (snd G G ≫ q)).left.appTop.hom c = u.val := by
  have e₀ : pb (1 : splitTorus S Ch ⟶ G ⊗ G).left u = 1 := by
    have : (1 : splitTorus S Ch ⟶ G ⊗ G) = (1 : splitTorus S Ch ⟶ G) ≫ lift (1 : G ⟶ G) (𝟙 G) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp, MonObj.comp_one]
    rw [this, Over.comp_left, pb_comp, h0, map_one]
  have i₁ : pb (act₁ i).left u = pb (snd (splitTorus S Ch) (G ⊗ G)).left u := by
    refine pb_act_eq (G ⊗ G) (act₁ i) (act₁_unit i) 1 u ?_ e₀
    rw [act₁_axis, Over.comp_left, pb_comp, h1, map_one]
  have i₂ : pb (act₂ i).left u = pb (snd (splitTorus S Ch) (G ⊗ G)).left u := by
    refine pb_act_eq (G ⊗ G) (act₂ i) (act₂_unit i) 1 u ?_ e₀
    rw [act₂_axis, Over.comp_left, pb_comp, h0, map_one]
  have j₁ : ∀ {Z : Over S} (s : Z ⟶ splitTorus S Ch) (y : Z ⟶ G ⊗ G),
      pb (lift s y ≫ act₁ i).left u = pb y.left u := fun s y => by
    rw [Over.comp_left, pb_comp, i₁, ← pb_comp, ← Over.comp_left, lift_snd]
  have j₂ : ∀ {Z : Over S} (s : Z ⟶ splitTorus S Ch) (y : Z ⟶ G ⊗ G),
      pb (lift s y ≫ act₂ i).left u = pb y.left u := fun s y => by
    rw [Over.comp_left, pb_comp, i₂, ← pb_comp, ← Over.comp_left, lift_snd]
  let qo : G ⊗ G ⟶ B ⊗ B := lift (fst G G ≫ q) (snd G G ≫ q)
  have hfac : qo = (q ▷ G) ≫ (B ◁ q) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [qo]
  let r := qo.left
  have hr : r = (q ▷ G).left ≫ (B ◁ q).left := by
    simp only [r]; rw [hfac, Over.comp_left]
  have : Flat (q ▷ G).left := MorphismProperty.of_isPullback (isPullback_whiskerRight q G).flip ‹_›
  have : Flat (B ◁ q).left := MorphismProperty.of_isPullback (isPullback_whiskerLeft q B).flip ‹_›
  have : Surjective (q ▷ G).left := MorphismProperty.of_isPullback (isPullback_whiskerRight q G).flip ‹_›
  have : Surjective (B ◁ q).left := MorphismProperty.of_isPullback (isPullback_whiskerLeft q B).flip ‹_›
  have : QuasiCompact (q ▷ G).left := MorphismProperty.of_isPullback (isPullback_whiskerRight q G).flip ‹_›
  have : QuasiCompact (B ◁ q).left := MorphismProperty.of_isPullback (isPullback_whiskerLeft q B).flip ‹_›
  have : Flat r := by rw [hr]; infer_instance
  have : Surjective r := by rw [hr]; infer_instance
  have : QuasiCompact r := by rw [hr]; infer_instance
  have hp := IsPullback.of_hasPullback r r
  have hW : r ≫ (B ⊗ B).hom = (G ⊗ G).hom := Over.w qo
  let P : Over S := Over.mk (pullback.fst r r ≫ (G ⊗ G).hom)
  let g : P ⟶ G ⊗ G := Over.homMk (pullback.fst r r) rfl
  let g' : P ⟶ G ⊗ G := Over.homMk (pullback.snd r r) (by
    show pullback.snd r r ≫ (G ⊗ G).hom = pullback.fst r r ≫ (G ⊗ G).hom
    rw [← hW, pullback.condition_assoc])
  have hq : g ≫ qo = g' ≫ qo := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have hq₁ : (g ≫ fst G G) ≫ q = (g' ≫ fst G G) ≫ q := by
    have := congrArg (· ≫ fst B B) hq
    simpa [qo] using this
  have hq₂ : (g ≫ snd G G) ≫ q = (g' ≫ snd G G) ≫ q := by
    have := congrArg (· ≫ snd B B) hq
    simpa [qo] using this
  obtain ⟨s₁, hs₁⟩ := exists_orbit q i hk _ _ hq₁
  obtain ⟨s₂, hs₂⟩ := exists_orbit q i hk _ _ hq₂
  have hg' : g' = lift s₂ (lift s₁ g ≫ act₁ i) ≫ act₂ i := by
    rw [lift_act₂, lift_act₁]
    apply CartesianMonoidalCategory.hom_ext
    · simpa using hs₁
    · simpa using hs₂
  have key : pb g'.left u = pb g.left u := by
    rw [hg', j₂, j₁]
  obtain ⟨c, hc, -⟩ := (GlobalTheory.FlatDescent.existsUnique_appTop_eq_iff r hp u.val).2
    (congrArg Units.val key).symm
  exact ⟨c, hc⟩

theorem unit_eq_one (q : G ⟶ B) [IsMonHom q] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (i : splitTorus S Ch ⟶ G) [IsMonHom i] (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B))
    [IsIntegral (G ⊗ G).left] (hB : Function.Surjective (B ⊗ B).hom.appTop.hom) (u : Γ((G ⊗ G).left, ⊤)ˣ)
    (h0 : pb (lift (1 : G ⟶ G) (𝟙 G)).left u = 1) (h1 : pb (lift (𝟙 G) (1 : G ⟶ G)).left u = 1) : u = 1 := by
  obtain ⟨c, hc⟩ := exists_descent q i hk u h0 h1
  obtain ⟨b, rfl⟩ := hB c
  have hw : (lift (fst G G ≫ q) (snd G G ≫ q)).left ≫ (B ⊗ B).hom = (G ⊗ G).hom :=
    Over.w (lift (fst G G ≫ q) (snd G G ≫ q))
  rw [← Rosenlicht.appTop_comp_apply, hw] at hc
  have hv : (lift (1 : G ⟶ G) (𝟙 G)).left ≫ (G ⊗ G).hom = G.hom := Over.w (lift (1 : G ⟶ G) (𝟙 G))
  have hs : (η : 𝟙_ (Over S) ⟶ G).left ≫ G.hom = 𝟙 S := Over.w (η : 𝟙_ (Over S) ⟶ G)
  have hb : b = 1 := by
    have e1 := congrArg Units.val h0
    simp only [Units.coe_map, Units.val_one] at e1
    have e2 : (lift (1 : G ⟶ G) (𝟙 G)).left.appTop.hom ((G ⊗ G).hom.appTop.hom b) = 1 := by
      rw [hc]; exact e1
    rw [← Rosenlicht.appTop_comp_apply, hv] at e2
    have e3 := congrArg (η : 𝟙_ (Over S) ⟶ G).left.appTop.hom e2
    rw [← Rosenlicht.appTop_comp_apply, hs, map_one] at e3
    simpa using e3
  apply Units.ext
  rw [← hc, hb, map_one, Units.val_one]

end Main

theorem unit_eq_one_of_axes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (_ : AbQuot t x) (d : ℕ) (_ : GermAt t x d) (u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ), (ax0 t x).appTop.hom u.val = 1 → (ax1 t x).appTop.hom u.val = 1 → u = 1 := by
  intro E _ _ _ H _ _ X t k _ _ p _ _ x Q d _ u h0 h1
  have hs : IsSemiAbelian (GF t x) := IsSemiAbelian.pullback x t.G t.semi
  have := hs.smooth
  have := hs.geomConnected
  have := Q.proper
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_flat
  have := Q.q_surjective
  have := Q.q_quasiCompact
  obtain ⟨c₁, c₂⟩ := GlobalTheory.GroupConn.connectedSpace_group _ (GF t x)
  obtain ⟨-, c₄⟩ := c₂ Q.Ch (GF t x) c₁
  have : Smooth (GF t x ⊗ GF t x).hom := inferInstanceAs (Smooth (pullback.fst (GF t x).hom (GF t x).hom ≫ _))
  have : IsIntegral (GF t x ⊗ GF t x).left := isIntegral_of_smooth_field_of_connectedSpace (GF t x ⊗ GF t x).hom
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper Q.tB.G Q.tB.semi
  have hB := (GlobalTheory.globalFns_holds _ _ (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)).2
  exact unit_eq_one Q.q Q.i Q.isKernel hB u (Units.ext h0) (Units.ext h1)

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit
