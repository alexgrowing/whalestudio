import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sab_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) {e : S'' ⟶ S} (he : g ≫ f = e) :
    ∃ n : SABMap t'' t e, n.φ = m'.φ ≫ m.φ := by
  subst he
  exact sabComp pullCubComp E H S S' S'' t t' t'' f g m m'

theorem sab_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {e : S'' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t e) (g : S'' ⟶ S') (he : g ≫ f = e) :
    ∃ m' : SABMap t'' t' g, m'.φ ≫ m.φ = n.φ := by
  subst he
  obtain ⟨m', h⟩ := sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n
  exact ⟨m', h.symm⟩

theorem sec_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) (x : 𝟙_ (Over S'') ⟶ t''.G) (y : 𝟙_ (Over S') ⟶ t'.G)
    (h : x.left ≫ m'.φ ≫ m.φ = g ≫ y.left ≫ m.φ) : x.left ≫ m'.φ = g ≫ y.left := by
  apply m.cart.1.hom_ext
  · simpa only [Category.assoc] using h
  · have a₁ : x.left ≫ t''.G.hom = 𝟙 _ := Over.w x
    have a₂ : y.left ≫ t'.G.hom = 𝟙 _ := Over.w y
    rw [Category.assoc, m'.cart.1.w, ← Category.assoc, a₁, Category.assoc, a₂]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_pow {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (x : 𝟙_ (Over S') ⟶ t'.G) (y : 𝟙_ (Over S) ⟶ t.G)
    (h : x.left ≫ m.φ = f ≫ y.left) (k : ℕ) : (x ^ k).left ≫ m.φ = f ≫ (y ^ k).left := by
  let U : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) :=
    Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e : pushHom m.cart _ x = preHom U y := Over.OverMorphism.ext h
  have e' : pushHom m.cart _ (x ^ k) = preHom U (y ^ k) := by rw [map_pow, map_pow, e]
  exact congrArg (fun z => z.left) e'

theorem zeta_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : zeta a = zeta b ^ (b / a) := by
  obtain ⟨k, rfl⟩ := h
  have ha : a ≠ 0 := by rintro rfl; simp at hb
  have hk : k ≠ 0 := by rintro rfl; simp at hb
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha), zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  push_cast
  field_simp

noncomputable def baseOf (l : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) : Base l F where
  unit n hn := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
  ρ := (IntermediateField.inclusion h).toRingHom (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := (IntermediateField.inclusion h).toRingHom (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective (RingHom.injective _)

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem spMap_inclusion_self {F : IntermediateField ℚ ℂ} (h : F ≤ F) :
    spMap (IntermediateField.inclusion h).toRingHom = 𝟙 (Sp F) := by
  rw [← spMap_id']
  exact congrArg spMap (RingHom.ext fun x => Subtype.ext (IntermediateField.coe_inclusion h x))

theorem baseOf_rho_coe (l : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) :
    (((baseOf l F h).ρ : F) : ℂ) = H.rt0 := IntermediateField.coe_inclusion h (baseKA l).ρ

theorem baseOf_rho (l l₂ : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) (h₂ : KA l₂ ≤ F) :
    (baseOf l F h).ρ = (baseOf l₂ F h₂).ρ :=
  Subtype.ext ((baseOf_rho_coe l F h).trans (baseOf_rho_coe l₂ F h₂).symm)

theorem baseOf_zeta (l l₂ : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) (h₂ : KA l₂ ≤ F) (hd : l.A ∣ l₂.A) :
    (baseOf l F h).ζ = (baseOf l₂ F h₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (IntermediateField.coe_inclusion h _).trans ((zeta_dvd l₂.A_pos hd).trans
    (congrArg (· ^ (l₂.A / l.A)) (IntermediateField.coe_inclusion h₂ (baseKA l₂).ζ).symm)))

def ObjCompSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)

variable {D : Datum H} {l l₂ : Level H}

def Represents {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {s : X ⟶ Sp B} (o : Obj D l b s) : Prop :=
  ∀ (S : Scheme.{0}) (s' : S ⟶ Sp B) (o' : Obj D l b s'), IsReduced S →
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o' o f)

theorem represents_pullback (hC : ObjCompSt) (Xo : Moduli D l) {B : Type} [CommRing B] {b : Base l B} (j : KA l →+* B)
    (hR : ∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S →
      ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f))
    {s : pullback Xo.s (spMap j) ⟶ Sp B} (hs : s = pullback.snd _ _) (o : Obj D l b s)
    (mo : ObjMap o Xo.univ (pullback.fst _ _)) : Represents o := by
  subst hs
  intro S s' o' hS
  obtain ⟨g, ⟨hg, ⟨u⟩⟩, huniq⟩ := hR S s' o' hS
  have hl : pullback.lift g s' hg ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  refine ⟨pullback.lift g s' hg, ⟨pullback.lift_snd _ _ _, ?_⟩, ?_⟩
  · obtain ⟨u', -⟩ := ((hC E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 _ (pullback.lift g s' hg) mo).2
      (hl.symm ▸ u)
    exact ⟨u'⟩
  · rintro f ⟨hf, ⟨v⟩⟩
    apply pullback.hom_ext
    · rw [hl]
      obtain ⟨v', -⟩ := ((hC E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 _ f mo).1 v
      exact huniq _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hf], ⟨v'⟩⟩
    · rw [hf, pullback.lift_snd]

theorem iso_cover (hC : ObjCompSt) {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} (k k' : ℕ)
    {X X₂ Y : Scheme.{0}} {s : X ⟶ Sp B} {r : X₂ ⟶ X} {π : Y ⟶ X} (o : Obj D l b s) (o₂ : Obj D l₂ b₂ (r ≫ s))
    (oc : Obj D l₂ b₂ (π ≫ s)) (o₁ : Obj D l b (π ≫ s)) (n : ObjMap o₁ o π)
    (m : SABMap o₂.t o.t r) (mc : SABMap oc.t o.t π)
    (hm : (∀ a, (o₂.eta a ^ k).left ≫ m.φ = r ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ k').left ≫ m.φ = r ≫ (o.etaA a).left))
    (hmc : (∀ a, (oc.eta a ^ k).left ≫ mc.φ = π ≫ (o.eta a).left) ∧
      (∀ a, (oc.etaA a ^ k').left ≫ mc.φ = π ≫ (o.etaA a).left))
    (hX : Represents o) (hX₂ : Represents o₂) (rX₂ : IsReduced X₂) (rY : IsReduced Y)
    (rig : ∀ m m' : SABMap o₁.t o.t π, (∀ a, ∃ σ, (o₁.eta a).left ≫ m.φ = σ ∧ (o₁.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (univ : ∀ (T : Scheme.{0}) (f : T ⟶ X) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f),
      (∀ a, (o'.eta a ^ k).left ≫ m'.φ = f ≫ (o.eta a).left) ∧
        (∀ a, (o'.etaA a ^ k').left ≫ m'.φ = f ≫ (o.etaA a).left) →
      ∃! h : T ⟶ Y, h ≫ π = f ∧ ∃ u : ObjMap o' oc h, u.toSABMap.φ ≫ mc.φ = m'.φ) :
    ∃ h : X₂ ⟶ Y, IsIso h ∧ h ≫ π = r := by
  obtain ⟨h, ⟨hh, u, hu⟩, -⟩ := univ X₂ r o₂ m hm
  obtain ⟨g, ⟨hg, ⟨w⟩⟩, -⟩ := hX₂ Y (π ≫ s) oc rY
  obtain ⟨v, hv⟩ := sab_cancel mc n.toSABMap (𝟙 Y) (Category.id_comp _)
  have v₁ : ∀ a, (o₁.eta a).left ≫ v.φ = (oc.eta a ^ k).left := fun a =>
    (sec_cancel v mc _ _ (by rw [hv, hmc.1, Category.id_comp]; exact n.eta a)).trans (Category.id_comp _)
  have v₂ : ∀ a, (o₁.etaA a).left ≫ v.φ = (oc.etaA a ^ k').left := fun a =>
    (sec_cancel v mc _ _ (by rw [hv, hmc.2, Category.id_comp]; exact n.etaA a)).trans (Category.id_comp _)
  obtain ⟨vw, hvw⟩ := sab_comp v w.toSABMap (Category.id_comp g)
  have key : ∀ (e : Y ⟶ X) (he : g ≫ r = e), ∃ z : ObjMap o₁ o e, z.toSABMap.φ = v.φ ≫ w.toSABMap.φ ≫ m.φ := by
    intro e he
    obtain ⟨z, hz⟩ := sab_comp vw m he
    rw [hvw, Category.assoc] at hz
    refine ⟨⟨z, fun a => ?_, fun a => ?_⟩, hz⟩
    · show _ ≫ z.φ = _
      rw [hz, ← Category.assoc, v₁, ← Category.assoc, sec_pow w.toSABMap _ _ (w.eta a), Category.assoc, hm.1,
        ← Category.assoc, he]
    · show _ ≫ z.φ = _
      rw [hz, ← Category.assoc, v₂, ← Category.assoc, sec_pow w.toSABMap _ _ (w.etaA a), Category.assoc, hm.2,
        ← Category.assoc, he]
  have hgr : g ≫ r = π := by
    obtain ⟨z, -⟩ := key _ rfl
    exact (hX Y (π ≫ s) o₁ rY).unique ⟨by rw [Category.assoc, hg], ⟨z⟩⟩ ⟨rfl, ⟨n⟩⟩
  obtain ⟨z, hz⟩ := key _ hgr
  have hzn : z.toSABMap.φ = n.toSABMap.φ := rig _ _ fun a => ⟨_, z.eta a, n.eta a⟩
  have : IsIso v.φ := v.cart.1.isIso_fst_of_isIso
  have hwm : w.toSABMap.φ ≫ m.φ = mc.φ := by
    rw [← cancel_epi v.φ, ← hz, hzn, hv]
  refine ⟨h, ⟨g, ?_, ?_⟩, hh⟩
  · obtain ⟨x, -⟩ := ((hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ o₂ oc o₂).2 g h w).1 u
    obtain ⟨y, -⟩ := (hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ o₂ o₂ o₂).1
    exact (hX₂ X₂ (r ≫ s) o₂ rX₂).unique
      ⟨by rw [Category.assoc, hg, ← Category.assoc, hh], ⟨x⟩⟩ ⟨Category.id_comp _, ⟨y⟩⟩
  · obtain ⟨x, hx⟩ := ((hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ oc o₂ oc).2 h g u).1 w
    obtain ⟨y, hy⟩ := (hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ oc oc oc).1
    exact (univ Y π oc mc hmc).unique
      ⟨by rw [Category.assoc, hh, hgr], x, by rw [hx, Category.assoc, hu, hwm]⟩
      ⟨Category.id_comp _, y, by rw [hy, Category.id_comp]⟩

theorem levelMap_over_field
    (hSm : ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X)
    (hPull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f))
    (hC : ObjCompSt)
    (hRig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (hRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f))
    (hCov : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ)
    (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X)
    (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm₁ : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hm₂ : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (F : Type) [Field F] (b : Base l F) (b₂ : Base l₂ F) (j : KA l →+* F) (j₂ : KA l₂ →+* F)
    (e₁ : j (baseKA l).ρ = b.ρ) (e₂ : j (baseKA l).ζ = b.ζ) (e₃ : j₂ (baseKA l₂).ρ = b₂.ρ)
    (e₄ : j₂ (baseKA l₂).ζ = b₂.ζ) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A))
    (rF : pullback Xo₂.s (spMap j₂) ⟶ pullback Xo.s (spMap j))
    (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r) (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) :
    IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  obtain ⟨o, ⟨mo⟩⟩ := hPull E H D l _ _ (baseKA l) b j _ _ Xo.s
    (pullback.snd Xo.s (spMap j)) (pullback.fst _ _) e₁ e₂ pullback.condition Xo.univ
  obtain ⟨o₂, ⟨mo₂⟩⟩ := hPull E H D l₂ _ _ (baseKA l₂) b₂ j₂ _ _ Xo₂.s
    (rF ≫ pullback.snd Xo.s (spMap j)) (pullback.fst _ _) e₃ e₄ (by rw [h₂]; exact pullback.condition) Xo₂.univ
  obtain ⟨Y, π, oc, mc, hfin, het, hsur, hmc, univ⟩ := hCov E H D l l₂ _ b b₂ _ _ o hpq hd hρ hζ
  obtain ⟨o₁, ⟨n⟩⟩ := hPull E H D l _ _ b b (RingHom.id _) _ _ _
    (π ≫ pullback.snd Xo.s (spMap j)) π rfl rfl (by rw [spMap_id', Category.comp_id]) o
  obtain ⟨x, hx⟩ := sab_comp mo₂.toSABMap m h₁.symm
  obtain ⟨mF, hmF⟩ := sab_cancel mo.toSABMap x rF rfl
  have := Xo.smooth
  have := Xo₂.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth Xo₂.s := SmoothOfRelativeDimension.smooth D.dim _
  have rY : IsReduced Y := (hSm F Y (π ≫ pullback.snd Xo.s (spMap j)) inferInstance).1
  have rX₂ := (hSm F _ (pullback.snd Xo₂.s (spMap j₂)) inferInstance).1
  obtain ⟨h, hiso, hh⟩ := iso_cover hC (l₂.M / l.M) (l₂.A / l.A) o o₂ oc o₁ n mF mc
    ⟨fun a => sec_cancel mF mo.toSABMap _ _ (by
      rw [hmF, hx, ← Category.assoc, sec_pow mo₂.toSABMap _ _ (mo₂.eta a), Category.assoc, hm₁, ← Category.assoc, ← h₁,
        Category.assoc]
      exact congrArg _ (mo.eta a).symm),
    fun a => sec_cancel mF mo.toSABMap _ _ (by
      rw [hmF, hx, ← Category.assoc, sec_pow mo₂.toSABMap _ _ (mo₂.etaA a), Category.assoc, hm₂, ← Category.assoc, ← h₁,
        Category.assoc]
      exact congrArg _ (mo.etaA a).symm)⟩ hmc
    (represents_pullback hC Xo _ (fun S s o hS => hRep E H D l Xo _ b _ S s o hS e₁ e₂) rfl o mo)
    (represents_pullback hC Xo₂ _ (fun S s o hS => hRep E H D l₂ Xo₂ _ b₂ _ S s o hS e₃ e₄) h₂ o₂ mo₂)
    rX₂ rY (hRig E H D l _ _ b b _ _ _ _ o o₁ π (Or.inl rY)) univ
  rw [← hh]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem levelMap_finite_etale_surjective : (∀ (k : Type) [Field k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S'
    : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
    : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b'
    : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s''
    : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
    : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
    : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
    f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
    f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B
    : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂
    : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m
    : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta
    a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s
    : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S'
    ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta
    a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B
    : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B
    : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂
    : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m
    : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫
    s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta
    a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA
    a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo
    : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK
    : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l)
    : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc
    : c.F = c₂.F) (rF
    : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion
    hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  intro hSm hPull hC _ hRig hRep hCov E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m ⟨_, _, hm₁, hm₂⟩ c c₂ hc rF h₁ h₂
  obtain ⟨F, fin, conj, zm, le⟩ := c
  obtain ⟨F₂, fin₂, conj₂, zm₂, le₂⟩ := c₂
  obtain rfl : F = F₂ := hc
  exact levelMap_over_field hSm hPull hC hRig hRep hCov Xo Xo₂ hpq hd r m hm₁ hm₂ F (baseOf l F le) (baseOf l₂ F le₂)
    _ _ rfl rfl rfl rfl (baseOf_rho _ _ _ _ _) (baseOf_zeta _ _ _ _ _ hd.2.2) rF h₁
    (h₂.trans ((congrArg _ (spMap_inclusion_self _)).trans (Category.comp_id _)))

end GlobalTheory.LevelCover
