import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerComplexLiftAndExtensionLemmasStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.TowerOne

universe u u'

variable {C : Type u} [Category.{0} C] {C' : Type u'} [Category.{0} C'] {K : Cx C} {K' : Cx C'}

theorem exists_cocycle_of_h0_surjective (m : CxMap K K') (hm : Function.Surjective m.h0) (g' : K'.M0.c0)
    (hg : K'.D0 g' = 0) : ∃ g, K.D0 g = 0 ∧ m.p0 g = g' := by
  obtain ⟨⟨g, hg0⟩, h⟩ := hm ⟨g', hg⟩
  exact ⟨g, hg0, congrArg Subtype.val h⟩

theorem exists_primitive_of_h1_injective (m : CxMap K K') (hm : Function.Injective m.h1) (z : K.T1) (hz : z ∈ K.Z1)
    (g : K'.M0.c0) (h : m.p1 z = K'.D0 g) : ∃ g', K.D0 g' = z := by
  have h0 : m.h1 (QuotientAddGroup.mk ⟨z, hz⟩ : K.H1) = 0 := by
    change (QuotientAddGroup.mk (m.z1 ⟨z, hz⟩) : K'.H1) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨g, h.symm⟩
  have h1 := hm (h0.trans (map_zero m.h1).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

theorem exists_cocycle_of_h1_surjective (m : CxMap K K') (hm : Function.Surjective m.h1) (z' : K'.T1)
    (hz : z' ∈ K'.Z1) : ∃ z ∈ K.Z1, ∃ g, z' = m.p1 z + K'.D0 g := by
  obtain ⟨x, hx⟩ := hm (QuotientAddGroup.mk ⟨z', hz⟩)
  obtain ⟨⟨z, hz1⟩, rfl⟩ := QuotientAddGroup.mk_surjective x
  change (QuotientAddGroup.mk (m.z1 ⟨z, hz1⟩) : K'.H1) = _ at hx
  rw [QuotientAddGroup.eq] at hx
  obtain ⟨g, hg⟩ := hx
  refine ⟨z, hz1, g, ?_⟩
  have e : K'.D0 g = -m.p1 z + z' := hg
  rw [e]; abel

theorem cx_D1_D0_eq_zero (K : Cx C) (g : K.M0.c0) : K.D1 (K.D0 g) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ
    simp only [Cx.D1, Cx.D0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sub, K.M0.map_comp,
      Prod.fst_zero, Pi.zero_apply]
    abel
  · funext T T' φ
    simp only [Cx.D1, Cx.D0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sub, K.diffZero_natural,
      Prod.snd_zero, Prod.fst_zero, Pi.zero_apply]
    abel
  · funext T
    simp only [Cx.D1, Cx.D0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, K.diffOne_diffZero, Prod.snd_zero, Pi.zero_apply]

end GlobalTheory.CxCoh.TowerOne

namespace GlobalTheory.CxCoh.TowerOne

open ObjectProperty

variable {C : Type 1} [Category.{0} C]

theorem tower (K : Cx C) (Q : ℕ → ObjectProperty C) (hQ : ∀ n, Q n ≤ Q (n + 1))
    (hex : ∀ T, ∃ n, Q n T)
    (h0s : ∀ n, Function.Surjective ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h0)
    (h1b : ∀ n, Function.Bijective ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h1) :
    Function.Bijective (K.resMap (Q 0).ι).h1 := by
  have ml := GlobalTheory.T.tower_complex_lift_and_extension_lemmas
  have hle : ∀ n k T, Q n T → Q (n + k) T := by
    intro n k T h
    induction k with
    | zero => exact h
    | succ k ih => exact hQ (n + k) T ih
  have hle' : ∀ n m, n ≤ m → ∀ T, Q n T → Q m T := by
    intro n m hnm T h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact hle n k T h
  have hex2 : ∀ T T', ∃ n, Q n T ∧ Q n T' := by
    intro T T'
    obtain ⟨n, h⟩ := hex T
    obtain ⟨n', h'⟩ := hex T'
    exact ⟨max n n', hle' _ _ (le_max_left _ _) _ h, hle' _ _ (le_max_right _ _) _ h'⟩
  have hex3 : ∀ T T' T'', ∃ n, Q n T ∧ Q n T' ∧ Q n T'' := by
    intro T T' T''
    obtain ⟨n, h, h'⟩ := hex2 T T'
    obtain ⟨n', h''⟩ := hex T''
    exact ⟨max n n', hle' _ _ (le_max_left _ _) _ h, hle' _ _ (le_max_left _ _) _ h',
      hle' _ _ (le_max_right _ _) _ h''⟩
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hx' : (K.resMap (Q 0).ι).p1 z ∈ (K.res (Q 0).ι).D0.range := by
      change (QuotientAddGroup.mk ((K.resMap (Q 0).ι).z1 ⟨z, hz⟩) : (K.res (Q 0).ι).H1) = 0 at hx
      rw [QuotientAddGroup.eq_zero_iff] at hx
      exact hx
    have hb : ∀ n, ∃ a, (K.res (Q n).ι).D0 a = (K.resMap (Q n).ι).p1 z := by
      intro n
      induction n with
      | zero => exact hx'
      | succ n ih =>
        obtain ⟨g, hg⟩ := ih
        exact exists_primitive_of_h1_injective _ (h1b n).1 ((K.resMap (Q (n + 1)).ι).p1 z)
          ((K.resMap (Q (n + 1)).ι).z1 ⟨z, hz⟩).2 g hg.symm
    obtain ⟨a, has, had⟩ := ml.1 (fun _ ↦ PUnit) (fun n ↦ (K.res (Q n).ι).M0.c0)
      (fun n ↦ (K.res (Q n).ι).T1) (fun _ ↦ 0) (fun n ↦ (K.res (Q n).ι).D0) (fun _ ↦ 0)
      (fun n ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).p0)
      (fun n ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).p1)
      (fun n x ↦ by simp) (fun n x ↦ by simp)
      (fun n x ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).pullback_firstDifferential x)
      (fun n x ↦ ⟨PUnit.unit, Subsingleton.elim _ _⟩)
      (fun n a ha ↦ by
        obtain ⟨g, hg0, hg⟩ := exists_cocycle_of_h0_surjective _ (h0s n) a ha
        exact ⟨g, 0, hg0, by simpa using hg.symm⟩)
      (fun n ↦ (K.resMap (Q n).ι).p1 z) (fun n ↦ rfl) hb
    have hs : ∀ j (X : (Q j).FullSubcategory), a (j + 1) ⟨X.obj, hQ j _ X.property⟩ = a j X :=
      fun j X ↦ congrFun (has j) X
    have ha_le : ∀ n k T (h : Q n T) (h' : Q (n + k) T), a (n + k) ⟨T, h'⟩ = a n ⟨T, h⟩ := by
      intro n k T h h'
      induction k with
      | zero => rfl
      | succ k ih => exact (hs (n + k) ⟨T, hle n k T h⟩).trans (ih _)
    have ha_any : ∀ n m T (h : Q n T) (h' : Q m T), a n ⟨T, h⟩ = a m ⟨T, h'⟩ := by
      intro n m T h h'
      rcases le_total n m with hnm | hmn
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        exact (ha_le n k T h h').symm
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact ha_le m k T h' h
    let g : K.M0.c0 := fun T ↦ a (Classical.choose (hex T)) ⟨T, Classical.choose_spec (hex T)⟩
    have hg : ∀ n T (h : Q n T), g T = a n ⟨T, h⟩ := fun n T h ↦ ha_any _ _ _ _ _
    have hgz : K.D0 g = z := by
      refine Prod.ext ?_ ?_
      · funext T T' φ
        obtain ⟨n, h, h'⟩ := hex2 T T'
        have e := congrArg (fun w ↦ w.1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ)) (had n)
        show g T' - K.M0.map φ (g T) = z.1 T T' φ
        rw [hg n T h, hg n T' h']
        exact e
      · funext T
        obtain ⟨n, h⟩ := hex T
        have e := congrArg (fun w ↦ w.2 ⟨T, h⟩) (had n)
        show K.d0 T (g T) = z.2 T
        rw [hg n T h]
        exact e
    change (QuotientAddGroup.mk ⟨z, hz⟩ : K.H1) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨g, hgz⟩
  · intro y
    obtain ⟨⟨z0, hz0⟩, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨b, hb0, hbZ, hbt⟩ := ml.2 (fun n ↦ (K.res (Q n).ι).M0.c0) (fun n ↦ (K.res (Q n).ι).T1)
      (fun n ↦ (K.res (Q n).ι).Z1) (fun n ↦ (K.res (Q n).ι).D0)
      (fun n ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).p0)
      (fun n ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).p1)
      (fun n x ↦ cx_D1_D0_eq_zero _ x)
      (fun n x ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).pullback_firstDifferential x)
      (fun n g ↦ by
        classical
        refine ⟨fun X ↦ if h : Q n X.obj then g ⟨X.obj, h⟩ else 0, ?_⟩
        funext X
        show (if h : Q n X.obj then g ⟨X.obj, h⟩ else 0) = g X
        rw [dif_pos X.property])
      (fun n x hx ↦ (((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).z1 ⟨x, hx⟩).2)
      (fun n b hb ↦ by
        obtain ⟨z, hz, g, e⟩ := exists_cocycle_of_h1_surjective _ (h1b n).2 b hb
        exact ⟨z, hz, g, e⟩)
      z0 hz0
    have hb1 : ∀ j (X Y : (Q j).FullSubcategory) (f : X ⟶ Y),
        (b (j + 1)).1 ⟨X.obj, hQ j _ X.property⟩ ⟨Y.obj, hQ j _ Y.property⟩ (homMk f.hom) = (b j).1 X Y f :=
      fun j X Y f ↦ congrArg (fun w ↦ w.1 X Y f) (hbt j)
    have hb2 : ∀ j (X : (Q j).FullSubcategory), (b (j + 1)).2 ⟨X.obj, hQ j _ X.property⟩ = (b j).2 X :=
      fun j X ↦ congrArg (fun w ↦ w.2 X) (hbt j)
    have hb1_le : ∀ n k T T' (h : Q n T) (h' : Q n T') (h2 : Q (n + k) T) (h2' : Q (n + k) T') (φ : T ⟶ T'),
        (b (n + k)).1 ⟨T, h2⟩ ⟨T', h2'⟩ (homMk φ) = (b n).1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ) := by
      intro n k T T' h h' h2 h2' φ
      induction k with
      | zero => rfl
      | succ k ih => exact (hb1 (n + k) ⟨T, hle n k T h⟩ ⟨T', hle n k T' h'⟩ (homMk φ)).trans (ih _ _)
    have hb2_le : ∀ n k T (h : Q n T) (h2 : Q (n + k) T), (b (n + k)).2 ⟨T, h2⟩ = (b n).2 ⟨T, h⟩ := by
      intro n k T h h2
      induction k with
      | zero => rfl
      | succ k ih => exact (hb2 (n + k) ⟨T, hle n k T h⟩).trans (ih _)
    have hb1_any : ∀ n m T T' (h : Q n T) (h' : Q n T') (h2 : Q m T) (h2' : Q m T') (φ : T ⟶ T'),
        (b n).1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ) = (b m).1 ⟨T, h2⟩ ⟨T', h2'⟩ (homMk φ) := by
      intro n m T T' h h' h2 h2' φ
      rcases le_total n m with hnm | hmn
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        exact (hb1_le n k T T' h h' h2 h2' φ).symm
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact hb1_le m k T T' h2 h2' h h' φ
    have hb2_any : ∀ n m T (h : Q n T) (h2 : Q m T), (b n).2 ⟨T, h⟩ = (b m).2 ⟨T, h2⟩ := by
      intro n m T h h2
      rcases le_total n m with hnm | hmn
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        exact (hb2_le n k T h h2).symm
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact hb2_le m k T h2 h
    let c : K.T1 := (fun T T' φ ↦ (b (Classical.choose (hex2 T T'))).1
        ⟨T, (Classical.choose_spec (hex2 T T')).1⟩ ⟨T', (Classical.choose_spec (hex2 T T')).2⟩ (homMk φ),
      fun T ↦ (b (Classical.choose (hex T))).2 ⟨T, Classical.choose_spec (hex T)⟩)
    have hc1 : ∀ n T T' (h : Q n T) (h' : Q n T') (φ : T ⟶ T'),
        c.1 T T' φ = (b n).1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ) := fun n T T' h h' φ ↦ hb1_any _ _ _ _ _ _ _ _ _
    have hc2 : ∀ n T (h : Q n T), c.2 T = (b n).2 ⟨T, h⟩ := fun n T h ↦ hb2_any _ _ _ _ _
    have hc : c ∈ K.Z1 := by
      show K.D1 c = 0
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext T T' T'' φ ψ
        obtain ⟨n, h, h', h''⟩ := hex3 T T' T''
        have e := congrArg (fun w ↦ w.1 ⟨T, h⟩ ⟨T', h'⟩ ⟨T'', h''⟩ (homMk φ) (homMk ψ))
          (hbZ n : (K.res (Q n).ι).D1 (b n) = 0)
        show K.M0.map ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ = 0
        rw [hc1 n T T' h h', hc1 n T T'' h h'', hc1 n T' T'' h' h'']
        exact e
      · funext T T' φ
        obtain ⟨n, h, h'⟩ := hex2 T T'
        have e := congrArg (fun w ↦ w.2.1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ))
          (hbZ n : (K.res (Q n).ι).D1 (b n) = 0)
        show c.2 T' - K.M1.map φ (c.2 T) - K.d0 T' (c.1 T T' φ) = 0
        rw [hc1 n T T' h h', hc2 n T h, hc2 n T' h']
        exact e
      · funext T
        obtain ⟨n, h⟩ := hex T
        have e := congrArg (fun w ↦ w.2.2 ⟨T, h⟩) (hbZ n : (K.res (Q n).ι).D1 (b n) = 0)
        show K.d1 T (c.2 T) = 0
        rw [hc2 n T h]
        exact e
    refine ⟨QuotientAddGroup.mk ⟨c, hc⟩, ?_⟩
    change (QuotientAddGroup.mk ((K.resMap (Q 0).ι).z1 ⟨c, hc⟩) : (K.res (Q 0).ι).H1) = _
    congr 1
    apply Subtype.ext
    show (K.resMap (Q 0).ι).p1 c = z0
    rw [← hb0]
    refine Prod.ext ?_ ?_
    · funext X Y f
      exact hc1 0 X.obj Y.obj X.property Y.property f.hom
    · funext X
      exact hc2 0 X.obj X.property

end GlobalTheory.CxCoh.TowerOne

namespace GlobalTheory.CxCoh

open ObjectProperty

theorem restriction_h1_bijective_of_exhaustion : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C)
    (P : ℕ → ObjectProperty C) (ℓ : D ⥤ C) (N₀ : ℕ), (∀ m n T, m ≤ n → P m T → P n T) →
    (∀ T, ∃ n, P n T) →
    (∀ N, N₀ ≤ N → ∃ h : ∀ U, P N (ℓ.obj U), ((K.res (P N).ι).resMap ((P N).lift ℓ h)).Bij) →
    Function.Bijective (K.resMap ℓ).h1 := by
  intro C _ D _ K P ℓ N₀ hmono hex hB
  let Q : ℕ → ObjectProperty C := fun n ↦ P (N₀ + n)
  have hQ : ∀ n, Q n ≤ Q (n + 1) := fun n T h ↦ hmono _ _ T (Nat.le_succ _) h
  have hex' : ∀ T, ∃ n, Q n T := fun T ↦
    let ⟨n, h⟩ := hex T
    ⟨n, hmono _ _ T (Nat.le_add_left n N₀) h⟩
  have hB' : ∀ n, ∃ h : ∀ U, Q n (ℓ.obj U), ((K.res (Q n).ι).resMap ((Q n).lift ℓ h)).Bij :=
    fun n ↦ hB (N₀ + n) (Nat.le_add_right _ _)
  choose hl hbij using hB'
  have key : ∀ n, Function.Surjective ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h0 ∧
      Function.Bijective ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h1 := by
    intro n
    have e0 : ∀ c, ((K.res (Q (n + 1)).ι).resMap ((Q (n + 1)).lift ℓ (hl (n + 1)))).h0 c =
        ((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))).h0
          (((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h0 c) :=
      fun c ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).cohomZero_pullback_comp
        ((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))) c
    have e1 : ∀ c, ((K.res (Q (n + 1)).ι).resMap ((Q (n + 1)).lift ℓ (hl (n + 1)))).h1 c =
        ((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))).h1
          (((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h1 c) :=
      fun c ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).cohomOne_pullback_comp
        ((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))) c
    have A0 := (hbij (n + 1)).1
    have B0 := (hbij n).1
    have A1 := (hbij (n + 1)).2.1
    have B1 := (hbij n).2.1
    refine ⟨fun y ↦ ?_, fun a b hab ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨c, hc⟩ := A0.2 (((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))).h0 y)
      exact ⟨c, B0.1 ((e0 c).symm.trans hc)⟩
    · apply A1.1
      rw [e1, e1, hab]
    · obtain ⟨c, hc⟩ := A1.2 (((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))).h1 y)
      exact ⟨c, B1.1 ((e1 c).symm.trans hc)⟩
  have e : ⇑(K.resMap ℓ).h1 =
      ((K.res (Q 0).ι).resMap ((Q 0).lift ℓ (hl 0))).h1 ∘ (K.resMap (Q 0).ι).h1 :=
    funext fun c ↦ (K.resMap (Q 0).ι).cohomOne_pullback_comp ((K.res (Q 0).ι).resMap ((Q 0).lift ℓ (hl 0))) c
  rw [e]
  exact (hbij 0).2.1.comp
    (TowerOne.tower K Q hQ hex' (fun n ↦ (key n).1) (fun n ↦ (key n).2))

end GlobalTheory.CxCoh
