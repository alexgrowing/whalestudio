import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.VertQ

universe a b

theorem D0_eq_iff {C' : Type b} [Category.{0} C'] (L : Cx C') (g : L.M0.c0) (c : L.T1) :
    L.D0 g = c ↔ (∀ T T' (φ : T ⟶ T'), g T' - L.M0.map φ (g T) = c.1 T T' φ) ∧
      ∀ T, L.d0 T (g T) = c.2 T := by
  constructor
  · rintro rfl; exact ⟨fun _ _ _ => rfl, fun _ => rfl⟩
  · rintro ⟨h1, h2⟩
    refine Prod.ext ?_ ?_
    · funext T T' φ; exact h1 T T' φ
    · funext T; exact h2 T

theorem components_of_D0_eq_zero {C' : Type b} [Category.{0} C'] (L : Cx C') (g : L.M0.c0) (h : L.D0 g = 0) :
    (∀ T T' (φ : T ⟶ T'), g T' - L.M0.map φ (g T) = 0) ∧ ∀ T, L.d0 T (g T) = 0 :=
  (D0_eq_iff L g 0).1 h

theorem D0_eq_zero_of_compat_of_d0_eq_zero {C' : Type b} [Category.{0} C'] (L : Cx C') (g : L.M0.c0)
    (h1 : ∀ T T' (φ : T ⟶ T'), g T' - L.M0.map φ (g T) = 0) (h2 : ∀ T, L.d0 T (g T) = 0) :
    L.D0 g = 0 :=
  (D0_eq_iff L g 0).2 ⟨h1, h2⟩

theorem components_of_D1_eq_zero {C' : Type b} [Category.{0} C'] (L : Cx C') (c : L.T1) (h : L.D1 c = 0) :
    (∀ T T' (φ : T ⟶ T'), c.2 T' - L.M1.map φ (c.2 T) - L.d0 T' (c.1 T T' φ) = 0) ∧
      ∀ T, L.d1 T (c.2 T) = 0 := by
  refine ⟨fun T T' φ => ?_, fun T => ?_⟩
  · have := congrFun (congrFun (congrFun (congrArg (fun x => x.2.1) h) T) T') φ
    exact this
  · have := congrFun (congrArg (fun x => x.2.2) h) T
    exact this

variable {C : Type a} [Category.{0} C] {C' : Type b} [Category.{0} C']

theorem vertical_h0_injective {K : Cx C} {K' : Cx C'} (m : CxMap K K') (hq : m.QAll) :
    Function.Injective m.vert.h0 := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨g, hg⟩ h
  have hg' := components_of_D0_eq_zero _ g (AddMonoidHom.mem_ker.1 hg)
  apply Subtype.ext
  funext T
  have hT : m.a0 T (g T) = 0 := congrFun (congrArg Subtype.val h) T
  exact (hq T).inj0 _ (hg'.2 T) hT

theorem vertical_h0_surjective {K : Cx C} {K' : Cx C'} (m : CxMap K K') (hq : m.QAll) :
    Function.Surjective m.vert.h0 := by
  rintro ⟨y, hy⟩
  have hy' := components_of_D0_eq_zero K' y (AddMonoidHom.mem_ker.1 hy)
  choose x hx0 hxa using fun T => (hq T).surj0 (y T) (hy'.2 T)
  refine ⟨⟨x, AddMonoidHom.mem_ker.2 (D0_eq_zero_of_compat_of_d0_eq_zero (K.res m.G) x (fun T T' φ => ?_) hx0)⟩, Subtype.ext (funext hxa)⟩
  show x T' - K.M0.map (m.G.map φ) (x T) = 0
  apply (hq T').inj0
  · rw [map_sub, hx0 T', K.diffZero_natural, hx0 T, map_zero, sub_zero]
  · rw [map_sub, hxa T', m.compDegreeZero_natural, hxa T]
    exact hy'.1 T T' φ

theorem vertical_h1_injective {K : Cx C} {K' : Cx C'} (m : CxMap K K') (hq : m.QAll) :
    Function.Injective m.vert.h1 := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨⟨⟨f, ω⟩, hfω⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [CxMap.h1, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf] at hc
  obtain ⟨g', hg'⟩ := hc
  have hg'' := (D0_eq_iff K' g' _).1 hg'
  have hc1 := components_of_D1_eq_zero _ _ (AddMonoidHom.mem_ker.1 hfω)
  have e0 : ∀ T, K'.d0 T (g' T) = m.a1 T (ω T) := fun T => hg''.2 T
  have e3 : ∀ T T' (φ : T ⟶ T'), m.a0 T' (f T T' φ) = g' T' - K'.M0.map φ (g' T) :=
    fun T T' φ => (hg''.1 T T' φ).symm
  have hc1a : ∀ T T' (φ : T ⟶ T'), ω T' - K.M1.map (m.G.map φ) (ω T) - K.d0 _ (f T T' φ) = 0 :=
    hc1.1
  choose w hw using fun T => (hq T).inj1 (ω T) (g' T) (hc1.2 T) (e0 T).symm
  choose u hu0 hua using fun T => (hq T).surj0 (g' T - m.a0 T (w T))
    (by rw [map_sub, e0 T, ← m.comp_commutes_diffZero, hw T, sub_self])
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  refine ⟨fun T => w T + u T, (D0_eq_iff _ _ _).2 ⟨fun T T' φ => ?_, fun T => ?_⟩⟩
  · show w T' + u T' - K.M0.map (m.G.map φ) (w T + u T) = f T T' φ
    rw [← sub_eq_zero]
    apply (hq T').inj0
    · rw [map_sub, map_sub, K.diffZero_natural, map_add, map_add, hw, hw, hu0, hu0, add_zero, add_zero]
      exact hc1a T T' φ
    · have e1 : m.a0 T' (w T' + u T') = g' T' := by rw [map_add, hua]; abel
      have e2 : m.a0 T' (K.M0.map (m.G.map φ) (w T + u T)) = K'.M0.map φ (g' T) := by
        rw [m.compDegreeZero_natural, map_add, hua, add_sub_cancel]
      rw [map_sub, map_sub, e1, e2, e3]
      abel
  · show K.d0 _ (w T + u T) = ω T
    rw [map_add, hw, hu0, add_zero]

theorem main : VertHas.{a,b} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) :=
  fun m hq => ⟨⟨vertical_h0_injective m hq, vertical_h0_surjective m hq⟩, vertical_h1_injective m hq⟩

end GlobalTheory.CxCoh.VertQ

theorem GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 :
    VertHas.{1,1} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧
    VertHas.{1,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧
    VertHas.{0,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) :=
  ⟨VertQ.main.{1,1}, VertQ.main.{1,0}, VertQ.main.{0,0}⟩
