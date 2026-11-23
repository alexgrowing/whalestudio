import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtaleChernClass

open GlobalTheory.CatH (face toLast)

universe w

section Cochains

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{w} R)

theorem d_zero_apply (f : Cn F 0) (s : ComposableArrows C 1) :
    d F 0 f s = (show F.obj (s.obj (Fin.last 1)) from f (face 0 s)) - (show F.obj (s.obj (Fin.last 1)) from (F.map (s.map' 0 1)).hom (f (face 1 s))) := by
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_two]
  have e0 : toLast (0 : Fin 2) s = 𝟙 _ := s.map_id _
  have e1 : toLast (1 : Fin 2) s = s.map' 0 1 := rfl
  rw [e0, e1, F.map_id]
  simp [sub_eq_add_neg]
  rfl

theorem d_one_apply (f : Cn F 1) (s : ComposableArrows C 2) :
    d F 1 f s = (show F.obj (s.obj (Fin.last 2)) from f (face 0 s)) - (show F.obj (s.obj (Fin.last 2)) from f (face 1 s)) +
      (show F.obj (s.obj (Fin.last 2)) from (F.map (s.map' 1 2)).hom (f (face 2 s))) := by
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_three]
  have e0 : toLast (0 : Fin 3) s = 𝟙 _ := s.map_id _
  have e1 : toLast (1 : Fin 3) s = 𝟙 _ := s.map_id _
  have e2 : toLast (2 : Fin 3) s = s.map' 1 2 := rfl
  rw [e0, e1, e2, F.map_id]
  simp [sub_eq_add_neg]
  rfl

end Cochains

theorem close_sum {M : Type*} [AddCommGroup M] (tce tbe tbc kv kw ku kvw i : M)
    (h₁ : tce - tbe + tbc = kv + kw - kvw) (h₂ : kvw = ku + i) :
    (-1 : ℤ) ^ 1 • ((tce - kw) - (tbe - ku) + (tbc - kv)) = i := by
  have e : tce = kv + kw - kvw + tbe - tbc := by rw [← h₁]; abel
  rw [e, h₂]
  simp only [pow_one, neg_smul, one_smul]
  abel

theorem u_congr {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) (ha : a = a') (hb : b = b') :
    D.u a b h = D.u a' b' h' := by
  subst ha hb; rfl

theorem etale_chern_class_eq_kummer_class : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.ResGood → CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.FirstChernCoboundary → CrystallineSemistableComparison.E.KumPow →
    CrystallineSemistableComparison.E.EtaleFirstChernKummer := by
  intro hES hRG hSC hCP hKP hGen hKum hC1 q _ C _ P X Y D L hL hInv x hx z Λ
  obtain ⟨a, η, θ, hRep, hηn, hθn, hdη, hdiff, hcoc⟩ := hCP hC1 q X D L hL hInv x hx
  have hθc : ∀ (V : Scheme.{0}) (b b' c : V ⟶ D.Y) (h : b ≫ D.f = c ≫ D.f) (h' : b' ≫ D.f = c ≫ D.f),
      b = b' → θ V b c h = θ V b' c h' := by
    intro V b b' c h h' e
    subst e
    rfl
  have hG : (P.res 1).Good := hRG hGen q C P 1
  obtain ⟨hιd, hdd, hinj, -, -⟩ := hSC ℤ C P.L (P.res 1) hG
  have hpp : ∀ {c c' : C} (φ : c ⟶ c'), ((P.S.map φ).unop ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    intro c c' φ
    rw [Category.assoc, Λ.hp, Λ.hp, Y.nat]
  let A₀ : ∀ {c c' : C} (φ : c ⟶ c'), Sec ((res _ (tw q 1)).X 0) (P.U c') := fun {c c'} φ =>
    θ _ ((P.S.map φ).unop ≫ Λ.p c) (Λ.p c') (hpp φ) - kumT q _ (Λ.r φ)
  let a₁ : Cn ((P.res 1).K 1) 0 := fun s => η _ (Λ.p (s.obj 0))
  let a₀ : Cn ((P.res 1).K 0) 1 := fun s => A₀ (s.map' 0 1)
  have h1 : (P.res 1).dvC 1 0 a₁ = Y.glob 1 2 a := by
    funext s
    refine (hdη _ (Λ.p (s.obj 0))).trans ?_
    rw [Λ.hp]
    rfl
  have h2 : (-1 : ℤ) ^ 0 • d ((P.res 1).K 1) 0 a₁ = (P.res 1).dvC 0 1 a₀ := by
    funext s
    rw [pow_zero, one_smul, d_zero_apply]
    have e := hdiff _ ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) (Λ.p (s.obj 1)) (hpp (s.map' 0 1)) _ (Λ.hr _)
    rw [← hηn] at e
    exact e
  have h3 : (-1 : ℤ) ^ 1 • d ((P.res 1).K 0) 1 a₀ = (P.res 1).ιC 2 z := by
    funext s
    rw [Pi.smul_apply, d_one_apply]
    let g := (P.S.map (s.map' 1 2)).unop
    have hg : g ≫ (P.S.map (s.map' 0 1)).unop = (P.S.map (s.map' 0 2)).unop := by
      have e : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map_comp _ _
      rw [e, P.S.map_comp, unop_comp]
    have hb : g ≫ (P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0) =
        (P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0) := by
      rw [← Category.assoc, hg]
    have hbc' : (g ≫ (P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = (g ≫ Λ.p (s.obj 1)) ≫ D.f := by
      have e : ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = Λ.p (s.obj 1) ≫ D.f := hpp (s.map' 0 1)
      rw [Category.assoc g, e, Category.assoc]
    have hbc : ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = (g ≫ Λ.p (s.obj 1)) ≫ D.f := by
      rw [← hb]
      exact hbc'
    let v := Units.map g.appTop.hom.toMonoidHom (Λ.r (s.map' 0 1))
    let w := Λ.r (s.map' 1 2)
    let u := Λ.r (s.map' 0 2)
    have hv : v ^ q = D.u _ _ hbc := by
      change Units.map g.appTop.hom.toMonoidHom (Λ.r (s.map' 0 1)) ^ q = _
      rw [← map_pow, Λ.hr, ← D.nat]
      exact u_congr D _ _ hb rfl
    have hw : w ^ q = D.u (g ≫ Λ.p (s.obj 1)) (Λ.p (s.obj 2)) (hpp (s.map' 1 2)) := Λ.hr _
    have hc := hcoc _ _ _ _ hbc (hpp (s.map' 1 2)) v w hv hw
    have hk := hKP hKum q _ (P.ζ (s.obj (Fin.last 2))) (z s) (v * w * u⁻¹) u (Λ.hz s)
    rw [inv_mul_cancel_right] at hk
    have hn : ((((P.res 1).K 0).map (s.map' 1 2)).hom (a₀ (face 2 s))) =
        θ _ ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) (g ≫ Λ.p (s.obj 1)) hbc - kumT q _ v := by
      have t₁ : Sec.res g (θ _ ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) (Λ.p (s.obj 1)) (hpp (s.map' 0 1))) =
          θ _ ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) (g ≫ Λ.p (s.obj 1)) hbc :=
        (hθn _ _ g _ _ _ hbc').trans (hθc _ _ _ _ _ _ hb)
      have t₂ : Sec.res g (kumT q _ (Λ.r (s.map' 0 1))) = kumT q _ v := (hKum q).1 _ _ g _ (P.ζ _).2.1
      exact (map_sub _ _ _).trans (congrArg₂ (· - ·) t₁ t₂)
    rw [hn]
    exact close_sum _ _ _ _ _ _ _ _ hc hk
  have hSt : (P.res 1).St z 2 0 (Y.glob 1 2 a) := ⟨a₁, h1, a₀, h2.symm, rfl, h3.symm⟩
  have hz : d P.L 2 z = 0 := by
    apply hinj 3
    rw [map_zero, ← hιd, ← h3, map_smul, d_d, smul_zero]
  exact ⟨hz, ((hES hGen q C P X Y 1 2 x).2 _ ⟨a, hRep, z, hz, hSt, rfl⟩).symm⟩

end GlobalTheory.CompanionTheory.EtaleChernClass
