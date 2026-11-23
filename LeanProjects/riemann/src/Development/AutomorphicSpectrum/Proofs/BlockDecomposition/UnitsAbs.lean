import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernComparison

open CrystallineSemistableComparison.CH

universe w w' u v u' v' u'' v''

section Coh
variable {R : Type} [CommRing R] {Th : Type u} [Category.{v} Th] {Ec : Type u'} [Category.{v'} Ec]
  {C : Type u''} [Category.{v''} C]

theorem pull_transport (F : Th ⥤ ModuleCat.{w} R) (F' : Ec ⥤ ModuleCat.{w'} R) (m : Mor F F' (RingHom.id R)) (G : C ⥤ Ec)
    (x : H F 2) (c : Cn ((G ⋙ m.G) ⋙ F) 2) (hc : d _ 2 c = 0)
    (h : (cx _).cls c hc = (Mor.restrict F (G ⋙ m.G)).pull 2 x) :
    ∃ hz : d (G ⋙ F') 2 (fun s => m.τ _ (c s)) = 0,
      (cx _).cls _ hz = (Mor.restrict F' G).pull 2 (m.pull 2 x) := by
  let m' : Mor ((G ⋙ m.G) ⋙ F) (G ⋙ F') (RingHom.id R) :=
    ⟨𝟭 _, fun T => m.τ (G.obj T), fun φ x => m.nat (G.map φ) x⟩
  have hz : d (G ⋙ F') 2 (fun s => m.τ _ (c s)) = 0 := by
    have := m'.d_pullC 2 c
    rw [hc, map_zero] at this
    exact this
  refine ⟨hz, ?_⟩
  have e1 := CrystallineSemistableComparison.P.mapH_cls m'.hom 2 c hc hz
  have e2 : (Mor.restrict F' G).pull 2 (m.pull 2 x) = m'.pull 2 ((Mor.restrict F (G ⋙ m.G)).pull 2 x) := by
    have a := (CrystallineSemistableComparison.P.pull_comp m (Mor.restrict F' G) 2 x).1
    have b := (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F (G ⋙ m.G)) m' 2 x).1
    exact a.symm.trans b
  rw [e2, ← h]
  exact e1.symm

end Coh

section Line
variable {X : Scheme.{0}}

theorem gamma_nat {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom y) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) :=
  congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem u_map (D : E.LineData X) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (a b : Spec (CommRingCat.of A) ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f) (a' b' : Spec (CommRingCat.of B) ⟶ D.Y)
    (ha : a' = Spec.map (CommRingCat.ofHom f) ≫ a) (hb : b' = Spec.map (CommRingCat.ofHom f) ≫ b)
    (h' : a' ≫ D.f = b' ≫ D.f) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (D.u a' b' h') =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (D.u a b h)) := by
  subst ha hb
  rw [D.nat (Spec.map (CommRingCat.ofHom f)) a b h, ← gamma_nat]
  rfl

theorem u_coc (D : E.LineData X) {U₀ U₁ U₂ : Type} [CommRing U₀] [CommRing U₁] [CommRing U₂]
    (f₁ : U₀ →+* U₁) (f₂ : U₁ →+* U₂) (f₃ : U₀ →+* U₂) (hf : f₃ = f₂.comp f₁)
    (p₀ : Spec (CommRingCat.of U₀) ⟶ D.Y) (p₁ : Spec (CommRingCat.of U₁) ⟶ D.Y) (p₂ : Spec (CommRingCat.of U₂) ⟶ D.Y)
    (h₁ : (Spec.map (CommRingCat.ofHom f₁) ≫ p₀) ≫ D.f = p₁ ≫ D.f)
    (h₂ : (Spec.map (CommRingCat.ofHom f₂) ≫ p₁) ≫ D.f = p₂ ≫ D.f)
    (h₃ : (Spec.map (CommRingCat.ofHom f₃) ≫ p₀) ≫ D.f = p₂ ≫ D.f) :
    f₂ ((Scheme.ΓSpecIso (CommRingCat.of U₁)).hom.hom (D.u _ _ h₁)) *
      (Scheme.ΓSpecIso (CommRingCat.of U₂)).hom.hom (D.u _ _ h₂) =
      (Scheme.ΓSpecIso (CommRingCat.of U₂)).hom.hom (D.u _ _ h₃) := by
  subst hf
  have e : Spec.map (CommRingCat.ofHom (f₂.comp f₁)) = Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have h12 : (Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) ≫ p₀) ≫ D.f =
      (Spec.map (CommRingCat.ofHom f₂) ≫ p₁) ≫ D.f := by
    simpa only [Category.assoc] using congrArg (Spec.map (CommRingCat.ofHom f₂) ≫ ·) h₁
  have A := u_map D f₂ _ _ h₁ _ _ rfl rfl h12
  have c := D.coc _ _ _ h12 h₂
  have e3 : ∀ (a : Spec (CommRingCat.of U₂) ⟶ D.Y) (ha : a = Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) ≫ p₀)
      (hh : a ≫ D.f = p₂ ≫ D.f), D.u a p₂ hh = D.u _ p₂ (h12.trans h₂) := by
    intro a ha hh; subst ha; rfl
  rw [← A, ← map_mul, ← Units.val_mul, c, e3 _ (by rw [e, Category.assoc]) h₃]

theorem u_square (D : E.LineData X) {U U' Q Q' : Type} [CommRing U] [CommRing U'] [CommRing Q] [CommRing Q']
    (m : U →+* U') (g : U →+* Q) (g' : U' →+* Q') (t : Q →+* Q') (comm : t.comp g = g'.comp m)
    (pT : Spec (CommRingCat.of U) ⟶ D.Y) (pT' : Spec (CommRingCat.of U') ⟶ D.Y)
    (h' : (Spec.map (CommRingCat.ofHom m) ≫ pT) ≫ D.f = pT' ≫ D.f)
    (h : (Spec.map (CommRingCat.ofHom t) ≫ Spec.map (CommRingCat.ofHom g) ≫ pT) ≫ D.f =
      (Spec.map (CommRingCat.ofHom g') ≫ pT') ≫ D.f) :
    (Scheme.ΓSpecIso (CommRingCat.of Q')).hom.hom (D.u _ _ h) =
      g' ((Scheme.ΓSpecIso (CommRingCat.of U')).hom.hom (D.u _ _ h')) := by
  refine u_map D g' _ _ h' _ _ ?_ rfl h
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, comm]

end Line

section Log
variable {l : ℕ} [Fact l.Prime]

theorem dxi_mem (k : Bool) (A : PAlg l) (n : ℕ) : A.dxi n 1 ∈ JJ k A n :=
  fil_le k A n (Ideal.subset_span ⟨1, le_rfl, rfl⟩)

theorem dd_dxi (k : Bool) (A : PAlg l) (n m : ℕ) : (DD k A n).dpow m (A.dxi n 1) = A.dxi n m := by
  cases k
  · exact A.dpow_dxi n m
  · have h := (A.dp_fil_pfil n).2 (A.dxi n 1) (Ideal.subset_span ⟨1, le_rfl, rfl⟩) (n := m)
    exact h.trans (A.dpow_dxi n m)

theorem isLog_dlog (k : Bool) (A : PAlg l) (n : ℕ) (u : A.A) (hu : A.sharp u = 1) (v : A.Acr n)
    (hv : v = A.toAcr n (WittVector.teichmuller l u)) :
    E.IsLog A n (WittVector.teichmuller l u) (dlog (DD k A n) (l * n) v) := by
  have h1 : WittVector.teichmuller l u - 1 ∈ Ideal.span {A.xi} := by
    have h0 : A.th (WittVector.teichmuller l u - 1) = 0 := by
      rw [map_sub, map_one]; exact sub_eq_zero.2 hu
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  refine ⟨fun m => algebraMap A.W A.Acr0 c ^ m * A.dxi0 m, fun m => ?_, ?_⟩
  · rw [← hc]
    change algebraMap A.W (Localization.Away (l : A.W)) c ^ m * dpw m A.xi = dpw m (c * A.xi)
    simp only [dpw, map_mul, mul_pow]; ring
  · have hd : v - 1 = A.toAcr n c * A.dxi n 1 := by
      rw [hv, ← toAcr_xi, ← map_mul, hc, map_sub, map_one]
    simp only [dlog, hd]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [DividedPowers.dpow_mul _ (dxi_mem k A n), dd_dxi, map_mul, map_pow]
    rfl

end Log

section Pts
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X}

theorem pt_hom {T T' : C} (φ : T ⟶ T') :
    Spec.map (CommRingCat.ofHom (mapU (G.map φ).1.hom)) ≫ (G.obj T).2.1 = (G.obj T').2.1 :=
  congrArg Subtype.val (G.map φ).2

theorem lift_h (Λ : E.Lift G D) {T T' : C} (φ : T ⟶ T') :
    (Spec.map (CommRingCat.ofHom (mapU (G.map φ).1.hom)) ≫ Λ.p T) ≫ D.f = Λ.p T' ≫ D.f := by
  rw [Category.assoc, Λ.hp, Λ.hp]; exact pt_hom φ

theorem mapU_sharp' {A A' : PAlg l} (f : A ⟶ A') (a : A.A) : mapU f (A.sharp a) = A'.sharp (PAlg.Hom.f f a) := by
  change A'.th (mapW f (WittVector.teichmuller l a)) = _
  rw [mapW, WittVector.map_teichmuller]
  rfl

theorem sharp_r (Λ : E.Lift G D) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) (hc : c = a ≫ b) :
    (G.obj c₂).1.obj.sharp ((Units.map (PAlg.Hom.f (G.map b).1.hom).toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹ :
      ((G.obj c₂).1.obj.A)ˣ) : (G.obj c₂).1.obj.A) = 1 := by
  subst hc
  have wa := Λ.hw a (lift_h Λ a)
  have wb := Λ.hw b (lift_h Λ b)
  have wc := Λ.hw (a ≫ b) (lift_h Λ (a ≫ b))
  have key := u_coc D (mapU (G.map a).1.hom) (mapU (G.map b).1.hom) (mapU (G.map (a ≫ b)).1.hom)
    (by rw [G.map_comp]; exact mapU_comp _ _) (Λ.p c₀) (Λ.p c₁) (Λ.p c₂) (lift_h Λ a) (lift_h Λ b) (lift_h Λ (a ≫ b))
  rw [← wa, ← wb, ← wc, mapU_sharp', ← map_mul] at key
  rw [Units.val_mul, Units.val_mul, map_mul]
  change (G.obj c₂).1.obj.sharp (PAlg.Hom.f (G.map b).1.hom (Λ.w a) * Λ.w b) * _ = 1
  rw [key, ← map_mul, Units.mul_inv, map_one]

end Pts

section Main
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X}

def tm (A : PAlg l) (n : ℕ) : A.A →* A.Acr n :=
  (A.toAcr n).toMonoidHom.comp (WittVector.teichmuller l)

variable (k : Bool) (n : ℕ)

abbrev gG (G : C ⥤ El (PX q κ)) : C ⥤ Thick (Lc (schFn q) κ k n) := G ⋙ gT (schFn q) κ k n

def lam (Λ : E.Lift G D) : CLift (gG k n G) D where
  p T := Spec.map (CommRingCat.ofHom (uJ k (G.obj T).1.obj n)) ≫ Λ.p T
  hp T := by
    rw [Category.assoc, Λ.hp]
    rfl
  w {T T'} φ := Units.map (tm (G.obj T').1.obj n) (Λ.w φ)
  hw {T T'} φ h := by
    have e := u_square D (mapU (G.map φ).1.hom) (uJ k (G.obj T).1.obj n) (uJ k (G.obj T').1.obj n)
      (Ideal.quotientMap _ (mapAcr (G.map φ).1.hom n) (jj_le k (G.map φ).1.hom n)) (uJ_map k (G.map φ).1.hom n)
      (Λ.p T) (Λ.p T') (lift_h Λ φ) h
    refine Eq.trans ?_ e.symm
    rw [← Λ.hw φ (lift_h Λ φ)]
    exact uJ_th k _ n (WittVector.teichmuller l (Λ.w φ).val) |>.symm

theorem units_abs {A₁ A₂ B₁ B₂ : Type} [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂] (t₁ : A₁ →* B₁) (t₂ : A₂ →* B₂)
    (f : A₁ →+* A₂) (g : B₁ →+* B₂) (h : ∀ x, g (t₁ x) = t₂ (f x)) (wa : A₁ˣ) (wb wc : A₂ˣ) :
    Units.map g.toMonoidHom (Units.map t₁ wa) * Units.map t₂ wb * (Units.map t₂ wc)⁻¹ =
      Units.map t₂ (Units.map f.toMonoidHom wa * wb * wc⁻¹) := by
  rw [map_mul, map_mul, map_inv]
  congr 2
  exact Units.ext (h _)

theorem tm_map {A A' : PAlg l} (f : A ⟶ A') (x : A.A) : mapAcr f n (tm A n x) = tm A' n (PAlg.Hom.f f x) := by
  change mapAcr f n (A.toAcr n (WittVector.teichmuller l x)) = A'.toAcr n (WittVector.teichmuller l (PAlg.Hom.f f x))
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller]

theorem lam_r' (Λ : E.Lift G D) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) :
    Units.map ((gG k n G).map b).φ.toMonoidHom ((lam k n Λ).w a) * (lam k n Λ).w b * ((lam k n Λ).w c)⁻¹ =
      Units.map (tm (G.obj c₂).1.obj n) (Units.map (PAlg.Hom.f (G.map b).1.hom).toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹) :=
  units_abs (tm (G.obj c₁).1.obj n) (tm (G.obj c₂).1.obj n) (PAlg.Hom.f (G.map b).1.hom) (mapAcr (G.map b).1.hom n)
    (tm_map n (G.map b).1.hom) (Λ.w a) (Λ.w b) (Λ.w c)

theorem lam_r (Λ : E.Lift G D) (s : ComposableArrows C 2) :
    ((lam k n Λ).r s).val = (G.obj (s.obj (Fin.last 2))).1.obj.toAcr n (WittVector.teichmuller l (Λ.r s).val) :=
  congrArg Units.val (lam_r' k n Λ (s.map' 0 1) (s.map' 1 2) (s.map' 0 2))

end Main

end GlobalTheory.CompanionTheory.FirstChernComparison
