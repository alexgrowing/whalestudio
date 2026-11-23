import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeMapFApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfProd
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanOne

variable {T : Type 1} [Category.{0} T]

lemma nat_el {C D : T ⥤ AbCx} (φ : C ⟶ D) {U V : T} (g : U ⟶ V) (n : ℤ) (c : (C.obj U).X n) :
    (φ.app V).f n ((C.map g).f n c) = (D.map g).f n ((φ.app U).f n c) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, φ.naturality]

lemma comm_el {A B : AbCx} (f : A ⟶ B) (n m : ℤ) (a : A.X n) : f.f m (A.d n m a) = B.d n m (f.f n a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, f.comm]

lemma map_comp_el (C : T ⥤ AbCx) {U V W : T} (g : U ⟶ V) (h : V ⟶ W) (n : ℤ) (c : (C.obj U).X n) :
    (C.map (g ≫ h)).f n c = (C.map h).f n ((C.map g).f n c) := by
  rw [Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

lemma hom_zero' {A B : AddCommGrpCat.{1}} (f : A ⟶ B) : f (0 : A) = 0 := map_zero f.hom

lemma locInj' {Cov : MorphismProperty T} {C D : T ⥤ AbCx} {φ : C ⟶ D} (h : LocInj Cov φ) (k m : ℤ) (hk : k + 1 = m)
    (U : T) (c : (C.obj U).X m) (hc : (C.obj U).d m (m + 1) c = 0)
    (hy : ∃ y : (D.obj U).X k, (φ.app U).f m c = (D.obj U).d k m y) :
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ b : (C.obj V).X k, (C.obj V).d k m b = (C.map g).f m c := by
  obtain rfl : k = m - 1 := by omega
  exact h m U c hc hy

lemma locSurj' {Cov : MorphismProperty T} {C D : T ⥤ AbCx} {φ : C ⟶ D} (h : LocSurj Cov φ) (k n : ℤ) (hk : k + 1 = n)
    (U : T) (z : (D.obj U).X n) (hz : (D.obj U).d n (n + 1) z = 0) :
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ (c : (C.obj V).X n) (y : (D.obj V).X k), (C.obj V).d n (n + 1) c = 0 ∧
      (φ.app V).f n c = (D.map g).f n z + (D.obj V).d k n y := by
  obtain rfl : k = n - 1 := by omega
  exact h n U z hz

theorem cartan_one : ∀ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition]
    (C D : T ⥤ AbCx) (φ : C ⟶ D), (∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n) ∧ IsZero ((D.obj U).X n)) →
    Refines Cov (fun U X a => ∀ n, WExact (term C n) a ∧ WExact (term D n) a) → LocSurj Cov φ → LocInj Cov φ →
    ∀ U, SurjH (φ.app U) ∧ InjH (φ.app U) := by
  intro T _ Cov _ C D φ hb hR hS hI
  obtain ⟨K, p, q, hbij, hd⟩ := GlobalTheory.EtC.coneEl_exists T C D φ
  have ext : ∀ n U (x y : (K.obj U).X n), (p n).app U x = (p n).app U y → (q n).app U x = (q n).app U y → x = y :=
    fun n U x y h1 h2 => (hbij n U).1 (Prod.ext h1 h2)
  have mk : ∀ n U (c : (C.obj U).X (n + 1)) (z : (D.obj U).X n), ∃ x : (K.obj U).X n, (p n).app U x = c ∧ (q n).app U x = z := by
    intro n U c z
    obtain ⟨x, hx⟩ := (hbij n U).2 (c, z)
    exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  have dp := fun n U x => (hd n U x).1
  have dq := fun n U x => (hd n U x).2
  have natP : ∀ n {U V : T} (g : U ⟶ V) (x : (K.obj U).X n),
      (p n).app V ((K.map g).f n x) = (C.map g).f (n + 1) ((p n).app U x) :=
    fun n _ _ g x => NatTrans.naturality_apply (p n) g x
  have natQ : ∀ n {U V : T} (g : U ⟶ V) (x : (K.obj U).X n),
      (q n).app V ((K.map g).f n x) = (D.map g).f n ((q n).app U x) :=
    fun n _ _ g x => NatTrans.naturality_apply (q n) g x
  have cyc : ∀ n U (x : (K.obj U).X n), (C.obj U).d (n + 1) (n + 1 + 1) ((p n).app U x) = 0 →
      (φ.app U).f (n + 1) ((p n).app U x) + (D.obj U).d n (n + 1) ((q n).app U x) = 0 →
      (K.obj U).d n (n + 1) x = 0 := by
    intro n U x h1 h2
    apply ext
    · rw [dp, h1, neg_zero]; exact (hom_zero' _).symm
    · rw [dq, h2]; exact (hom_zero' _).symm

  have hbK : ∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((K.obj U).X n) := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨b - 1, fun n hn U => ?_⟩
    have h1 := AddCommGrpCat.subsingleton_of_isZero (hb (n + 1) (by omega) U).1
    have h2 := AddCommGrpCat.subsingleton_of_isZero (hb n (by omega) U).2
    haveI : Subsingleton ((K.obj U).X n) :=
      ⟨fun x y => ext n U x y (@Subsingleton.elim _ h1 _ _) (@Subsingleton.elim _ h2 _ _)⟩
    exact AddCommGrpCat.isZero_of_subsingleton _

  have hRK : Refines Cov (fun U X a => ∀ n, WExact (term K n) a) := by
    intro U V g hg
    obtain ⟨X, a, h, hga, hQ⟩ := hR U V g hg
    refine ⟨X, a, h, hga, fun n => ?_⟩
    refine GlobalTheory.EtC.WExactProd.wexact_of_prod T U X a Bool (fun i => cond i (term C (n + 1)) (term D n)) (term K n)
      (fun i => match i with | true => p n | false => q n) ?_ ?_
    · intro W
      constructor
      · intro x y hxy
        exact ext n W x y (congrFun hxy true) (congrFun hxy false)
      · intro f
        obtain ⟨x, hx1, hx2⟩ := mk n W (f true) (f false)
        refine ⟨x, funext fun i => ?_⟩
        cases i
        · exact hx2
        · exact hx1
    · intro i
      cases i
      · exact (hQ n).2
      · exact (hQ (n + 1)).1

  have gen : ∀ (j : ℤ) (U : T) (x : (K.obj U).X (j + 1)), (K.obj U).d (j + 1) (j + 1 + 1) x = 0 →
      ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (K.obj V).X j, (K.obj V).d j (j + 1) y = (K.map g).f (j + 1) x := by
    intro j U x hx
    obtain ⟨c, hc⟩ : ∃ c : (C.obj U).X (j + 1 + 1), (p (j + 1)).app U x = c := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : (D.obj U).X (j + 1), (q (j + 1)).app U x = z := ⟨_, rfl⟩
    have h1 : (C.obj U).d (j + 1 + 1) (j + 1 + 1 + 1) c = 0 := by
      have := dp (j + 1) U x
      rw [hx] at this
      erw [hom_zero'] at this
      rw [hc] at this
      exact neg_eq_zero.mp this.symm
    have h2 : (D.obj U).d (j + 1) (j + 1 + 1) z + (φ.app U).f (j + 1 + 1) c = 0 := by
      have := dq (j + 1) U x
      rw [hx] at this
      erw [hom_zero'] at this
      rw [hc, hz] at this
      exact (add_comm _ _).trans this.symm
    obtain ⟨V₁, g₁, hg₁, b, hb⟩ := locInj' hI (j + 1) (j + 1 + 1) rfl U c h1
      ⟨-z, by rw [map_neg]; exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h2)⟩
    obtain ⟨w, hw⟩ : ∃ w : (D.obj V₁).X (j + 1), (D.map g₁).f (j + 1) z + (φ.app V₁).f (j + 1) b = w := ⟨_, rfl⟩
    have hw0 : (D.obj V₁).d (j + 1) (j + 1 + 1) w = 0 := by
      rw [← hw, map_add, ← comm_el (D.map g₁), ← comm_el (φ.app V₁), hb, nat_el, ← map_add, h2, map_zero]
    obtain ⟨V₂, g₂, hg₂, c', y', hc', hy'⟩ := locSurj' hS j (j + 1) rfl V₁ w hw0
    obtain ⟨y, hyp, hyq⟩ := mk j V₂ (c' - (C.map g₂).f (j + 1) b) (-y')
    refine ⟨V₂, g₁ ≫ g₂, Cov.comp_mem _ _ hg₁ hg₂, y, ?_⟩
    apply ext
    · rw [dp, hyp, natP, hc, map_sub, hc', ← comm_el (C.map g₂), hb, map_comp_el, zero_sub, neg_neg]
    · rw [dq, hyp, hyq, natQ, hz, map_sub, map_neg, hy', ← hw, map_add, nat_el, map_comp_el]
      abel
  have hLK : LocExact Cov K := by
    have gen' : ∀ k n : ℤ, k + 1 = n → ∀ (U : T) (x : (K.obj U).X n), (K.obj U).d n (n + 1) x = 0 →
        ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (K.obj V).X k, (K.obj V).d k n y = (K.map g).f n x := by
      intro k n hkn
      subst hkn
      exact gen k
    intro n U x hx
    exact gen' (n - 1) n (by omega) U x hx

  have exK : ∀ (U : T) (k n : ℤ), k + 1 = n → ∀ x : (K.obj U).X n, (K.obj U).d n (n + 1) x = 0 →
      ∃ y : (K.obj U).X k, (K.obj U).d k n y = x := by
    intro U k n hkn x hx
    obtain rfl : k = n - 1 := by omega
    exact GlobalTheory.CartanZero.cartan_zero T Cov K hbK hRK hLK U n x hx
  intro U
  constructor
  · have sg : ∀ (j : ℤ) (z : (D.obj U).X (j + 1)), (D.obj U).d (j + 1) (j + 1 + 1) z = 0 →
        ∃ (c : (C.obj U).X (j + 1)) (y : (D.obj U).X j), (C.obj U).d (j + 1) (j + 1 + 1) c = 0 ∧
          (φ.app U).f (j + 1) c = z + (D.obj U).d j (j + 1) y := by
      intro j z hz
      obtain ⟨x, hxp, hxq⟩ := mk (j + 1) U 0 z
      have hx : (K.obj U).d (j + 1) (j + 1 + 1) x = 0 :=
        cyc _ _ _ (by rw [hxp, map_zero]) (by rw [hxp, hxq, map_zero, zero_add, hz])
      obtain ⟨y, hy⟩ := exK U j (j + 1) rfl x hx
      obtain ⟨u, hu⟩ : ∃ u : (D.obj U).X j, (q j).app U y = u := ⟨_, rfl⟩
      obtain ⟨v, hv⟩ : ∃ v : (C.obj U).X (j + 1), (p j).app U y = v := ⟨_, rfl⟩
      refine ⟨v, -u, ?_, ?_⟩
      · have := dp j U y
        rw [hy, hxp, hv] at this
        exact neg_eq_zero.mp this.symm
      · have := dq j U y
        rw [hy, hxq, hu, hv] at this
        rw [map_neg, this]
        abel
    have sg' : ∀ k n : ℤ, k + 1 = n → ∀ (z : (D.obj U).X n), (D.obj U).d n (n + 1) z = 0 →
        ∃ (c : (C.obj U).X n) (y : (D.obj U).X k), (C.obj U).d n (n + 1) c = 0 ∧
          (φ.app U).f n c = z + (D.obj U).d k n y := by
      intro k n hkn
      subst hkn
      exact sg k
    intro n z hz
    exact sg' (n - 1) n (by omega) z hz
  · have ij : ∀ (j : ℤ) (c : (C.obj U).X (j + 1 + 1)), (C.obj U).d (j + 1 + 1) (j + 1 + 1 + 1) c = 0 →
        ∀ y : (D.obj U).X (j + 1), (φ.app U).f (j + 1 + 1) c = (D.obj U).d (j + 1) (j + 1 + 1) y →
        ∃ b : (C.obj U).X (j + 1), (C.obj U).d (j + 1) (j + 1 + 1) b = c := by
      intro j c hc y hy
      obtain ⟨x, hxp, hxq⟩ := mk (j + 1) U c (-y)
      have hx : (K.obj U).d (j + 1) (j + 1 + 1) x = 0 :=
        cyc _ _ _ (by rw [hxp, hc]) (by rw [hxp, hxq, map_neg, hy, add_neg_cancel])
      obtain ⟨y', hy'⟩ := exK U j (j + 1) rfl x hx
      obtain ⟨v, hv⟩ : ∃ v : (C.obj U).X (j + 1), (p j).app U y' = v := ⟨_, rfl⟩
      refine ⟨-v, ?_⟩
      have := dp j U y'
      rw [hy', hxp, hv] at this
      rw [map_neg]
      exact this.symm
    have ij' : ∀ i n : ℤ, i + 1 = n → ∀ c : (C.obj U).X n, (C.obj U).d n (n + 1) c = 0 →
        ∀ y : (D.obj U).X i, (φ.app U).f n c = (D.obj U).d i n y → ∃ b : (C.obj U).X i, (C.obj U).d i n b = c := by
      intro i n hin
      subst hin
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact ij j
    intro n c hc ⟨y, hy⟩
    exact ij' (n - 1) n (by omega) c hc y hy

end GlobalTheory.CartanOne
