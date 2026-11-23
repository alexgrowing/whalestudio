import Mathlib
import Development.EtaleCohomology.CohomologicalPurity.LeafOffContPf
import Development.EtaleCohomology.CohomologicalPurity.LeafHsContPfFive
import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyMVPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtalePurityFreeCover

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.CohomologicalPurity

namespace UpperTheory.Cb.OffDiagonalContinuation

universe u

structure Sys (J : Type) [SmallCategory J] where
  G : J → Type u
  [g : ∀ j, AddCommGroup (G j)]
  L : Type u
  [l : AddCommGroup L]
  ρ : ∀ {j k : J}, (j ⟶ k) → G j →+ G k
  ι : ∀ j, G j →+ L
  ι_ρ : ∀ {j k : J} (f : j ⟶ k) (y : G j), ι k (ρ f y) = ι j y
  ρ_comp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l) (y : G j), ρ (f ≫ g) y = ρ g (ρ f y)

attribute [instance] Sys.g Sys.l

variable {J : Type} [SmallCategory J]

def Sys.Surj (S : Sys.{u} J) : Prop := ∀ x : S.L, ∃ j, ∃ y : S.G j, S.ι j y = x

def Sys.Inj (S : Sys.{u} J) : Prop := ∀ j (y : S.G j), S.ι j y = 0 → ∃ (k : J) (f : j ⟶ k), S.ρ f y = 0

structure Sys.Hom (S T : Sys.{u} J) where
  a : ∀ j, S.G j →+ T.G j
  b : S.L →+ T.L
  a_ρ : ∀ {j k : J} (f : j ⟶ k) (y : S.G j), a k (S.ρ f y) = T.ρ f (a j y)
  b_ι : ∀ j (y : S.G j), b (S.ι j y) = T.ι j (a j y)

def Sys.prod (S T : Sys.{u} J) : Sys.{u} J where
  G j := S.G j × T.G j
  L := S.L × T.L
  ρ f := (S.ρ f).prodMap (T.ρ f)
  ι j := (S.ι j).prodMap (T.ι j)
  ι_ρ f y := Prod.ext (S.ι_ρ f y.1) (T.ι_ρ f y.2)
  ρ_comp f g y := Prod.ext (S.ρ_comp f g y.1) (T.ρ_comp f g y.2)

theorem Sys.prod_surj [IsFiltered J] {S T : Sys.{u} J} (hS : S.Surj) (hT : T.Surj) : (S.prod T).Surj := by
  rintro ⟨a, b⟩
  obtain ⟨j, y, rfl⟩ := hS a
  obtain ⟨k, z, rfl⟩ := hT b
  exact ⟨IsFiltered.max j k, (S.ρ (IsFiltered.leftToMax j k) y, T.ρ (IsFiltered.rightToMax j k) z),
    Prod.ext (S.ι_ρ _ y) (T.ι_ρ _ z)⟩

theorem Sys.prod_inj {S T : Sys.{u} J} (hS : S.Inj) (hT : T.Inj) : (S.prod T).Inj := by
  rintro j ⟨y, z⟩ h
  have h1 : S.ι j y = 0 := congrArg Prod.fst h
  have h2 : T.ι j z = 0 := congrArg Prod.snd h
  obtain ⟨k, f, hk⟩ := hS j y h1
  obtain ⟨l, g, hl⟩ := hT k (T.ρ f z) (by rw [T.ι_ρ, h2])
  refine ⟨l, f ≫ g, Prod.ext ?_ ?_⟩
  · change S.ρ (f ≫ g) y = 0
    rw [S.ρ_comp, hk, map_zero]
  · change T.ρ (f ≫ g) z = 0
    rw [T.ρ_comp, hl]

def Sys.Hom.pair {S T T' : Sys.{u} J} (α : S.Hom T) (β : S.Hom T') : S.Hom (T.prod T') where
  a j := (α.a j).prod (β.a j)
  b := α.b.prod β.b
  a_ρ f y := Prod.ext (α.a_ρ f y) (β.a_ρ f y)
  b_ι j y := Prod.ext (α.b_ι j y) (β.b_ι j y)

def Sys.Hom.diff {S T T' : Sys.{u} J} (α : S.Hom T') (β : T.Hom T') : (S.prod T).Hom T' where
  a j := (α.a j).comp (AddMonoidHom.fst _ _) - (β.a j).comp (AddMonoidHom.snd _ _)
  b := α.b.comp (AddMonoidHom.fst _ _) - β.b.comp (AddMonoidHom.snd _ _)
  a_ρ f y := by
    change α.a _ (S.ρ f y.1) - β.a _ (T.ρ f y.2) = T'.ρ f (α.a _ y.1 - β.a _ y.2)
    rw [α.a_ρ, β.a_ρ, map_sub]
  b_ι j y := by
    change α.b (S.ι j y.1) - β.b (T.ι j y.2) = T'.ι j (α.a _ y.1 - β.a _ y.2)
    rw [α.b_ι, β.b_ι, map_sub]

theorem Sys.five [IsFiltered J] {S₁ S₂ S₃ S₄ S₅ : Sys.{u} J} (h₁ : S₁.Hom S₂) (h₂ : S₂.Hom S₃) (h₃ : S₃.Hom S₄)
    (h₄ : S₄.Hom S₅) (c₂ : ∀ j, Function.Exact (h₁.a j) (h₂.a j)) (c₃ : ∀ j, Function.Exact (h₂.a j) (h₃.a j))
    (c₄ : ∀ j, Function.Exact (h₃.a j) (h₄.a j)) (e₂ : Function.Exact h₁.b h₂.b) (e₃ : Function.Exact h₂.b h₃.b)
    (e₄ : Function.Exact h₃.b h₄.b) (s₁ : S₁.Surj) (s₂ : S₂.Surj) (i₂ : S₂.Inj) (s₄ : S₄.Surj) (i₄ : S₄.Inj)
    (i₅ : S₅.Inj) : S₃.Surj ∧ S₃.Inj := by
  constructor
  · intro x
    obtain ⟨j, y₄, hy₄⟩ := s₄ (h₃.b x)
    have h5 : S₅.ι j (h₄.a j y₄) = 0 := by
      rw [← h₄.b_ι, hy₄]
      exact e₄.apply_apply_eq_zero x
    obtain ⟨k, f, hk⟩ := i₅ j _ h5
    rw [← h₄.a_ρ] at hk
    obtain ⟨y₃, hy₃⟩ := (c₄ k _).1 hk
    have h6 : h₃.b (x - S₃.ι k y₃) = 0 := by
      rw [map_sub, h₃.b_ι, hy₃, S₄.ι_ρ, hy₄, sub_self]
    obtain ⟨w, hw⟩ := (e₃ _).1 h6
    obtain ⟨j₂, w₂, rfl⟩ := s₂ w
    refine ⟨IsFiltered.max k j₂, S₃.ρ (IsFiltered.leftToMax k j₂) y₃ + h₂.a _ (S₂.ρ (IsFiltered.rightToMax k j₂) w₂), ?_⟩
    rw [map_add, S₃.ι_ρ, ← h₂.b_ι, S₂.ι_ρ, hw]
    abel
  · intro j y hy
    have h4 : S₄.ι j (h₃.a j y) = 0 := by rw [← h₃.b_ι, hy, map_zero]
    obtain ⟨k, f, hk⟩ := i₄ j _ h4
    rw [← h₃.a_ρ] at hk
    obtain ⟨w, hw⟩ := (c₃ k _).1 hk
    have h2 : h₂.b (S₂.ι k w) = 0 := by rw [h₂.b_ι, hw, S₃.ι_ρ, hy]
    obtain ⟨z, hz⟩ := (e₂ _).1 h2
    obtain ⟨j₁, z₁, rfl⟩ := s₁ z
    have h3 : S₂.ι (IsFiltered.max k j₁) (S₂.ρ (IsFiltered.leftToMax k j₁) w -
        h₁.a _ (S₁.ρ (IsFiltered.rightToMax k j₁) z₁)) = 0 := by
      rw [map_sub, S₂.ι_ρ, ← h₁.b_ι, S₁.ι_ρ, hz, sub_self]
    obtain ⟨m, g, hm⟩ := i₂ _ _ h3
    refine ⟨m, f ≫ IsFiltered.leftToMax k j₁ ≫ g, ?_⟩
    rw [S₃.ρ_comp, S₃.ρ_comp, ← hw, ← h₂.a_ρ, ← h₂.a_ρ]
    rw [map_sub, sub_eq_zero] at hm
    rw [hm, ← h₁.a_ρ]
    exact (c₂ m).apply_apply_eq_zero _

structure Sq {X : Scheme.{0}} (U V W P : X.Opens) : Prop where
  hW : W = U ⊔ V
  hP : P = U ⊓ V

section Sq
variable {X : Scheme.{0}} {U V W P : X.Opens}

theorem Sq.uw (c : Sq U V W P) : U ≤ W := c.hW ▸ le_sup_left
theorem Sq.vw (c : Sq U V W P) : V ≤ W := c.hW ▸ le_sup_right
theorem Sq.pu (c : Sq U V W P) : P ≤ U := c.hP ▸ inf_le_left
theorem Sq.pv (c : Sq U V W P) : P ≤ V := c.hP ▸ inf_le_right

theorem Sq.cover (c : Sq U V W P) (R : Type) [CommRing R] :
    Cover2 R (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw)) := by
  obtain ⟨rfl, rfl⟩ := c
  exact ⟨Thom.HtpyMVPf.mono_sch _, Thom.HtpyMVPf.mono_sch _, fun _ => UpperTheory.etale_purity_free_cover R X U V⟩

theorem Sq.pb (c : Sq U V W P) : IsPullback (sch.map (X.homOfLE c.pu)) (sch.map (X.homOfLE c.pv))
    (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw)) := by
  obtain ⟨rfl, rfl⟩ := c
  have := Thom.HtpyMVPf.sch_pres
  exact (isPullback_opens_inf_le (X := X) (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch

end Sq

def res (q : ℕ) (i n : ℤ) {X : Scheme.{0}} {U W : X.Opens} (h : U ≤ W) :
    Ht q (sch.obj W) n i →+ Ht q (sch.obj U) n i := pull _ (sch.map (X.homOfLE h)) (tw q i) n

def rDiff (q : ℕ) (i n : ℤ) {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P) :
    Ht q (sch.obj U) n i × Ht q (sch.obj V) n i →+ Ht q (sch.obj P) n i :=
  (res q i n c.pu).comp (AddMonoidHom.fst _ _) - (res q i n c.pv).comp (AddMonoidHom.snd _ _)

def rPair (q : ℕ) (i n : ℤ) {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P) :
    Ht q (sch.obj W) n i →+ Ht q (sch.obj U) n i × Ht q (sch.obj V) n i :=
  (res q i n c.uw).prod (res q i n c.vw)

private theorem pull_hom_inv (R : Type) [CommRing R] (F : Shv R) {A B : Spc} (e : A ≅ B) (n : ℤ) (x : H R B F n) :
    pull R e.inv F n (pull R e.hom F n x) = x := by
  rw [← pull_comp, e.inv_hom_id, pull_id]

private theorem pull_inv_hom (R : Type) [CommRing R] (F : Shv R) {A B : Spc} (e : A ≅ B) (n : ℤ) (x : H R A F n) :
    pull R e.hom F n (pull R e.inv F n x) = x := by
  rw [← pull_comp, e.hom_inv_id, pull_id]

private theorem res_fst (q : ℕ) (i n : ℤ) {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P) (a : Ht q (sch.obj U) n i) :
    pull _ c.pb.isoPullback.inv (tw q i) n (res q i n c.pu a) = pull _ (pullback.fst _ _) (tw q i) n a := by
  have h : sch.map (X.homOfLE c.pu) = c.pb.isoPullback.hom ≫ pullback.fst _ _ := c.pb.isoPullback_hom_fst.symm
  have h2 : pull _ (sch.map (X.homOfLE c.pu)) (tw q i) n a =
      pull _ c.pb.isoPullback.hom (tw q i) n (pull _ (pullback.fst _ _) (tw q i) n a) := by
    rw [← pull_comp]; exact congrArg (fun m => pull _ m (tw q i) n a) h
  change pull _ c.pb.isoPullback.inv (tw q i) n (pull _ (sch.map (X.homOfLE c.pu)) (tw q i) n a) = _
  rw [h2, pull_hom_inv]

private theorem res_snd (q : ℕ) (i n : ℤ) {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P) (a : Ht q (sch.obj V) n i) :
    pull _ c.pb.isoPullback.inv (tw q i) n (res q i n c.pv a) = pull _ (pullback.snd _ _) (tw q i) n a := by
  have h : sch.map (X.homOfLE c.pv) = c.pb.isoPullback.hom ≫ pullback.snd _ _ := c.pb.isoPullback_hom_snd.symm
  have h2 : pull _ (sch.map (X.homOfLE c.pv)) (tw q i) n a =
      pull _ c.pb.isoPullback.hom (tw q i) n (pull _ (pullback.snd _ _) (tw q i) n a) := by
    rw [← pull_comp]; exact congrArg (fun m => pull _ m (tw q i) n a) h
  change pull _ c.pb.isoPullback.inv (tw q i) n (pull _ (sch.map (X.homOfLE c.pv)) (tw q i) n a) = _
  rw [h2, pull_hom_inv]

private theorem pull_inv_inj (q : ℕ) (i n : ℤ) {A B : Spc} (e : A ≅ B) :
    Function.Injective (pull _ e.inv (tw q i) n) := fun x y h => by
  rw [← pull_inv_hom _ _ e n x, h, pull_inv_hom]

section ex
variable {q : ℕ} {i n : ℤ} {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P)

private theorem ex1 {G : Type 1} [AddCommGroup G]
    (Dd : H (ZMod q) (pullback (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n →+ G)
    (E2 : ∀ z, Dd z = 0 ↔ ∃ a b, z = pull _ (pullback.fst _ _) (tw q i) n a - pull _ (pullback.snd _ _) (tw q i) n b) :
    Function.Exact (rDiff q i n c) (Dd.comp (pull _ c.pb.isoPullback.inv (tw q i) n)) := by
  intro y
  refine (E2 (pull _ c.pb.isoPullback.inv (tw q i) n y)).trans ⟨?_, ?_⟩
  · rintro ⟨a, b, h⟩
    refine ⟨(a, b), pull_inv_inj q i n c.pb.isoPullback ?_⟩
    have : rDiff q i n c (a, b) = res q i n c.pu a - res q i n c.pv b := rfl
    rw [this, map_sub, res_fst q i n c, res_snd q i n c, h]
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨a, b, ?_⟩
    have : rDiff q i n c (a, b) = res q i n c.pu a - res q i n c.pv b := rfl
    rw [this, map_sub, res_fst q i n c, res_snd q i n c]

private theorem ex2
    (Dd : H (ZMod q) (pullback (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n →+
      Ht q (sch.obj W) (n + 1) i)
    (E3 : ∀ x, (pull _ (sch.map (X.homOfLE c.uw)) (tw q i) (n + 1) x = 0 ∧
      pull _ (sch.map (X.homOfLE c.vw)) (tw q i) (n + 1) x = 0) ↔ ∃ z, Dd z = x) :
    Function.Exact (Dd.comp (pull _ c.pb.isoPullback.inv (tw q i) n)) (rPair q i (n + 1) c) := by
  intro x
  refine Iff.trans Prod.mk_eq_zero ((E3 x).trans ⟨?_, ?_⟩)
  · rintro ⟨y, rfl⟩
    refine ⟨pull _ c.pb.isoPullback.hom (tw q i) n y, ?_⟩
    exact congrArg Dd (pull_hom_inv _ _ c.pb.isoPullback n y)
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩

private theorem ex3
    (E1 : ∀ a b, pull _ (pullback.fst (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n a =
        pull _ (pullback.snd (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n b ↔
      ∃ x, pull _ (sch.map (X.homOfLE c.uw)) (tw q i) n x = a ∧ pull _ (sch.map (X.homOfLE c.vw)) (tw q i) n x = b) :
    Function.Exact (rPair q i n c) (rDiff q i n c) := by
  rintro ⟨a, b⟩
  have h0 : rDiff q i n c (a, b) = 0 ↔
      pull _ (pullback.fst (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n a =
        pull _ (pullback.snd (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n b := by
    rw [← res_fst q i n c, ← res_snd q i n c]
    have : rDiff q i n c (a, b) = res q i n c.pu a - res q i n c.pv b := rfl
    rw [this, sub_eq_zero]
    exact ⟨fun h => congrArg _ h, fun h => pull_inv_inj q i n c.pb.isoPullback h⟩
  refine h0.trans ((E1 a b).trans ⟨?_, ?_⟩)
  · rintro ⟨x, h1, h2⟩
    exact ⟨x, Prod.ext h1 h2⟩
  · rintro ⟨x, h⟩
    exact ⟨x, congrArg Prod.fst h, congrArg Prod.snd h⟩

end ex

private theorem pb_sq {X' X : Scheme.{0}} (f : X' ⟶ X) {U' V' W' P' : X'.Opens} {U V W P : X.Opens}
    (c' : Sq U' V' W' P') (c : Sq U V W P) (hU : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (hW : W' ≤ f ⁻¹ᵁ W)
    (hP : P' ≤ f ⁻¹ᵁ P)
    (eu : sch.map (X'.homOfLE c'.uw) ≫ sch.map (f.resLE W W' hW) = sch.map (f.resLE U U' hU) ≫ sch.map (X.homOfLE c.uw))
    (ev : sch.map (X'.homOfLE c'.vw) ≫ sch.map (f.resLE W W' hW) = sch.map (f.resLE V V' hV) ≫ sch.map (X.homOfLE c.vw)) :
    c'.pb.isoPullback.hom ≫ pullback.map _ _ _ _ _ _ _ eu ev = sch.map (f.resLE P P' hP) ≫ c.pb.isoPullback.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc, Category.assoc,
      IsPullback.isoPullback_hom_fst, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp
  · rw [Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc, Category.assoc,
      IsPullback.isoPullback_hom_snd, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp

private theorem nat_pull (q : ℕ) (i n : ℤ) {A A' B B' : Spc} (e : A ≅ B) (e' : A' ≅ B') (m : B' ⟶ B) (r : A' ⟶ A)
    (hs : e'.hom ≫ m = r ≫ e.hom) (x : Ht q A n i) :
    pull _ m (tw q i) n (pull _ e.inv (tw q i) n x) = pull _ e'.inv (tw q i) n (pull _ r (tw q i) n x) := by
  apply pull_inv_inj q i n e'.symm
  change pull _ e'.hom _ _ _ = pull _ e'.hom _ _ (pull _ e'.inv _ _ _)
  rw [pull_inv_hom, ← pull_comp, hs, pull_comp, pull_inv_hom]

theorem mv (q : ℕ) (i : ℤ) : ∃ d : ∀ {X : Scheme.{0}} {U V W P : X.Opens}, Sq U V W P → ∀ n : ℤ,
    Ht q (sch.obj P) n i →+ Ht q (sch.obj W) (n + 1) i,
    (∀ {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P) (n : ℤ),
      Function.Exact (rDiff q i n c) (d c n) ∧ Function.Exact (d c n) (rPair q i (n + 1) c) ∧
      Function.Exact (rPair q i n c) (rDiff q i n c)) ∧
    ∀ {X' X : Scheme.{0}} (f : X' ⟶ X) {U' V' W' P' : X'.Opens} {U V W P : X.Opens} (c' : Sq U' V' W' P')
      (c : Sq U V W P) (hU : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (hW : W' ≤ f ⁻¹ᵁ W) (hP : P' ≤ f ⁻¹ᵁ P) (n : ℤ)
      (x : Ht q (sch.obj P) n i),
      pull _ (sch.map (f.resLE W W' hW)) (tw q i) (n + 1) (d c n x) =
        d c' n (pull _ (sch.map (f.resLE P P' hP)) (tw q i) n x) := by
  obtain ⟨D, hex, hnat⟩ := GlobalTheory.EtC.mayerVietoris (ZMod q) (tw q i)
  refine ⟨fun {X U V W P} c n => (D (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw)) (c.cover _) n).comp
    (pull _ c.pb.isoPullback.inv (tw q i) n), ?_, ?_⟩
  · intro X U V W P c n
    obtain ⟨E1, E2, E3⟩ := hex (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw)) (c.cover _) n
    exact ⟨ex1 c _ E2, ex2 c _ E3, ex3 c E1⟩
  · intro X' X f U' V' W' P' U V W P c' c hU hV hW hP n x
    have eu : sch.map (X'.homOfLE c'.uw) ≫ sch.map (f.resLE W W' hW) =
        sch.map (f.resLE U U' hU) ≫ sch.map (X.homOfLE c.uw) := by
      rw [← sch.map_comp, ← sch.map_comp]; congr 1; simp
    have ev : sch.map (X'.homOfLE c'.vw) ≫ sch.map (f.resLE W W' hW) =
        sch.map (f.resLE V V' hV) ≫ sch.map (X.homOfLE c.vw) := by
      rw [← sch.map_comp, ← sch.map_comp]; congr 1; simp
    refine (hnat _ _ _ _ _ _ _ eu ev (c'.cover _) (c.cover _) n _).trans ?_
    exact congrArg (D _ _ _ n) (nat_pull q i n _ _ _ _ (pb_sq f c' c hU hV hW hP eu ev) x)

section sys
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {J : Type} [SmallCategory J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B))

private theorem off_le_map {R S : Type} [CommRing R] [CommRing S] (K : Ideal A) (a : A →+* R) (b : A →+* S)
    (c : R →+* S) (e : c.comp a = b) :
    off S (K.map b) ≤ Spec.map (CommRingCat.ofHom c) ⁻¹ᵁ off R (K.map a) := by
  subst e
  rw [← Ideal.map_map]
  exact (off_map c _).le

private theorem offD (K : Ideal A) {j k : J} (f : j ⟶ k) : off (D.obj k) (K.map (s.app k).hom) ≤
    Spec.map (D.map f) ⁻¹ᵁ off (D.obj j) (K.map (s.app j).hom) :=
  off_le_map K _ _ (D.map f).hom (by
    have h : s.app j ≫ D.map f = s.app k := by simpa using (s.naturality f).symm
    exact congrArg CommRingCat.Hom.hom h)

private theorem offT (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (K : Ideal A) (j : J) :
    off B (K.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (K.map (s.app j).hom) :=
  off_le_map K _ _ (t.app j).hom (congrArg CommRingCat.Hom.hom (he j))

private theorem pull_tri (q : ℕ) (i n : ℤ) {X'' X' X : Scheme.{0}} {g : X'' ⟶ X} (a : X'' ⟶ X') (b : X' ⟶ X) (e : g = a ≫ b)
    {U'' : X''.Opens} {U' : X'.Opens} {U : X.Opens} (h : U'' ≤ g ⁻¹ᵁ U) (h1 : U'' ≤ a ⁻¹ᵁ U') (h2 : U' ≤ b ⁻¹ᵁ U)
    (y : Ht q (sch.obj U) n i) :
    pull _ (opnMap g U'' U h).left (tw q i) n y =
      pull _ (opnMap a U'' U' h1).left (tw q i) n (pull _ (opnMap b U' U h2).left (tw q i) n y) := by
  rw [opnMap_tri a b e U'' U' U h h1 h2]
  exact pull_left_comp q (opnMap a U'' U' h1) (opnMap b U' U h2) n i y

def sysOf (q : ℕ) (i m : ℤ) (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (K : Ideal A) : Sys.{1} J where
  G j := Ht q (sch.obj (off (D.obj j) (K.map (s.app j).hom))) m i
  L := Ht q (sch.obj (off B (K.map φ))) m i
  ρ f := pull _ (opnMap (Spec.map (D.map f)) _ _ (offD D s K f)).left (tw q i) m
  ι j := pull _ (opnMap (Spec.map (t.app j)) _ _ (offT φ D s t he K j)).left (tw q i) m
  ι_ρ {j k} f y := by
    have e : Spec.map (t.app j) = Spec.map (t.app k) ≫ Spec.map (D.map f) := by
      rw [← Spec.map_comp]
      congr 1
      simpa using (t.naturality f).symm
    exact (pull_tri q i m _ _ e (offT φ D s t he K j) (offT φ D s t he K k) (offD D s K f) y).symm
  ρ_comp {j k l} f g y := by
    have e : Spec.map (D.map (f ≫ g)) = Spec.map (D.map g) ≫ Spec.map (D.map f) := by
      rw [← Spec.map_comp, ← Functor.map_comp]
    exact pull_tri q i m _ _ e (offD D s K (f ≫ g)) (offD D s K g) (offD D s K f) y

private theorem res_nat (q : ℕ) (i n : ℤ) {X' X : Scheme.{0}} (f : X' ⟶ X) {U' W' : X'.Opens} {U W : X.Opens}
    (h1 : U' ≤ W') (h2 : U ≤ W) (a : W' ≤ f ⁻¹ᵁ W) (b : U' ≤ f ⁻¹ᵁ U) (y : Ht q (sch.obj W) n i) :
    res q i n h1 (pull _ (opnMap f W' W a).left (tw q i) n y) =
      pull _ (opnMap f U' U b).left (tw q i) n (res q i n h2 y) := by
  have e : sch.map (X'.homOfLE h1) ≫ sch.map (f.resLE W W' a) = sch.map (f.resLE U U' b) ≫ sch.map (X.homOfLE h2) := by
    rw [← sch.map_comp, ← sch.map_comp]; congr 1; simp
  have h := congrArg (fun m => pull _ m (tw q i) n y) e
  simp only [pull_comp] at h
  exact h

def resHom (q : ℕ) (i m : ℤ) (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (K K' : Ideal A)
    (hle : ∀ (R : Type) [CommRing R] (ψ : A →+* R), off R (K.map ψ) ≤ off R (K'.map ψ)) :
    (sysOf φ D s t q i m he K').Hom (sysOf φ D s t q i m he K) where
  a j := res q i m (hle _ _)
  b := res q i m (hle _ _)
  a_ρ f y := res_nat q i m _ _ _ _ _ y
  b_ι j y := res_nat q i m _ _ _ _ _ y

theorem cont_iff (q : ℕ) (i m : ℤ) (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (K : Ideal A) :
    HtOffCont q φ K D s t m i ↔ (sysOf φ D s t q i m he K).Surj ∧ (sysOf φ D s t q i m he K).Inj := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x => ?_, fun j y hy => ?_⟩
    · obtain ⟨j, _, y, e⟩ := h1 x
      exact ⟨j, y, e⟩
    · obtain ⟨k, f, _, e⟩ := h2 j (offT φ D s t he K j) y hy
      exact ⟨k, f, e⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun x => ?_, fun j h y hy => ?_⟩
    · obtain ⟨j, y, e⟩ := h1 x
      exact ⟨j, offT φ D s t he K j, y, e⟩
    · obtain ⟨k, f, e⟩ := h2 j y hy
      exact ⟨k, f, offD D s K f, e⟩

end sys

section final
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {J : Type} [SmallCategory J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B))

def dHom (q : ℕ) (i m : ℤ) (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) (KU KV KW KP : Ideal A)
    (hsq : ∀ (R : Type) [CommRing R] (ψ : A →+* R),
      Sq (off R (KU.map ψ)) (off R (KV.map ψ)) (off R (KW.map ψ)) (off R (KP.map ψ)))
    (d : ∀ {X : Scheme.{0}} {U V W P : X.Opens}, Sq U V W P → ∀ n : ℤ,
      Ht q (sch.obj P) n i →+ Ht q (sch.obj W) (n + 1) i)
    (nat : ∀ {X' X : Scheme.{0}} (f : X' ⟶ X) {U' V' W' P' : X'.Opens} {U V W P : X.Opens} (c' : Sq U' V' W' P')
      (c : Sq U V W P) (hU : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (hW : W' ≤ f ⁻¹ᵁ W) (hP : P' ≤ f ⁻¹ᵁ P) (n : ℤ)
      (x : Ht q (sch.obj P) n i),
      pull _ (sch.map (f.resLE W W' hW)) (tw q i) (n + 1) (d c n x) =
        d c' n (pull _ (sch.map (f.resLE P P' hP)) (tw q i) n x)) :
    (sysOf φ D s t q i m he KP).Hom (sysOf φ D s t q i (m + 1) he KW) where
  a j := d (hsq _ _) m
  b := d (hsq _ _) m
  a_ρ f y := (nat (Spec.map (D.map f)) (hsq _ _) (hsq _ _) (offD D s KU f) (offD D s KV f) (offD D s KW f)
    (offD D s KP f) m y).symm
  b_ι j y := (nat (Spec.map (t.app j)) (hsq _ _) (hsq _ _) (offT φ D s t he KU j) (offT φ D s t he KV j)
    (offT φ D s t he KW j) (offT φ D s t he KP j) m y).symm

theorem step [IsFiltered J] (q : ℕ) (i : ℤ) (he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ)
    (KU KV KW KP : Ideal A)
    (hsq : ∀ (R : Type) [CommRing R] (ψ : A →+* R),
      Sq (off R (KU.map ψ)) (off R (KV.map ψ)) (off R (KW.map ψ)) (off R (KP.map ψ)))
    (hU : ∀ m, HtOffCont q φ KU D s t m i) (hV : ∀ m, HtOffCont q φ KV D s t m i)
    (hP : ∀ m, HtOffCont q φ KP D s t m i) (n : ℤ) : HtOffCont q φ KW D s t n i := by
  obtain ⟨d, hex, hnat⟩ := mv q i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have u := fun m => (cont_iff φ D s t q i m he KU).1 (hU m)
  have v := fun m => (cont_iff φ D s t q i m he KV).1 (hV m)
  have p := fun m => (cont_iff φ D s t q i m he KP).1 (hP m)
  have hpu : ∀ (R : Type) [CommRing R] (ψ : A →+* R), off R (KP.map ψ) ≤ off R (KU.map ψ) := fun R _ ψ => (hsq R ψ).pu
  have hpv : ∀ (R : Type) [CommRing R] (ψ : A →+* R), off R (KP.map ψ) ≤ off R (KV.map ψ) := fun R _ ψ => (hsq R ψ).pv
  have huw : ∀ (R : Type) [CommRing R] (ψ : A →+* R), off R (KU.map ψ) ≤ off R (KW.map ψ) := fun R _ ψ => (hsq R ψ).uw
  have hvw : ∀ (R : Type) [CommRing R] (ψ : A →+* R), off R (KV.map ψ) ≤ off R (KW.map ψ) := fun R _ ψ => (hsq R ψ).vw
  refine (cont_iff φ D s t q i (m + 1) he KW).2 (Sys.five
    ((resHom φ D s t q i m he KP KU hpu).diff (resHom φ D s t q i m he KP KV hpv))
    (dHom φ D s t q i m he KU KV KW KP hsq d hnat)
    ((resHom φ D s t q i (m + 1) he KU KW huw).pair (resHom φ D s t q i (m + 1) he KV KW hvw))
    ((resHom φ D s t q i (m + 1) he KP KU hpu).diff (resHom φ D s t q i (m + 1) he KP KV hpv))
    (fun _ => (hex (hsq _ _) m).1) (fun _ => (hex (hsq _ _) m).2.1) (fun _ => (hex (hsq _ _) (m + 1)).2.2)
    (hex (hsq _ _) m).1 (hex (hsq _ _) m).2.1 (hex (hsq _ _) (m + 1)).2.2
    (Sys.prod_surj (u m).1 (v m).1) (p m).1 (p m).2 (Sys.prod_surj (u (m + 1)).1 (v (m + 1)).1)
    (Sys.prod_inj (u (m + 1)).2 (v (m + 1)).2) (p (m + 1)).2)

private theorem mem_off {R : Type} [CommRing R] (K : Ideal R) (p : Spec (CommRingCat.of R)) :
    p ∈ off R K ↔ ¬ K ≤ (p : PrimeSpectrum R).asIdeal := Iff.rfl

private theorem off_inf {r : ℕ} (y : Fin r → A) (f : A) :
    off A (Ideal.span (Set.range fun k => y k * f)) = off A (Ideal.span (Set.range y)) ⊓ off A (Ideal.span {f}) := by
  ext p
  change p ∈ off A _ ↔ p ∈ off A _ ∧ p ∈ off A _
  simp only [mem_off, Ideal.span_le, Set.range_subset_iff, Ideal.span_singleton_le_iff_mem, SetLike.mem_coe]
  have hp := (p : PrimeSpectrum A).isPrime
  by_cases hf : f ∈ (p : PrimeSpectrum A).asIdeal
  · simp [hf, Ideal.mul_mem_left]
  · simp [hf, hp.mul_mem_iff_mem_or_mem]

private theorem sq_of {r : ℕ} (x : Fin (r + 1) → A) (R : Type) [CommRing R] (ψ : A →+* R) :
    Sq (off R ((Ideal.span (Set.range fun k : Fin r => x k.castSucc)).map ψ))
      (off R ((Ideal.span {x (Fin.last r)}).map ψ)) (off R ((Ideal.span (Set.range x)).map ψ))
      (off R ((Ideal.span (Set.range fun k : Fin r => x k.castSucc * x (Fin.last r))).map ψ)) := by
  rw [off_map, off_map, off_map, off_map, off_inf]
  refine ⟨?_, rfl⟩
  rw [range_fin_succ x, off_span_union]
  rfl

end final

end UpperTheory.Cb.OffDiagonalContinuation

theorem UpperTheory.Cb.off_diagonal_continuation_inductive :
    LateralTheory.CohomologicalPurity.LeafBd → LateralTheory.CohomologicalPurity.LeafExc → LateralTheory.CohomologicalPurity.OffContBasic → LateralTheory.CohomologicalPurity.OffContStep := by
  intro _ _ hb a1 a4 b1 _ _ _ r ih q A B _ _ φ x hq J _ _ D s t hc he n i
  exact UpperTheory.Cb.OffDiagonalContinuation.step φ D s t q i he _ _ _ _ (UpperTheory.Cb.OffDiagonalContinuation.sq_of x)
    (fun m => ih q φ _ hq J D s t hc he m i)
    (fun m => hb a1 a4 b1 q φ _ hq J D s t hc he m i)
    (fun m => ih q φ (fun k => x k.castSucc * x (Fin.last r)) hq J D s t hc he m i) n
