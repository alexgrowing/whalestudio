import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.BlowOfBl

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison TopologicalSpace

namespace UpperTheory.Gal.KunnethLefschetz.G

private lemma flat_nzd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (h : φ.Flat) {a : A}
    (ha : a ∈ nonZeroDivisors A) : φ a ∈ nonZeroDivisors B := by
  algebraize [φ]
  have hr := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) ha
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  apply hr
  change a • y = a • 0
  rw [Algebra.smul_def, Algebra.smul_def, mul_zero, mul_comm]
  exact hy

private def Reg {X : Scheme.{0}} (b : Γ(X, ⊤)) : Prop :=
  ∀ x : X, (X.presheaf.germ ⊤ x trivial).hom b ∈ nonZeroDivisors (X.presheaf.stalk x)

private lemma reg_flat {X Z : Scheme.{0}} (φ : X ⟶ Z) [Flat φ] {b : Γ(Z, ⊤)} (hb : Reg b) :
    Reg (φ.appTop.hom b) := by
  intro x
  have h := flat_nzd (φ.stalkMap x).hom (Flat.stalkMap φ x) (hb (φ x))
  have e := Scheme.Hom.germ_stalkMap_apply φ ⊤ x trivial b
  rw [e] at h
  exact h

private lemma reg_of_affine {X : Scheme.{0}} [IsAffine X] {b : Γ(X, ⊤)} (hb : b ∈ nonZeroDivisors Γ(X, ⊤)) :
    Reg b := by
  intro x
  have hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  let x' : (⊤ : X.Opens) := ⟨x, trivial⟩
  let _ := X.presheaf.algebra_section_stalk x'
  have hl := hU.isLocalization_stalk x'
  have hf : (X.presheaf.germ ⊤ x trivial).hom.Flat :=
    IsLocalization.flat (X.presheaf.stalk x'.1) (hU.primeIdealOf x').asIdeal.primeCompl
  exact flat_nzd _ hf hb

private lemma reg_cancel {X : Scheme.{0}} {b : Γ(X, ⊤)} (hb : Reg b) (O : X.Opens) (z : Γ(X, O))
    (h : z * (X.presheaf.map (homOfLE le_top : O ⟶ ⊤).op).hom b = 0) : z = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf O z 0 fun x hx => ?_
  have h1 := congrArg (X.presheaf.germ O x hx).hom h
  rw [map_mul, map_zero] at h1
  have h2 : (X.presheaf.germ O x hx).hom ((X.presheaf.map (homOfLE le_top : O ⟶ ⊤).op).hom b) = (X.presheaf.germ ⊤ x trivial).hom b :=
    X.presheaf.germ_res_apply _ _ _ _
  rw [h2] at h1
  rw [map_zero]
  exact (mem_nonZeroDivisors_iff_right.1 (hb x)) _ h1

private lemma glue_div {X : Scheme.{0}} (a b : Γ(X, ⊤)) (hb : Reg b)
    (h : ∀ x : X, ∃ (O : X.Opens) (w : Γ(O, ⊤)), x ∈ O ∧ O.ι.appTop.hom a = w * O.ι.appTop.hom b) :
    ∃ w : Γ(X, ⊤), a = w * b := by
  choose O w hx hw using h
  have res' (U : X.Opens) : U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op :=
    (X.presheaf.map_comp _ _).symm.trans rfl
  have res (U : X.Opens) (c : Γ(X, ⊤)) : U.topIso.hom.hom (U.ι.appTop.hom c) = (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom c :=
    congrArg (fun f => f.hom c) (res' U)
  let W (x : X) : Γ(X, O x) := (O x).topIso.hom.hom (w x)
  have hW (x : X) : (X.presheaf.map (homOfLE le_top : O x ⟶ ⊤).op).hom a = W x * (X.presheaf.map (homOfLE le_top : O x ⟶ ⊤).op).hom b := by
    rw [← res, ← res, hw, map_mul]
  have rr {A B C : X.Opens} (h₁ : C ≤ B) (h₂ : B ≤ A) (t : Γ(X, A)) :
      (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom t) = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom t := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hcomp (x y : X) : (X.presheaf.map (homOfLE inf_le_left : O x ⊓ O y ⟶ O x).op).hom (W x) = (X.presheaf.map (homOfLE inf_le_right : O x ⊓ O y ⟶ O y).op).hom (W y) := by
    refine sub_eq_zero.1 (reg_cancel hb (O x ⊓ O y) _ ?_)
    have e1 := congrArg (X.presheaf.map (homOfLE inf_le_left : O x ⊓ O y ⟶ O x).op).hom (hW x)
    have e2 := congrArg (X.presheaf.map (homOfLE inf_le_right : O x ⊓ O y ⟶ O y).op).hom (hW y)
    rw [map_mul, rr] at e1 e2
    rw [rr] at e1 e2
    rw [sub_mul, ← e1, ← e2, sub_self]
  obtain ⟨c, hc⟩ : ∃ c : Γ(X, ⊤), ∀ x, (X.presheaf.map (homOfLE le_top : O x ⟶ ⊤).op).hom c = W x := by
    obtain ⟨c, hc, -⟩ := X.sheaf.existsUnique_gluing' O ⊤ (fun x => homOfLE le_top)
      (fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩) W hcomp
    exact ⟨c, hc⟩
  refine ⟨c, ?_⟩
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ _ _ fun x _ => ?_
  have h1 := hW x
  rw [← hc x, ← map_mul] at h1
  have h2 := congrArg (X.presheaf.germ (O x) x (hx x)).hom h1
  rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply] at h2
  exact h2

private lemma appTop_comp {X Y Z : Scheme.{0}} (g : X ⟶ Y) (a : Y ⟶ Z) (s : Γ(Z, ⊤)) :
    (g ≫ a).appTop.hom s = g.appTop.hom (a.appTop.hom s) := by
  rw [Scheme.Hom.comp_appTop]
  rfl

private lemma topIso_res {Y : Scheme.{0}} {W U : Y.Opens} (h : W ≤ U) (s : Γ(Y, U)) :
    (Y.homOfLE h).appTop.hom (U.topIso.inv.hom s) = W.topIso.inv.hom ((Y.presheaf.map (homOfLE h).op).hom s) := by
  have e : U.topIso.inv ≫ (Y.homOfLE h).appTop = Y.presheaf.map (homOfLE h).op ≫ W.topIso.inv := by
    rw [Scheme.homOfLE_appTop]
    exact (Y.presheaf.map_comp _ _).symm.trans (Eq.trans rfl (Y.presheaf.map_comp (homOfLE h).op (eqToIso W.ι_image_top.symm).op.inv))
  exact congrArg (fun t => t.hom s) e

private lemma sigma_section {I : Type} (V : I → Scheme.{0}) (s : ∀ i, Γ(V i, ⊤)) :
    ∃ s0 : Γ(∐ V, ⊤), ∀ i, (Sigma.ι V i).appTop.hom s0 = s i := by
  let R : CommRingCat.{0} := CommRingCat.of (Polynomial ℤ)
  let φ (i : I) : R ⟶ Γ(V i, ⊤) := CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) (s i))
  let m (i : I) : V i ⟶ Spec R := (V i).toSpecΓ ≫ Spec.map (φ i)
  refine ⟨(Sigma.desc m).appTop.hom ((Scheme.ΓSpecIso R).inv.hom Polynomial.X), fun i => ?_⟩
  rw [← appTop_comp, Sigma.ι_desc]
  have e : m i = (V i).toSpecΓ ≫ Spec.map (φ i) := rfl
  rw [e, appTop_comp]
  have h1 : (Spec.map (φ i)).appTop.hom ((Scheme.ΓSpecIso R).inv.hom Polynomial.X) = (Scheme.ΓSpecIso _).inv.hom ((φ i).hom Polynomial.X) :=
    (congrArg (fun t => t.hom Polynomial.X) (Scheme.ΓSpecIso_inv_naturality (φ i))).symm
  rw [h1, Scheme.toSpecΓ_appTop]
  have h2 : (φ i).hom Polynomial.X = s i := Polynomial.eval₂_X _ _
  rw [h2]
  exact congrArg (fun t => t.hom (s i)) (Scheme.ΓSpecIso _).inv_hom_id

private lemma reg_sigma {I : Type} (V : I → Scheme.{0}) (s0 : Γ(∐ V, ⊤))
    (h : ∀ i, Reg ((Sigma.ι V i).appTop.hom s0)) : Reg s0 := by
  intro x
  obtain ⟨⟨i, p⟩, rfl⟩ := (sigmaMk V).surjective x
  rw [sigmaMk_mk]
  have hi := h i p
  have e := Scheme.Hom.germ_stalkMap_apply (Sigma.ι V i) ⊤ p trivial s0
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  have h1 := congrArg ((Sigma.ι V i).stalkMap p).hom hy
  rw [map_mul, map_zero] at h1
  have h2 : ((Sigma.ι V i).stalkMap p).hom y * (V i).presheaf.germ ⊤ p trivial ((Sigma.ι V i).appTop.hom s0) = 0 := by
    rw [← h1]
    congr 1
    exact e.symm
  have h3 := mem_nonZeroDivisors_iff_right.1 hi _ h2
  exact (ConcreteCategory.bijective_of_isIso ((Sigma.ι V i).stalkMap p)).1 (h3.trans (map_zero _).symm)

private lemma local_div {Y : Scheme.{0}} {I : Type} (U : I → Y.Opens) (s : ∀ i, Γ(Y, U i))
    (hdiv : ∀ i i' y, y ∈ U i → y ∈ U i' → ∃ (W : Y.Opens) (h : W ≤ U i) (h' : W ≤ U i') (c : Γ(Y, W)), y ∈ W ∧
      (Y.presheaf.map (homOfLE h).op).hom (s i) = c * (Y.presheaf.map (homOfLE h').op).hom (s i'))
    {s0 : Γ(∐ fun i => (U i : Scheme.{0}), ⊤)}
    (hs0 : ∀ i, (Sigma.ι (fun i => (U i : Scheme.{0})) i).appTop.hom s0 = (U i).topIso.inv.hom (s i))
    {X : Scheme.{0}} (a b : X ⟶ ∐ fun i => (U i : Scheme.{0}))
    (hab : a ≫ Sigma.desc (fun i => (U i).ι) = b ≫ Sigma.desc (fun i => (U i).ι)) (x : X) :
    ∃ (O : X.Opens) (w : Γ(O, ⊤)), x ∈ O ∧ O.ι.appTop.hom (a.appTop.hom s0) = w * O.ι.appTop.hom (b.appTop.hom s0) := by
  let F : (∐ fun i => (U i : Scheme.{0})) ⟶ Y := Sigma.desc (fun i => (U i).ι)
  have hF (i) : Sigma.ι (fun i => (U i : Scheme.{0})) i ≫ F = (U i).ι := Sigma.ι_desc _ _
  obtain ⟨⟨i, p⟩, hp⟩ := (sigmaMk fun i => (U i : Scheme.{0})).surjective (a x)
  obtain ⟨⟨i', p'⟩, hp'⟩ := (sigmaMk fun i => (U i : Scheme.{0})).surjective (b x)
  rw [sigmaMk_mk] at hp hp'
  have hy : (a ≫ F) x = p.1 := by
    rw [Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply, hF]
    rfl
  have hy' : (a ≫ F) x = p'.1 := by
    have : a ≫ F = b ≫ F := hab
    rw [this, Scheme.Hom.comp_apply, ← hp', ← Scheme.Hom.comp_apply, hF]
    rfl
  obtain ⟨W, h, h', c, hyW, hc⟩ := hdiv i i' ((a ≫ F) x) (hy ▸ p.2) (hy' ▸ p'.2)
  let ρ : (W : Scheme.{0}) ⟶ _ := Y.homOfLE h ≫ Sigma.ι (fun i => (U i : Scheme.{0})) i
  let ρ' : (W : Scheme.{0}) ⟶ _ := Y.homOfLE h' ≫ Sigma.ι (fun i => (U i : Scheme.{0})) i'
  have hρ : ρ ≫ F = W.ι := by simp only [ρ, Category.assoc, hF, Scheme.homOfLE_ι]
  have hρ' : ρ' ≫ F = W.ι := by simp only [ρ', Category.assoc, hF, Scheme.homOfLE_ι]
  have hq : Y.homOfLE h ⟨_, hyW⟩ = p := Subtype.ext ((Scheme.homOfLE_apply h ⟨_, hyW⟩).trans hy)
  have hq' : Y.homOfLE h' ⟨_, hyW⟩ = p' := Subtype.ext ((Scheme.homOfLE_apply h' ⟨_, hyW⟩).trans hy')
  have hr : a x ∈ Set.range ρ := ⟨⟨_, hyW⟩, (Scheme.Hom.comp_apply _ _ _).trans ((congrArg _ hq).trans hp)⟩
  have hr' : b x ∈ Set.range ρ' := ⟨⟨_, hyW⟩, (Scheme.Hom.comp_apply _ _ _).trans ((congrArg _ hq').trans hp')⟩
  let O : X.Opens := a ⁻¹ᵁ ρ.opensRange ⊓ b ⁻¹ᵁ ρ'.opensRange
  have e1 : Set.range (O.ι ≫ a) ⊆ Set.range ρ := by
    rintro _ ⟨t, rfl⟩
    exact t.2.1
  have e2 : Set.range (O.ι ≫ b) ⊆ Set.range ρ' := by
    rintro _ ⟨t, rfl⟩
    exact t.2.2
  let m := IsOpenImmersion.lift ρ (O.ι ≫ a) e1
  let m' := IsOpenImmersion.lift ρ' (O.ι ≫ b) e2
  have hm : m ≫ ρ = O.ι ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hm' : m' ≫ ρ' = O.ι ≫ b := IsOpenImmersion.lift_fac _ _ _
  have hmm : m = m' := by
    have e3 : m ≫ W.ι = m' ≫ W.ι := calc
      m ≫ W.ι = (m ≫ ρ) ≫ F := by rw [Category.assoc, hρ]
      _ = (m' ≫ ρ') ≫ F := by
        rw [hm, hm', Category.assoc, Category.assoc]
        exact congrArg (O.ι ≫ ·) hab
      _ = m' ≫ W.ι := by rw [Category.assoc, hρ']
    exact (cancel_mono W.ι).1 e3
  have t1 : ρ.appTop.hom s0 = W.topIso.inv.hom ((Y.presheaf.map (homOfLE h).op).hom (s i)) := by
    rw [appTop_comp, hs0, topIso_res]
  have t2 : ρ'.appTop.hom s0 = W.topIso.inv.hom ((Y.presheaf.map (homOfLE h').op).hom (s i')) := by
    rw [appTop_comp, hs0, topIso_res]
  refine ⟨O, m.appTop.hom (W.topIso.inv.hom c), ⟨hr, hr'⟩, ?_⟩
  have u1 : O.ι.appTop.hom (a.appTop.hom s0) = m.appTop.hom (ρ.appTop.hom s0) := by
    rw [← appTop_comp, ← appTop_comp, hm]
  have u2 : O.ι.appTop.hom (b.appTop.hom s0) = m.appTop.hom (ρ'.appTop.hom s0) := by
    rw [hmm, ← appTop_comp, ← appTop_comp, hm']
  rw [u1, u2, t1, t2, hc, map_mul, map_mul]

private lemma reg_cancel_top {X : Scheme.{0}} {b : Γ(X, ⊤)} (hb : Reg b) (z : Γ(X, ⊤)) (h : z * b = 0) : z = 0 := by
  refine reg_cancel hb ⊤ z ?_
  have e : X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op = 𝟙 _ := X.presheaf.map_id _
  rw [e]
  exact h

private lemma nzd_topIso {Y : Scheme.{0}} {V : Y.Opens} {s : Γ(Y, V)} (hs : s ∈ nonZeroDivisors Γ(Y, V)) :
    V.topIso.inv.hom s ∈ nonZeroDivisors Γ(V, ⊤) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  have h1 := congrArg V.topIso.hom.hom hy
  rw [map_mul, map_zero] at h1
  have h2 : V.topIso.hom.hom (V.topIso.inv.hom s) = s := congrArg (fun t => t.hom s) V.topIso.inv_hom_id
  rw [h2] at h1
  have h3 := mem_nonZeroDivisors_iff_right.1 hs _ h1
  have h4 : V.topIso.inv.hom (V.topIso.hom.hom y) = y := congrArg (fun t => t.hom y) V.topIso.hom_inv_id
  rw [← h4, h3, map_zero]

private lemma ker_div {Y T : Scheme.{0}} (j : T ⟶ Y) [IsClosedImmersion j] {V V' : Y.Opens} {s : Γ(Y, V)} {s' : Γ(Y, V')}
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hk : RingHom.ker (j.app V).hom = Ideal.span {s})
    (hk' : RingHom.ker (j.app V').hom = Ideal.span {s'}) (y : Y) (hy : y ∈ V) (hy' : y ∈ V') :
    ∃ (W : Y.Opens) (h : W ≤ V) (h' : W ≤ V') (c : Γ(Y, W)), y ∈ W ∧
      (Y.presheaf.map (homOfLE h).op).hom s = c * (Y.presheaf.map (homOfLE h').op).hom s' := by
  obtain ⟨W, hWa, hyW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := V ⊓ V') (x := y) ⟨hy, hy'⟩
  have h : W ≤ V := fun x hx => (hle hx).1
  have h' : W ≤ V' := fun x hx => (hle hx).2
  have m1 := j.ker.map_ideal (U := ⟨W, hWa⟩) (V := ⟨V, hV⟩) h
  have m2 := j.ker.map_ideal (U := ⟨W, hWa⟩) (V := ⟨V', hV'⟩) h'
  rw [Scheme.Hom.ker_apply, hk, Ideal.map_span, Set.image_singleton] at m1
  rw [Scheme.Hom.ker_apply, hk', Ideal.map_span, Set.image_singleton] at m2
  have m3 := m1.trans m2.symm
  have m4 : (Y.presheaf.map (homOfLE h).op).hom s ∈ Ideal.span {(Y.presheaf.map (homOfLE h').op).hom s'} := by
    have : (Y.presheaf.map (homOfLE h).op).hom s ∈ Ideal.span {(Y.presheaf.map (homOfLE h).op).hom s} :=
      Ideal.subset_span rfl
    exact m3 ▸ this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 m4
  exact ⟨W, h, h', c, hyW, hc.symm⟩

private lemma off_image {Y T : Scheme.{0}} (j : T ⟶ Y) [IsClosedImmersion j] {V : Y.Opens} {s : Γ(Y, V)}
    (hV : IsAffineOpen V) (hk : RingHom.ker (j.app V).hom = Ideal.span {s}) (y : Y) (hy : y ∈ V)
    (hj : y ∉ Set.range j) : y ∈ Y.basicOpen s := by
  by_contra hns
  apply hj
  have h1 : y ∈ j.ker.support := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hy, Scheme.mem_zeroLocus_iff]
    intro g hg hgy
    rw [Scheme.Hom.ker_apply] at hg
    have hg' : g ∈ RingHom.ker (j.app V).hom := hg
    rw [hk] at hg'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hg'
    rw [Scheme.basicOpen_mul] at hgy
    exact hns hgy.2
  have h2 : y ∈ (j.ker.support : Set Y) := h1
  rw [Scheme.Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq] at h2
  exact h2

private lemma line_core {Y : Scheme.{0}} {I : Type} (U : I → Y.Opens) (s : ∀ i, Γ(Y, U i))
    (haff : ∀ i, IsAffineOpen (U i)) (hnz : ∀ i, s i ∈ nonZeroDivisors Γ(Y, U i)) (hcov : ∀ y : Y, ∃ i, y ∈ U i)
    (hdiv : ∀ i i' y, y ∈ U i → y ∈ U i' → ∃ (W : Y.Opens) (h : W ≤ U i) (h' : W ≤ U i') (c : Γ(Y, W)), y ∈ W ∧
      (Y.presheaf.map (homOfLE h).op).hom (s i) = c * (Y.presheaf.map (homOfLE h').op).hom (s i')) :
    ∃ (D : E.LineData Y) (f : ∀ {V : Scheme.{0}} (_ : V ⟶ D.Y), Γ(V, ⊤)),
      Etale D.f ∧
      (∀ {V' V : Scheme.{0}} (g : V' ⟶ V) (a : V ⟶ D.Y), f (g ≫ a) = g.appTop.hom (f a)) ∧
      (∀ {V : Scheme.{0}} (a b : V ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f), f a = (D.u a b h : Γ(V, ⊤)) * f b) ∧
      (∀ {V : Scheme.{0}} (a : V ⟶ D.Y), (∀ (v : V) i, (a ≫ D.f) v ∈ U i → (a ≫ D.f) v ∈ Y.basicOpen (s i)) → IsUnit (f a)) ∧
      ∀ i, ∃ σ : (U i : Scheme.{0}) ⟶ D.Y, σ ≫ D.f = (U i).ι ∧ f σ = (U i).topIso.inv.hom (s i) := by
  let C : Scheme.{0} := ∐ fun i => (U i : Scheme.{0})
  let F : C ⟶ Y := Sigma.desc fun i => (U i).ι
  have hF (i) : Sigma.ι (fun i => (U i : Scheme.{0})) i ≫ F = (U i).ι := Sigma.ι_desc _ _
  have hEt : Etale F := IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
  have hFl : Flat F := IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
  have hSm : Smooth F := IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
  have hSu : Surjective F := ⟨fun y => by
    obtain ⟨i, hi⟩ := hcov y
    have e : (Sigma.ι (fun i => (U i : Scheme.{0})) i ≫ F) ⟨y, hi⟩ = y := by
      rw [hF]
      rfl
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans e⟩⟩
  obtain ⟨s0, hs0⟩ := sigma_section (fun i => (U i : Scheme.{0})) fun i => (U i).topIso.inv.hom (s i)
  have hreg : Reg s0 := reg_sigma _ _ fun i => by
    rw [hs0]
    have : IsAffine (U i : Scheme.{0}) := haff i
    exact reg_of_affine (nzd_topIso (hnz i))
  have hd {X : Scheme.{0}} (a b : X ⟶ C) (h : a ≫ F = b ≫ F) (hb : Reg (b.appTop.hom s0)) :
      ∃ w : Γ(X, ⊤), a.appTop.hom s0 = w * b.appTop.hom s0 :=
    glue_div _ _ hb (local_div U s hdiv hs0 a b h)
  obtain ⟨w, hw⟩ := hd (pullback.fst F F) (pullback.snd F F) pullback.condition (reg_flat _ hreg)
  obtain ⟨w', hw'⟩ := hd (pullback.snd F F) (pullback.fst F F) pullback.condition.symm (reg_flat _ hreg)
  have hww : w * w' = 1 := by
    refine sub_eq_zero.1 (reg_cancel_top (reg_flat (pullback.fst F F) hreg) _ ?_)
    rw [sub_mul, mul_assoc, ← hw', ← hw, one_mul, sub_self]
  let wu : (Γ(pullback F F, ⊤))ˣ := ⟨w, w', hww, by rw [mul_comm]; exact hww⟩
  let u : ∀ {V : Scheme.{0}} (a b : V ⟶ C), a ≫ F = b ≫ F → (Γ(V, ⊤))ˣ := fun a b h =>
    Units.map (pullback.lift a b h).appTop.hom.toMonoidHom wu
  have hu {V : Scheme.{0}} (a b : V ⟶ C) (h : a ≫ F = b ≫ F) :
      a.appTop.hom s0 = (u a b h : Γ(V, ⊤)) * b.appTop.hom s0 := by
    have e1 := congrArg (pullback.lift a b h).appTop.hom hw
    rw [map_mul, ← appTop_comp, ← appTop_comp, pullback.lift_fst, pullback.lift_snd] at e1
    exact e1
  have unat {V' V : Scheme.{0}} (g : V' ⟶ V) (a b : V ⟶ C) (h : a ≫ F = b ≫ F) :
      u (g ≫ a) (g ≫ b) (by rw [Category.assoc, h, Category.assoc]) = Units.map g.appTop.hom.toMonoidHom (u a b h) := by
    apply Units.ext
    have e : pullback.lift (g ≫ a) (g ≫ b) (by rw [Category.assoc, h, Category.assoc]) = g ≫ pullback.lift a b h := by
      exact pullback.hom_ext (by rw [pullback.lift_fst, Category.assoc, pullback.lift_fst])
        (by rw [pullback.lift_snd, Category.assoc, pullback.lift_snd])
    change (pullback.lift (g ≫ a) (g ≫ b) _).appTop.hom w = g.appTop.hom ((pullback.lift a b h).appTop.hom w)
    rw [e, appTop_comp]
  have ukey {V : Scheme.{0}} (a b c : V ⟶ C) (h : a ≫ F = b ≫ F) (h' : b ≫ F = c ≫ F) (hc : Reg (c.appTop.hom s0)) :
      u a b h * u b c h' = u a c (h.trans h') := by
    apply Units.ext
    refine sub_eq_zero.1 (reg_cancel_top hc _ ?_)
    rw [sub_mul, Units.val_mul, mul_assoc, ← hu, ← hu, ← hu, sub_self]
  have ucoc {V : Scheme.{0}} (a b c : V ⟶ C) (h : a ≫ F = b ≫ F) (h' : b ≫ F = c ≫ F) :
      u a b h * u b c h' = u a c (h.trans h') := by
    let Q := pullback (pullback.snd F F) (pullback.fst F F)
    let q1 : Q ⟶ C := pullback.fst _ _ ≫ pullback.fst F F
    let q2 : Q ⟶ C := pullback.fst _ _ ≫ pullback.snd F F
    let q3 : Q ⟶ C := pullback.snd _ _ ≫ pullback.snd F F
    have hq : pullback.fst (pullback.snd F F) (pullback.fst F F) ≫ pullback.snd F F =
        pullback.snd (pullback.snd F F) (pullback.fst F F) ≫ pullback.fst F F := pullback.condition
    have k1 : q1 ≫ F = q2 ≫ F := by
      simp only [q1, q2, Category.assoc]
      rw [pullback.condition (f := F) (g := F)]
    have k2 : q2 ≫ F = q3 ≫ F := by
      simp only [q2, q3]
      rw [hq, Category.assoc, Category.assoc, pullback.condition (f := F) (g := F)]
    have hk := ukey q1 q2 q3 k1 k2 (reg_flat _ hreg)
    let l : V ⟶ Q := pullback.lift (pullback.lift a b h) (pullback.lift b c h') (by rw [pullback.lift_snd, pullback.lift_fst])
    have hl1 : l ≫ pullback.fst _ _ = pullback.lift a b h := pullback.lift_fst _ _ _
    have hl2 : l ≫ pullback.snd _ _ = pullback.lift b c h' := pullback.lift_snd _ _ _
    have l1 : l ≫ q1 = a := by
      simp only [q1]
      rw [← Category.assoc, hl1, pullback.lift_fst]
    have l2 : l ≫ q2 = b := by
      simp only [q2]
      rw [← Category.assoc, hl1, pullback.lift_snd]
    have l3 : l ≫ q3 = c := by
      simp only [q3]
      rw [← Category.assoc, hl2, pullback.lift_snd]
    have ucg {a a' b b' : V ⟶ C} (e : a = a') (e' : b = b') (h) (h') : u a b h = u a' b' h' := by
      subst e e'
      rfl
    have hk' := congrArg (Units.map l.appTop.hom.toMonoidHom) hk
    rw [map_mul, ← unat, ← unat, ← unat] at hk'
    rw [ucg l1.symm l2.symm h (by simp only [Category.assoc, k1]), ucg l2.symm l3.symm h' (by simp only [Category.assoc, k2]),
      ucg l1.symm l3.symm (h.trans h') (by simp only [Category.assoc, k1, k2])]
    exact hk'
  refine ⟨{ Y := C, f := F, sm := hSm, surj := hSu, u := u, nat := unat, coc := ucoc }, fun a => a.appTop.hom s0, hEt,
    fun g a => appTop_comp g a s0, hu, ?_, fun i => ⟨Sigma.ι (fun i => (U i : Scheme.{0})) i, hF i, hs0 i⟩⟩
  intro V a ha
  refine V.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun v hv => (V.mem_basicOpen _ v hv).1 ?_
  have e1 : a v ∈ C.basicOpen s0 := by
    obtain ⟨⟨i, p⟩, hp⟩ := (sigmaMk fun i => (U i : Scheme.{0})).surjective (a v)
    rw [sigmaMk_mk] at hp
    have hy : (a ≫ F) v = p.1 := by
      rw [Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply, hF]
      rfl
    have h1 := ha v i (hy ▸ p.2)
    rw [hy, ← Scheme.Opens.ι_image_basicOpen_topIso_inv] at h1
    obtain ⟨q, hq, hqp⟩ := h1
    have hqp' : q = p := (U i).ι.isOpenEmbedding.injective hqp
    subst hqp'
    have h2 : q ∈ Sigma.ι (fun i => (U i : Scheme.{0})) i ⁻¹ᵁ C.basicOpen s0 := by
      rw [Scheme.preimage_basicOpen]
      exact (hs0 i).symm ▸ hq
    exact hp ▸ h2
  have e2 : v ∈ a ⁻¹ᵁ C.basicOpen s0 := e1
  rw [Scheme.preimage_basicOpen] at e2
  exact e2

theorem lineEx : LineEx := by
  intro Y T j _ hc
  let I := {p : (Σ V : Y.Opens, Γ(Y, V)) // IsAffineOpen p.1 ∧ p.2 ∈ nonZeroDivisors Γ(Y, p.1) ∧
    RingHom.ker (j.app p.1).hom = Ideal.span {p.2}}
  obtain ⟨D, f, hEt, h1, h2, h3, h4⟩ := line_core (I := I) (fun i => i.1.1) (fun i => i.1.2) (fun i => i.2.1)
    (fun i => i.2.2.1)
    (fun y => by
      obtain ⟨V, s, hy, ha, hn, hk⟩ := hc y
      exact ⟨⟨⟨V, s⟩, ha, hn, hk⟩, hy⟩)
    (fun i i' y hy hy' => ker_div j i.2.1 i'.2.1 i.2.2.2 i'.2.2.2 y hy hy')
  refine ⟨D, f, h1, h2, fun a ha => h3 a fun v i hv => off_image j i.2.1 i.2.2.2 _ hv (ha v), ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨V, s, hy, ha, hn, hk⟩ := hc y
    obtain ⟨σ, hσ, -⟩ := h4 ⟨⟨V, s⟩, ha, hn, hk⟩
    exact Opens.mem_sSup.2 ⟨V, ⟨σ, hσ⟩, hy⟩
  · exact ⟨hEt, fun V s ha hn hk => h4 ⟨⟨V, s⟩, ha, hn, hk⟩⟩

end UpperTheory.Gal.KunnethLefschetz.G
