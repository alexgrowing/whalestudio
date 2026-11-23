import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings

structure IsCompleteLocalNormal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop where
  noeth : IsNoetherianRing R
  normal : IsIntegrallyClosed R
  complete : IsAdicComplete (IsLocalRing.maximalIdeal R) R

structure IsAdicNormalPair (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) : Prop where
  noeth : IsNoetherianRing R
  normal : IsIntegrallyClosed R
  complete : IsAdicComplete I R

theorem IsCompleteLocalNormal.pair {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (h : IsCompleteLocalNormal R) : IsAdicNormalPair R (IsLocalRing.maximalIdeal R) :=
  ⟨h.noeth, h.normal, h.complete⟩

theorem isCompleteLocalNormal_padicInt (p : ℕ) [Fact p.Prime] : IsCompleteLocalNormal ℤ_[p] :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem isAdicNormalPair_powerSeries (O : Type) [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] :
    IsAdicNormalPair (PowerSeries O) (Ideal.span {PowerSeries.X}) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

section Points

variable {S : Scheme.{0}} (B : Over S) [GrpObj B]

def laφ {T : Over S} (x y : T ⟶ B) : Fin 4 → (T.left ⟶ B.left) :=
  ![(padd B x y).left, x.left, y.left, (pzero B T).left]

def laε : Fin 4 → ℤ := ![1, -1, -1, 1]

def laDualε : Fin 4 → ℤ := ![-1, 1, 1, -1]

def symφ : Fin 2 → (B.left ⟶ B.left) := ![(GrpObj.inv : B ⟶ B).left, 𝟙 B.left]

def symε : Fin 2 → ℤ := ![1, -1]

def cubeAt {M : RigLB B} (t : CubicalStr B M) {T : Over S} (x y z : T ⟶ B) :
    LB.Gen (LB.LinComb M.L
      (fun k => (lift x (lift y z) : T ⟶ G3 B).left ≫ thφ B (x3 B) k) thε) :=
  LB.pullGen M.L (thφ B (x3 B)) thε t.t (lift x (lift y z) : T ⟶ G3 B).left

end Points

variable (R : Type) [CommRing R] [IsDomain R]

abbrev base : Scheme.{0} := Spec (CommRingCat.of R)

def genPt : Over (base R) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))

structure RawDeg where

  P : PolAV (base R)

  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen

  cube : CubicalStr P.A ⟨P.L, rig, P.isLB, rig_gen⟩

  sym : LB.Gen (LB.LinComb P.L (symφ P.A) symε)
  sym_gen : sym.IsGen

  sym_rig : LB.Gen.Corr P.L _ _ _ _
    (LB.pullGen P.L (symφ P.A) symε sym (eSec P.A)) (LB.oneGen P.L)

  X : Type
  [addCommGroup : AddCommGroup X]
  [free : Module.Free ℤ X]
  [finite : Module.Finite ℤ X]

  c : X → (𝟙_ (Over (base R)) ⟶ P.A)
  c_add : ∀ χ χ', c (χ + χ') = padd P.A (c χ) (c χ')

  ψ : ∀ χ, LB.Gen (LB.LinComb P.L (K := PUnit)
    (fun _ => (toUnit (genPt R) ≫ c χ).left) (fun _ => -1))
  ψ_gen : ∀ χ, (ψ χ).IsGen

attribute [instance] RawDeg.addCommGroup RawDeg.free RawDeg.finite

namespace RawDeg

variable {R} (D : RawDeg R)

abbrev cT (T : Over (base R)) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

abbrev cK (χ : D.X) : genPt R ⟶ D.P.A := D.cT (genPt R) χ

theorem cT_add (T : Over (base R)) (χ χ' : D.X) :
    D.cT T (χ + χ') = padd D.P.A (D.cT T χ) (D.cT T χ') := by
  simp only [cT, D.c_add, padd, ← Category.assoc, comp_lift]

def oChi (χ : D.X) : LB D.P.A.left :=
  LB.LinComb D.P.L (laφ D.P.A (D.cT D.P.A χ) (𝟙 D.P.A)) laε

def ψAt (χ : D.X) (i : D.P.L.ι) (V : (genPt R).left.Opens)
    (h : V ≤ (D.cK χ).left ⁻¹ᵁ D.P.L.U i) : Γ((genPt R).left, V)ˣ :=
  res (U := LB.wchart D.P.L (K := PUnit) (fun _ => (D.cK χ).left) (fun _ => i))
    (fun _ hy => Set.mem_iInter.2 fun _ => h hy) ((D.ψ χ).s (fun _ => i))

def rigAt (i : D.P.L.ι) (V : (genPt R).left.Opens)
    (h : V ≤ (pzero D.P.A (genPt R)).left ⁻¹ᵁ D.P.L.U i) : Γ((genPt R).left, V)ˣ :=
  res (U := LB.wchart D.P.L (K := PUnit)
      (fun _ => (toUnit (genPt R)).left ≫ eSec D.P.A) (fun _ => i))
    (fun _ hy => Set.mem_iInter.2 fun _ => h hy)
    ((LB.pullGen D.P.L (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig
      (toUnit (genPt R)).left).s (fun _ => i))

def τ (χ χ' : D.X) :
    LB.Gen (LB.LinComb D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) laDualε) where
  s := fun j =>
    D.ψAt (χ + χ') (j 0) _ ((LB.wchart_le D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j 0).trans
      (le_of_eq (congrArg (fun f : genPt R ⟶ D.P.A => f.left ⁻¹ᵁ D.P.L.U (j 0))
        (D.cT_add (genPt R) χ χ').symm))) *
    (D.ψAt χ (j 1) _ (LB.wchart_le D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j 1))⁻¹ *
    (D.ψAt χ' (j 2) _ (LB.wchart_le D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j 2))⁻¹ *
    (D.rigAt (j 3) _ (LB.wchart_le D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j 3))⁻¹

structure PrePt (T : Over (base R)) where

  b : T ⟶ D.P.A

  ev : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (laφ D.P.A (D.cT T χ) b) laDualε)

structure PrePt.IsPt {D : RawDeg R} {T : Over (base R)} (g : D.PrePt T) : Prop where
  gen : ∀ χ, (g.ev χ).IsGen
  mul : ∀ χ χ', LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g.ev (χ + χ'))
      (cubeAt D.P.A D.cube (D.cT T χ) (D.cT T χ') g.b))
    (LB.mulGen D.P.L _ _ _ _ (g.ev χ) (g.ev χ'))

def io (y : D.X) : D.PrePt (genPt R) where
  b := D.cK y
  ev := fun χ => D.τ χ y

def cst (a : R) (U : (𝟙_ (Over (base R))).left.Opens) : Γ((𝟙_ (Over (base R))).left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (base R).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a

def lattice (χ : D.X) : LB (𝟙_ (Over (base R))).left :=
  LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)

def ψMem (J : Ideal R) (χ : D.X) : Prop :=
  ∃ (m : ℕ) (a : Fin m → R) (s : Fin m → LB.Sec (D.lattice χ)), (∀ n, a n ∈ J) ∧
    ∀ j : PUnit → D.P.L.ι,
      ((D.ψ χ).s j).val =
        ((toUnit (genPt R)).left.appLE ((D.lattice χ).U j)
          (LB.wchart D.P.L (K := PUnit) (fun _ => (D.cK χ).left) j)
          (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)).hom
          (∑ n, cst (a n) _ * (s n).f j)

structure IsDeg (I : Ideal R) : Prop where

  even : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.ψ (-χ))
      (LB.pullGen D.P.L (symφ D.P.A) symε D.sym (D.cK χ).left))
    (D.ψ χ)

  mul_left : ∀ χ₁ χ₂ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.τ (χ₁ + χ₂) χ)
      (cubeAt D.P.A D.cube (D.cK χ₁) (D.cK χ₂) (D.cK χ)))
    (LB.mulGen D.P.L _ _ _ _ (D.τ χ₁ χ) (D.τ χ₂ χ))

  mul_right : ∀ χ χ₁ χ₂, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.τ χ (χ₁ + χ₂))
      (cubeAt D.P.A D.cube (D.cK χ) (D.cK χ₁) (D.cK χ₂)))
    (LB.mulGen D.P.L _ _ _ _ (D.τ χ χ₁) (D.τ χ χ₂))

  mem : ∀ χ, χ ≠ 0 → D.ψMem I χ

  tendsto : ∀ e : ℕ, {χ | ¬ D.ψMem (I ^ e) χ}.Finite

theorem res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(Y, U)ˣ) :
    res h' (res h u) = res (h'.trans h) u := by
  ext
  simp only [res, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_ψAt {χ χ' : D.X} {i i' : D.P.L.ι} (e : χ = χ') (e' : i = i') {V V' W} (h h')
    (k : W ≤ V) (k' : W ≤ V') :
    res k (D.ψAt χ i V h) = res k' (D.ψAt χ' i' V' h') := by
  subst e e'
  exact (res_res _ _ _).trans (res_res _ _ _).symm

theorem res_rigAt {i i' : D.P.L.ι} (e' : i = i') {V V' W} (h h')
    (k : W ≤ V) (k' : W ≤ V') :
    res k (D.rigAt i V h) = res k' (D.rigAt i' V' h') := by
  subst e'
  exact (res_res _ _ _).trans (res_res _ _ _).symm

theorem quot_congr {A : Type} [CommGroup A] {a b c d a' b' c' d' : A} (h0 : a = a') (h1 : b = c')
    (h2 : c = b') (h3 : d = d') : a * b⁻¹ * c⁻¹ * d⁻¹ = a' * b'⁻¹ * c'⁻¹ * d'⁻¹ := by
  subst h0 h1 h2 h3
  rw [mul_right_comm a]

theorem τ_symm (χ χ' : D.X) : LB.Gen.Corr D.P.L _ _ _ _ (D.τ χ χ') (D.τ χ' χ) := by
  intro j j' _ _ h
  have h0 : j 0 = j' 0 := h 0 0 (by
    change (padd D.P.A (D.cK χ) (D.cK χ')).left = (padd D.P.A (D.cK χ') (D.cK χ)).left
    rw [← cT_add, ← cT_add, add_comm])
  have h1 : j 1 = j' 2 := h 1 2 rfl
  have h2 : j 2 = j' 1 := h 2 1 rfl
  have h3 : j 3 = j' 3 := h 3 3 rfl
  simp only [τ, map_mul, map_inv]
  exact quot_congr (D.res_ψAt (add_comm χ χ') h0 _ _ _ _) (D.res_ψAt rfl h1 _ _ _ _)
    (D.res_ψAt rfl h2 _ _ _ _) (D.res_rigAt h3 _ _ _ _)

theorem res_pull_res {Y Z : Scheme.{0}} (f : Z ⟶ Y) {U V : Y.Opens} (h : V ≤ U) {W : Z.Opens}
    (k : W ≤ f ⁻¹ᵁ V) (k' : W ≤ f ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    res k (pullU f V (res h u)) = res k' (pullU f U u) := by
  ext
  simp only [res, pullU, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  change ((Y.presheaf.map (homOfLE h).op ≫ f.appLE V W k).hom _) = (f.appLE U W k').hom _
  rw [Scheme.Hom.map_appLE]

theorem pull_pull {Y Z Z' : Scheme.{0}} (f : Z ⟶ Y) (g : Z' ⟶ Z) (U : Y.Opens) (u : Γ(Y, U)ˣ) :
    pullU g _ (pullU f U u) = pullU (g ≫ f) U u := rfl

theorem res_pull_res_pull {Y Z Z' : Scheme.{0}} (f : Z ⟶ Y) (g : Z' ⟶ Z) (U : Y.Opens)
    {V : Z.Opens} {W : Z'.Opens} (h : V ≤ f ⁻¹ᵁ U) (k : W ≤ g ⁻¹ᵁ V) (k' : W ≤ (g ≫ f) ⁻¹ᵁ U)
    (u : Γ(Y, U)ˣ) :
    res k (pullU g V (res h (pullU f U u))) = res k' (pullU (g ≫ f) U u) :=
  res_pull_res g h k k' _

def gAt (f : (genPt R).left ⟶ D.P.A.left) (i i' : D.P.L.ι) (W : (genPt R).left.Opens)
    (h : W ≤ f ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U i')) : Γ((genPt R).left, W)ˣ :=
  res h (pullU f _ (D.P.L.g i i'))

theorem ψAt_trans (χ : D.X) (i i' : D.P.L.ι) {V V' W} (h h') (k : W ≤ V) (k' : W ≤ V') (hW) :
    res k (D.ψAt χ i V h) = (D.gAt (D.cK χ).left i i' W hW)⁻¹ * res k' (D.ψAt χ i' V' h') := by
  have H := congrArg (res (le_inf (fun _ hy => Set.mem_iInter.2 fun _ => h (k hy))
    (fun _ hy => Set.mem_iInter.2 fun _ => h' (k' hy)) : W ≤ _ ⊓ _))
    (D.ψ_gen χ (fun _ => i) (fun _ => i'))
  rw [map_mul, res_res, res_res] at H
  refine (res_res _ _ _).trans (H.trans ?_)
  refine congrArg₂ (· * ·) ?_ ?_
  · simp only [LB.LinComb, Finset.univ_unique, Finset.prod_singleton, map_zpow, zpow_neg, zpow_one, map_inv]
    exact congrArg (·⁻¹) (res_res _ _ _)
  · exact (res_res _ _ _).symm

theorem rigAt_trans (i i' : D.P.L.ι) {V V' W} (h h') (k : W ≤ V) (k' : W ≤ V') (hW) :
    res k (D.rigAt i V h) =
      D.gAt (pzero D.P.A (genPt R)).left i i' W hW * res k' (D.rigAt i' V' h') := by
  have H := congrArg (fun u => res (U := (toUnit (genPt R)).left ⁻¹ᵁ
      ((D.P.L.pull (eSec D.P.A)).U (fun _ => i) ⊓ (D.P.L.pull (eSec D.P.A)).U (fun _ => i'))) (V := W)
    (fun _ hy => ⟨Set.mem_iInter.2 fun _ => h (k hy), Set.mem_iInter.2 fun _ => h' (k' hy)⟩)
      (pullU (toUnit (genPt R)).left _ u))
    (D.rig_gen (fun _ => i) (fun _ => i'))
  simp only [map_mul] at H
  have a1 : W ≤ (toUnit (genPt R)).left ⁻¹ᵁ (D.P.L.pull (eSec D.P.A)).U (fun _ => i) :=
    fun _ hy => Set.mem_iInter.2 fun _ => h (k hy)
  have a2 : W ≤ (toUnit (genPt R)).left ⁻¹ᵁ (D.P.L.pull (eSec D.P.A)).U (fun _ => i') :=
    fun _ hy => Set.mem_iInter.2 fun _ => h' (k' hy)
  refine ((res_res _ _ _).trans (res_res _ _ _)).trans
    ((res_pull_res _ _ _ a1 _).symm.trans (H.trans ?_))
  refine congrArg₂ (· * ·) ?_ ?_
  · have hg : ∀ hh, (D.P.L.pull (eSec D.P.A)).g (fun _ => i) (fun _ => i') =
        res (U := eSec D.P.A ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U i')) hh
          (pullU (eSec D.P.A) _ (D.P.L.g i i')) := by
      intro hh
      simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
      rfl
    rw [hg (le_inf
      (inf_le_left.trans (LB.wchart_le D.P.L (K := PUnit) (fun _ => eSec D.P.A) _ PUnit.unit))
      (inf_le_right.trans (LB.wchart_le D.P.L (K := PUnit) (fun _ => eSec D.P.A) _ PUnit.unit)))]
    exact res_pull_res_pull (eSec D.P.A) (toUnit (genPt R)).left (D.P.L.U i ⊓ D.P.L.U i') _ _ hW _
  · exact (res_pull_res _ _ _ a2 _).trans ((res_res _ _ _).trans (res_res _ _ _)).symm

theorem gAt_congr {f f' : (genPt R).left ⟶ D.P.A.left} (e : f = f') (i i' W h h') :
    D.gAt f i i' W h = D.gAt f' i i' W h' := by
  subst e; rfl

theorem τ_isGen (χ χ' : D.X) : (D.τ χ χ').IsGen := by
  intro j j'
  have w : ∀ k, LB.wchart D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j ⊓
      LB.wchart D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j' ≤
      laφ D.P.A (D.cK χ) (D.cK χ') k ⁻¹ᵁ (D.P.L.U (j k) ⊓ D.P.L.U (j' k)) := fun k =>
    le_inf (inf_le_left.trans (LB.wchart_le D.P.L _ j k))
      (inf_le_right.trans (LB.wchart_le D.P.L _ j' k))
  have e0 : (D.cK (χ + χ')).left = laφ D.P.A (D.cK χ) (D.cK χ') 0 :=
    congrArg (fun f : genPt R ⟶ D.P.A => f.left) (D.cT_add (genPt R) χ χ')
  have key : ∀ {A : Type} [CommGroup A] {a b c d a' b' c' d' g0 g0' g1 g2 g3 : A},
      g0 = g0' → a = g0⁻¹ * a' → b = g1⁻¹ * b' → c = g2⁻¹ * c' → d = g3 * d' →
      a * b⁻¹ * c⁻¹ * d⁻¹ = (g0' ^ (-1 : ℤ) * g1 ^ (1 : ℤ) * g2 ^ (1 : ℤ) * g3 ^ (-1 : ℤ)) *
        (a' * b'⁻¹ * c'⁻¹ * d'⁻¹) := by
    intro A _ a b c d a' b' c' d' g0 g0' g1 g2 g3 e h0 h1 h2 h3
    subst e h0 h1 h2 h3
    simp only [zpow_neg, zpow_one, mul_inv, inv_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hg : (LB.LinComb D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) laDualε).g j j' =
      D.gAt _ _ _ _ (w 0) ^ (-1 : ℤ) * D.gAt _ _ _ _ (w 1) ^ (1 : ℤ) *
        D.gAt _ _ _ _ (w 2) ^ (1 : ℤ) * D.gAt _ _ _ _ (w 3) ^ (-1 : ℤ) :=
    Fin.prod_univ_four _
  have hm : ∀ {A A' : Type} [CommGroup A] [CommGroup A'] (φ : A →* A') (a b c d : A),
      φ (a * b⁻¹ * c⁻¹ * d⁻¹) = φ a * (φ b)⁻¹ * (φ c)⁻¹ * (φ d)⁻¹ := by
    intro A A' _ _ φ a b c d
    simp only [map_mul, map_inv]
  have w0 : LB.wchart D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j ⊓
      LB.wchart D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j' ≤
      (D.cK (χ + χ')).left ⁻¹ᵁ (D.P.L.U (j 0) ⊓ D.P.L.U (j' 0)) := by
    rw [e0]; exact w 0
  refine (hm _ _ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) hg (hm _ _ _ _ _)).symm)
  exact key (D.gAt_congr e0 (j 0) (j' 0) _ w0 (w 0))
    (D.ψAt_trans (χ + χ') (j 0) (j' 0) _ _ _ _ w0)
    (D.ψAt_trans χ (j 1) (j' 1) _ _ _ _ (w 1)) (D.ψAt_trans χ' (j 2) (j' 2) _ _ _ _ (w 2))
    (D.rigAt_trans (j 3) (j' 3) _ _ _ _ (w 3))

theorem IsDeg.io_isPt {D : RawDeg R} {I : Ideal R} (h : D.IsDeg I) (y : D.X) : (D.io y).IsPt :=
  ⟨fun χ => D.τ_isGen χ y, fun χ χ' => h.mul_left χ χ' y⟩

end RawDeg

structure DegData (I : Ideal R) extends RawDeg R where
  isDeg : toRawDeg.IsDeg I

end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
