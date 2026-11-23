import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.ValConstOfPowEq

noncomputable section

section Units

variable {X Y Z : Scheme.{0}}

theorem res_res' {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (x : Γ(X, U)ˣ) :
    res k (res h x) = res (k.trans h) x := by
  ext
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE k).op).hom x.val = _
  rw [← X.presheaf.map_comp]
  rfl

theorem res_self' {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)ˣ) : res h x = x := by
  ext
  change (X.presheaf.map (𝟙 _)).hom x.val = _
  rw [X.presheaf.map_id]
  rfl

theorem res_pullU_res' (f : Y ⟶ X) {U V : X.Opens} (k : V ≤ U) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ V)
    (x : Γ(X, U)ˣ) :
    res h (pullU f V (res k x)) = res (h.trans (f.preimage_mono k)) (pullU f U x) := by
  ext
  change (X.presheaf.map (homOfLE k).op ≫ f.appLE V W h).hom x.val = (f.appLE U W _).hom x.val
  rw [Scheme.Hom.map_appLE]

theorem res_pullU_comp (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {W : Z.Opens}
    (h : W ≤ g ⁻¹ᵁ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU g _ (pullU f U x)) = res (U := (g ≫ f) ⁻¹ᵁ U) h (pullU (g ≫ f) U x) := rfl

theorem res_pullU_congr {a b : Y ⟶ X} (e : a = b) (U : X.Opens) {W : Y.Opens}
    (h : W ≤ a ⁻¹ᵁ U) (h' : W ≤ b ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU a U x) = res h' (pullU b U x) := by
  subst e; rfl

theorem prod_punit {M : Type} [CommGroup M] (x : M) : ∏ _k : PUnit.{1}, x ^ (1 : ℤ) = x := by
  simp

theorem pull_g (L : LB X) (q : Y ⟶ X) (i j : PUnit → L.ι) :
    (L.pull q).g i j = res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => q) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ => q) j PUnit.unit)))
      (pullU q _ (L.g (i PUnit.unit) (j PUnit.unit))) :=
  prod_punit _

theorem wchart_pull_top (L : LB X) (q : Y ⟶ X) (i : L.ι) (h : q ⁻¹ᵁ L.U i = ⊤) :
    ⊤ ≤ LB.wchart L (fun _ : PUnit => q) (fun _ => i) := by
  intro x _
  refine Set.mem_iInter.2 fun _ => ?_
  have : x ∈ q ⁻¹ᵁ L.U i := by rw [h]; trivial
  exact this

end Units

theorem isLocalRing_of_integers {C Γ₀ R : Type} [Field C] [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation C Γ₀} [CommRing R] [Algebra R C] (hv : v.Integers R) : IsLocalRing R := by
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra h
  push_neg at h
  have h1 : v (algebraMap R C a) < 1 :=
    lt_of_le_of_ne (hv.map_le_one a) (fun e => h.1 (hv.isUnit_of_one' e))
  have h2 : v (algebraMap R C (1 - a)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) (fun e => h.2 (hv.isUnit_of_one' e))
  have h3 := v.map_add (algebraMap R C a) (algebraMap R C (1 - a))
  have h4 : algebraMap R C a + algebraMap R C (1 - a) = 1 := by rw [← map_add]; simp
  rw [h4, v.map_one] at h3
  exact lt_irrefl _ (lt_of_le_of_lt h3 (max_lt h1 h2))

theorem exists_chart_top {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X)
    (hL : L.IsLB) (q : Spec (CommRingCat.of V) ⟶ X) : ∃ i, q ⁻¹ᵁ L.U i = ⊤ := by
  have hc : q.base (IsLocalRing.closedPoint V) ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  refine ⟨i, eq_top_iff.2 fun x _ => ?_⟩
  exact ((IsLocalRing.specializes_closedPoint x).map q.continuous).mem_open (L.U i).isOpen hi

section Exist

variable {X R : Type} {Z : Scheme.{0}}

def chartGen (D : LB Z) {Y : Scheme.{0}} (q : Y ⟶ Z) (j₀ : D.ι) (hj₀ : q ⁻¹ᵁ D.U j₀ = ⊤) :
    (D.pull q).Gen where
  s := fun j => res (fun x hx => ⟨LB.wchart_le D (fun _ => q) j PUnit.unit hx,
    show x ∈ q ⁻¹ᵁ D.U j₀ by rw [hj₀]; trivial⟩ : (D.pull q).U j ≤ q ⁻¹ᵁ (D.U (j PUnit.unit) ⊓ D.U j₀))
    (pullU q _ (D.g (j PUnit.unit) j₀))

theorem chartGen_isGen (D : LB Z) (hD : D.IsLB) {Y : Scheme.{0}} (q : Y ⟶ Z) (j₀ : D.ι)
    (hj₀ : q ⁻¹ᵁ D.U j₀ = ⊤) : (chartGen D q j₀ hj₀).IsGen := by
  intro i j
  have hW : (D.pull q).U i ⊓ (D.pull q).U j ≤
      q ⁻¹ᵁ (D.U (i PUnit.unit) ⊓ D.U (j PUnit.unit) ⊓ D.U j₀) := fun x hx =>
    ⟨⟨LB.wchart_le D (fun _ => q) i PUnit.unit hx.1, LB.wchart_le D (fun _ => q) j PUnit.unit hx.2⟩,
      show x ∈ q ⁻¹ᵁ D.U j₀ by rw [hj₀]; trivial⟩
  have a := congrArg (fun x => res hW (pullU q _ x)) (hD.cocycle (i PUnit.unit) (j PUnit.unit) j₀)
  simp only [map_mul, res_pullU_res'] at a
  exact (res_res' _ _ _).trans (a.symm.trans
    (congrArg₂ (· * ·) (pull_g D q i j).symm (res_res' _ _ _).symm))
end Exist

section Coord

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Z : Scheme.{0}} {f : Z ⟶ Spec (.of O)}

theorem top_le_generic {R C : Type} [CommRing R] [Field C] [Algebra R C] (D : LB Z)
    (ybar : Spec (.of R) ⟶ Z) (y : Spec (.of C) ⟶ genericFibre f)
    (hy : y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar)
    (j₀ : D.ι) (hj₀ : ybar ⁻¹ᵁ D.U j₀ = ⊤) :
    ⊤ ≤ y ⁻¹ᵁ (D.pull (genericι f)).U (fun _ => j₀) := by
  intro p _
  refine Set.mem_iInter.2 fun _ => ?_
  show (y ≫ genericι f).base p ∈ D.U j₀
  rw [hy]
  have : (Spec.map (CommRingCat.ofHom (algebraMap R C))).base p ∈ ybar ⁻¹ᵁ D.U j₀ := by
    rw [hj₀]; trivial
  exact this

theorem top_le_special {R C : Type} [CommRing R] [Field C] [Algebra R C] (D : LB Z)
    (ybar : Spec (.of R) ⟶ Z) (j₀ : D.ι) (hj₀ : ybar ⁻¹ᵁ D.U j₀ = ⊤) :
    ⊤ ≤ Spec.map (CommRingCat.ofHom (algebraMap R C)) ⁻¹ᵁ (D.pull ybar).U (fun _ => j₀) := by
  intro p _
  refine Set.mem_iInter.2 fun _ => ?_
  have : (Spec.map (CommRingCat.ofHom (algebraMap R C))).base p ∈ ybar ⁻¹ᵁ D.U j₀ := by
    rw [hj₀]; trivial
  exact this

theorem constUnit_id_ΓSpecIso {C : Type} [Field C] (u : Γ(Spec (.of C), ⊤)ˣ) :
    constUnit (𝟙 (Spec (.of C))) (Units.map (Scheme.ΓSpecIso (.of C)).hom.hom.toMonoidHom u) = u := by
  ext
  simp [constUnit]

theorem isCoord_chartGen {R C : Type} [CommRing R] [Field C] [Algebra R C] (D : LB Z)
    (sig : (D.pull (genericι f)).Gen) (hsig : sig.IsGen) (ybar : Spec (.of R) ⟶ Z)
    (y : Spec (.of C) ⟶ genericFibre f)
    (hy : y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar)
    (j₀ : D.ι) (hj₀ : ybar ⁻¹ᵁ D.U j₀ = ⊤) :
    IsCoord f D sig ybar y (chartGen D ybar j₀ hj₀)
      (Units.map (Scheme.ΓSpecIso (.of C)).hom.hom.toMonoidHom
        (res (top_le_generic D ybar y hy j₀ hj₀) (pullU y _ (sig.s (fun _ => j₀))))) := by
  intro j W h₁ h₂
  rw [constUnit_id_ΓSpecIso, res_res']
  have htop := top_le_generic D ybar y hy j₀ hj₀
  have hW : W ≤ y ⁻¹ᵁ ((D.pull (genericι f)).U j ⊓ (D.pull (genericι f)).U (fun _ => j₀)) :=
    fun p hp => ⟨h₁ hp, htop trivial⟩
  have a := congrArg (fun x => res hW (pullU y _ x)) (hsig j (fun _ => j₀))
  simp only [map_mul] at a
  have hle : (D.pull ybar).U j ≤ ybar ⁻¹ᵁ (D.U (j PUnit.unit) ⊓ D.U j₀) := fun x hx =>
    ⟨LB.wchart_le D (fun _ => ybar) j PUnit.unit hx, show x ∈ ybar ⁻¹ᵁ D.U j₀ by rw [hj₀]; trivial⟩
  have hD : W ≤ (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar) ⁻¹ᵁ (D.U (j PUnit.unit) ⊓ D.U j₀) :=
    h₂.trans ((Spec.map (CommRingCat.ofHom (algebraMap R C))).preimage_mono hle)
  have kA : (D.pull (genericι f)).U j ⊓ (D.pull (genericι f)).U (fun _ => j₀) ≤
      genericι f ⁻¹ᵁ (D.U (j PUnit.unit) ⊓ D.U j₀) :=
    le_inf (inf_le_left.trans (LB.wchart_le D (fun _ => genericι f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le D (fun _ => genericι f) (fun _ => j₀) PUnit.unit))
  have hB : W ≤ y ⁻¹ᵁ (genericι f ⁻¹ᵁ (D.U (j PUnit.unit) ⊓ D.U j₀)) := hW.trans (y.preimage_mono kA)
  have sA : res hW (pullU y _ ((D.pull (genericι f)).g j (fun _ => j₀))) =
      res hW (pullU y _ (res kA (pullU (genericι f) _ (D.g (j PUnit.unit) j₀)))) :=
    congrArg (fun x => res hW (pullU y _ x)) (pull_g D (genericι f) j (fun _ => j₀))
  have sB : res hW (pullU y _ (res kA (pullU (genericι f) _ (D.g (j PUnit.unit) j₀)))) =
      res hB (pullU y _ (pullU (genericι f) _ (D.g (j PUnit.unit) j₀))) :=
    res_pullU_res' y kA hW _
  have sC : res hB (pullU y _ (pullU (genericι f) _ (D.g (j PUnit.unit) j₀))) =
      res hD (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar) _ (D.g (j PUnit.unit) j₀)) :=
    (res_pullU_comp y (genericι f) _ hB _).trans (res_pullU_congr hy _ hB hD _)
  have sD : res hD (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar) _ (D.g (j PUnit.unit) j₀)) =
      res h₂ (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C))) _
        (res hle (pullU ybar _ (D.g (j PUnit.unit) j₀)))) :=
    (res_pullU_comp (Spec.map (CommRingCat.ofHom (algebraMap R C))) ybar _ hD _).symm.trans
      (res_pullU_res' _ hle h₂ _).symm
  have e1 : res hW (pullU y _ ((D.pull (genericι f)).g j (fun _ => j₀))) =
      res h₂ (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C))) _ ((chartGen D ybar j₀ hj₀).s j)) :=
    sA.trans (sB.trans (sC.trans sD))
  have e2 : res hW (pullU y _ (res inf_le_right (sig.s (fun _ => j₀)))) =
      res (le_top.trans htop) (pullU y _ (sig.s (fun _ => j₀))) := res_pullU_res' _ _ _ _
  have e0 : res hW (pullU y _ (res inf_le_left (sig.s j))) = res h₁ (pullU y _ (sig.s j)) :=
    res_pullU_res' _ _ _ _
  rw [e0, e1, e2] at a
  rw [a, mul_comm]

end Coord

section Val

theorem res_top_val {X Y : Scheme.{0}} (g : Y ⟶ X) (k : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(Y, g ⁻¹ᵁ ⊤)ˣ) :
    ((res k u : Γ(Y, ⊤)ˣ) : Γ(Y, ⊤)) = (u : Γ(Y, g ⁻¹ᵁ ⊤)) := by
  exact congrArg Units.val (res_self' (U := (⊤ : Y.Opens)) k u)

theorem eval_pull_spec {R C : Type} [CommRing R] [Field C] [Algebra R C]
    (k : ⊤ ≤ Spec.map (CommRingCat.ofHom (algebraMap R C)) ⁻¹ᵁ ⊤) (a : Γ(Spec (.of R), ⊤)ˣ) :
    (Scheme.ΓSpecIso (.of C)).hom.hom
      ((res k (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C))) ⊤ a) : Γ(Spec (.of C), ⊤)ˣ) :
        Γ(Spec (.of C), ⊤)) = algebraMap R C ((Scheme.ΓSpecIso (.of R)).hom.hom a.val) := by
  have n := congrArg (fun φ => φ.hom a.val)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R C)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  exact (congrArg _ (res_top_val _ k _)).trans n

theorem val_pull_unit {R C Γ₀ : Type} [CommRing R] [Field C] [Algebra R C]
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation C Γ₀} (hv : v.Integers R)
    {U : (Spec (.of R)).Opens} (hU : ⊤ ≤ U)
    (h : ⊤ ≤ Spec.map (CommRingCat.ofHom (algebraMap R C)) ⁻¹ᵁ U) (x : Γ(Spec (.of R), U)ˣ) :
    v ((Scheme.ΓSpecIso (.of C)).hom.hom
      (res h (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C))) U x) : Γ(Spec (.of C), ⊤))) = 1 := by
  have e : res h (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C))) U x) =
      res (le_top : ⊤ ≤ Spec.map (CommRingCat.ofHom (algebraMap R C)) ⁻¹ᵁ ⊤)
        (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C))) ⊤ (res hU x)) :=
    (res_pullU_res' _ hU le_top x).symm
  exact (congrArg (fun w : Γ(Spec (.of C), ⊤)ˣ => v ((Scheme.ΓSpecIso (.of C)).hom.hom (w : Γ(Spec (.of C), ⊤)))) e).trans
    ((congrArg v (eval_pull_spec (R := R) (C := C) le_top (res hU x))).trans
      (hv.one_of_isUnit ((res hU x).isUnit.map _)))

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Z : Scheme.{0}} {f : Z ⟶ Spec (.of O)}

theorem eval_constUnit {R C : Type} [CommRing R] [Field C] [Algebra R C] (ϖ : O) (hϖ : Irreducible ϖ)
    (φ : O →+* R) (ybar : Spec (.of R) ⟶ Z) (hf : ybar ≫ f = Spec.map (CommRingCat.ofHom φ))
    (y : Spec (.of C) ⟶ genericFibre f)
    (hy : y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar)
    (h : ⊤ ≤ y ⁻¹ᵁ ⊤) :
    (Scheme.ΓSpecIso (.of C)).hom.hom
      (res h (pullU y ⊤ (constUnit (genericStr f) (unifUnit ϖ hϖ))) : Γ(Spec (.of C), ⊤)) =
      algebraMap R C (φ ϖ) := by
  have hm : y ≫ genericStr f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))) =
      Spec.map (CommRingCat.ofHom ((algebraMap R C).comp φ)) := by
    have hc : genericStr f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))) =
        genericι f ≫ f := pullback.condition.symm
    rw [hc, ← Category.assoc, hy, Category.assoc, hf, ← Spec.map_comp]
    rfl
  have key := congrArg (fun m => (Scheme.ΓSpecIso (.of C)).hom.hom
    (m.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ))) hm
  have nat1 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ((algebraMap R C).comp φ)))
  have nat2 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O (FractionRing O))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Scheme.Hom.comp_appTop] at key nat1 nat2
  refine (congrArg _ (res_top_val _ h _)).trans ?_
  have hinv : (Scheme.ΓSpecIso (.of O)).hom.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) = ϖ := by
    simp
  rw [hinv] at nat1 nat2
  have h3 : (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))).appTop.hom
      ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) =
      (Scheme.ΓSpecIso (.of (FractionRing O))).inv.hom (algebraMap O (FractionRing O) ϖ) := by
    rw [← nat2]; simp
  rw [h3, nat1] at key
  exact key

end Val

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Z : Scheme.{0}} {f : Z ⟶ Spec (.of O)}

theorem eval_constUnit_id {C : Type} [Field C] (c : Cˣ) :
    (Scheme.ΓSpecIso (.of C)).hom.hom
      ((res (le_top : (⊤ : (Spec (.of C)).Opens) ≤ ⊤) (constUnit (𝟙 (Spec (.of C))) c) :
        Γ(Spec (.of C), ⊤)ˣ) : Γ(Spec (.of C), ⊤)) = c := by
  rw [res_self']
  simp [constUnit]

theorem val_of_isCoord {R C Γ₀ : Type} [CommRing R] [Field C] [Algebra R C]
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation C Γ₀} (hv : v.Integers R)
    (ϖ : O) (hϖ : Irreducible ϖ) (D : LB Z) (sig : (D.pull (genericι f)).Gen)
    (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen) (hpow : PowEq f ϖ hϖ D sig M n gen)
    (φ : O →+* R) (ybar : Spec (.of R) ⟶ Z) (hf : ybar ≫ f = Spec.map (CommRingCat.ofHom φ))
    (y : Spec (.of C) ⟶ genericFibre f)
    (hy : y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar)
    (j₀ : D.ι) (hj₀ : ybar ⁻¹ᵁ D.U j₀ = ⊤) (e : (D.pull ybar).Gen) (c : Cˣ)
    (hc : IsCoord f D sig ybar y e c) :
    v (c : C) ^ M = v (algebraMap R C (φ ϖ)) ^ n := by
  have htopY := top_le_generic D ybar y hy j₀ hj₀
  have htopS := top_le_special (C := C) D ybar j₀ hj₀
  have h1 := hc (fun _ => j₀) ⊤ htopY htopS
  let Φ := (res htopY).comp (pullU y ((D.pull (genericι f)).U (fun _ => j₀)))
  have h2 := (map_pow Φ _ M).symm.trans ((congrArg Φ (hpow (fun _ => j₀))).trans
    ((map_mul Φ _ _).trans (congrArg (· * _) (map_zpow Φ _ n))))
  rw [show Φ (sig.s (fun _ => j₀)) = _ from h1] at h2
  let w : Γ(Spec (.of C), ⊤)ˣ →* Γ₀ˣ :=
    Units.map (v.toMonoidWithZeroHom.toMonoidHom.comp (Scheme.ΓSpecIso (.of C)).hom.hom.toMonoidHom)
  have h3 := congrArg w h2
  rw [map_mul, map_pow, map_mul, map_zpow] at h3
  have hw1 : w (res htopS (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C))) _
      (e.s (fun _ => j₀)))) = 1 :=
    Units.ext (val_pull_unit hv (wchart_pull_top D ybar j₀ hj₀) htopS (e.s (fun _ => j₀)))
  have hD' : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar) ⁻¹ᵁ D.U j₀ := fun p _ =>
    show (Spec.map (CommRingCat.ofHom (algebraMap R C))).base p ∈ ybar ⁻¹ᵁ D.U j₀ by rw [hj₀]; trivial
  have hw2 : w (Φ (res (LB.wchart_le D (fun _ : PUnit => genericι f) (fun _ => j₀) PUnit.unit)
      (pullU (genericι f) (D.U j₀) (gen.s j₀)))) = 1 := by
    have q1 : Φ (res (LB.wchart_le D (fun _ : PUnit => genericι f) (fun _ => j₀) PUnit.unit)
        (pullU (genericι f) (D.U j₀) (gen.s j₀))) =
        res hD' (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar) (D.U j₀) (gen.s j₀)) :=
      (res_pullU_res' _ _ _ _).trans ((res_pullU_comp _ _ _ _ _).trans (res_pullU_congr hy _ _ hD' _))
    rw [q1]
    exact Units.ext (val_pull_unit hv hj₀.ge hD' (pullU ybar (D.U j₀) (gen.s j₀)))
  have hw3 : (w (Φ (res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ)))) : Γ₀) =
      v (algebraMap R C (φ ϖ)) := by
    have q1 : Φ (res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ))) =
        res (le_top : ⊤ ≤ y ⁻¹ᵁ ⊤) (pullU y ⊤ (constUnit (genericStr f) (unifUnit ϖ hϖ))) :=
      res_pullU_res' _ _ _ _
    rw [q1]
    exact congrArg v (eval_constUnit ϖ hϖ φ ybar hf y hy le_top)
  have hw4 : (w (res le_top (constUnit (𝟙 (Spec (.of C))) c)) : Γ₀) = v (c : C) :=
    congrArg v (eval_constUnit_id c)
  rw [hw1, hw2, mul_one, mul_one] at h3
  have h4 := congrArg Units.val h3
  rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, hw4] at h4
  exact h4.trans (congrArg (· ^ n) hw3)

end Main

theorem valConst_of_powEq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : Irreducible ϖ) (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (D : LB Z), D.IsLB →
    ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
    ∀ (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen), 1 ≤ M → gen.IsGen → PowEq f ϖ hϖ D sig M n gen →
    ValConst f ϖ D sig M n := by
  intro O _ _ _ ϖ hϖ Z f D hD sig hsig M n gen _ _ hpow
  intro R C Γ₀ _ _ _ _ v hv φ _ _ ybar hf y hy
  haveI := isLocalRing_of_integers hv
  obtain ⟨j₀, hj₀⟩ := exists_chart_top D hD ybar
  exact ⟨⟨chartGen D ybar j₀ hj₀, _, chartGen_isGen D hD ybar j₀ hj₀,
    isCoord_chartGen D sig hsig ybar y hy j₀ hj₀⟩,
    fun e c _ hc => val_of_isCoord hv ϖ hϖ D sig M n gen hpow φ ybar hf y hy j₀ hj₀ e c hc⟩

end
end GlobalTheory.ValConstOfPowEq
