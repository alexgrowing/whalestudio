import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolTorsionAny

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

theorem triv_step (hA : IsAbelianScheme G) (hL : L.IsLB) {T : Over S} (a c : T ⟶ G) (n : ℕ) :
    GlobalTheory.AbLaw.Triv (LB.LinComb L (K := Fin 6)
      ![(a ^ n * c).left, c.left, (a ^ n).left, (1 : T ⟶ G).left, (a * c).left, a.left]
      ![1, (n : ℤ) - 1, -1, 1 - (n : ℤ), -(n : ℤ), (n : ℤ)]) := by
  induction n with
  | zero =>
    have h := GlobalTheory.CubeTop.cubeTheorem S G hA L hL T 1 1 c
    simp only [_root_.one_mul] at h
    obtain ⟨t, ht⟩ := h
    obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![((a ^ 0) * c).left, c.left, (a ^ 0).left, (1 : T ⟶ G).left,
      (a * c).left, a.left]) (ε' := ![1, ((0 : ℕ) : ℤ) - 1, -1, 1 - ((0 : ℕ) : ℤ), -((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)])
      (fun U _ h => by
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
          pow_zero, _root_.one_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        push_cast
        module) t ht
    exact ⟨u, hu⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    have h := GlobalTheory.CubeTop.cubeTheorem S G hA L hL T a (a ^ n) c
    rw [← pow_succ'] at h
    obtain ⟨q, hq⟩ := h
    obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![(a ^ (n + 1) * c).left, c.left, (a ^ (n + 1)).left,
      (1 : T ⟶ G).left, (a * c).left, a.left])
      (ε' := ![1, ((n + 1 : ℕ) : ℤ) - 1, -1, 1 - ((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)])
      (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        push_cast
        module) (LB.mulGen L _ _ _ _ t q) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht hq)
    exact ⟨u, hu⟩

theorem exists_theta_local (hA : IsAbelianScheme G) (hL : L.IsLB) {k : ℕ} {T : Over S} (x : T ⟶ G) (hx : x ^ k = 1)
    (p : T.left) : ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp G L (k : ℤ) (Out.overRes V), θ.pt = Out.overResι V ≫ x := by
  obtain ⟨V, hV, w, hw⟩ := exists_local_gen hL (Y := T.left) ![(1 : T ⟶ G).left, x.left] ![(k : ℤ), -(k : ℤ)] p
  refine ⟨V, hV, ?_⟩
  let xV : Out.overRes V ⟶ G := Out.overResι V ≫ x
  let a : Out.overRes V ⊗ G ⟶ G := fst (Out.overRes V) G ≫ xV
  let c : Out.overRes V ⊗ G ⟶ G := snd (Out.overRes V) G
  have ha : a ^ k = 1 := by
    show (fst (Out.overRes V) G ≫ Out.overResι V ≫ x) ^ k = 1
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, MonObj.comp_one]
  have hP := triv_step hA hL a c k
  rw [ha, _root_.one_mul] at hP
  obtain ⟨t, ht⟩ := hP
  have e₁ : (fst (Out.overRes V) G).left ≫ V.ι ≫ (1 : T ⟶ G).left = (1 : Out.overRes V ⊗ G ⟶ G).left := by
    have : (fst (Out.overRes V) G ≫ Out.overResι V ≫ (1 : T ⟶ G)) = 1 := by
      rw [MonObj.comp_one, MonObj.comp_one]
    rw [← this]
    rfl
  have e₂ : (fst (Out.overRes V) G).left ≫ V.ι ≫ x.left = a.left := rfl
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![(snd (Out.overRes V) G).left, (Out.translPt G xV).left])
    (ε' := ![(k : ℤ), -(k : ℤ)])
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, e₁, e₂]
      rw [translPt_eq]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ w (fst (Out.overRes V) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ hw _))
  exact ⟨⟨xV, u, hu⟩, rfl⟩

theorem exists_weilIs_pow_eq_one (hA : IsAbelianScheme G) (hL : L.IsLB) {k : ℕ} {T : Over S} {x y : T ⟶ G}
    (hx : x ^ k = 1) (hy : y ^ k = 1) : ∃ e : Γ(T.left, ⊤)ˣ, e ^ k = 1 ∧ Out.WeilIs G L (k : ℤ) x y e := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  obtain ⟨e, he⟩ := GlobalTheory.CommutatorPairing.exists_weilIs (k := (k : ℤ)) hG hA hL
    (fun p => exists_theta_local hA hL x hx p) (fun p => exists_theta_local hA hL y hy p)
  have pw : ∀ m : ℕ, Out.WeilIs G L (k : ℤ) (x ^ (m + 1)) y (e ^ (m + 1)) := fun m => by
    induction m with
    | zero => simpa only [zero_add, pow_one] using he
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ e (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih he
  have hk := pw k
  rw [pow_succ x k, hx, _root_.one_mul] at hk
  have := GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL hk he
  rw [pow_succ, mul_eq_right] at this
  exact ⟨e, this, he⟩

end GlobalTheory.HolTorsionAny

namespace GlobalTheory

open HolTorsion HolTorsionAny in

theorem torsion_eq_and_weilIs_of_isHolTo_anyLB : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), LocallyOfFiniteType s → IsAbelianScheme G → L.IsLB → ∀ (m k : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (c : ℂˣ) (b₀ : Fin m → ℂ), 0 < k → IsOpen B → IsPreconnected B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ = x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs G L k (x b₀) (x' b₀) (unitOn c) → ∀ b ∈ B, Out.WeilIs G L k (x b) (x' b) (unitOn c))) := by
  intro X s G _ _ L _ hA hLB m k B y x x' c b₀ hk _ hB hb₀ _ hx hx' htor
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds

  have hku : IsUnit (k : Γ(X, ⊤)) := by
    have h₁ : IsUnit ((k : ℂ)) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk.ne')
    have h₂ := (h₁.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).map s.appTop.hom
    simpa only [map_natCast] using h₂
  haveI : FormallyUnramified (Out.mulA G k).left := GlobalTheory.formallyUnramified_mulA X G k hku
  haveI : Smooth G.hom := hA.smooth
  haveI : IsProper G.hom := hA.proper
  haveI : LocallyOfFiniteType ((Out.mulA G k).left ≫ G.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType (Out.mulA G k).left := locallyOfFiniteType_of_comp _ G.hom
  haveI : IsSeparated ((Out.mulA G k).left ≫ G.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated (Out.mulA G k).left := IsSeparated.of_comp _ G.hom
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ k = 1 ↔ u.left ≫ (Out.mulA G k).left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ (Out.mulA G k).left = (u ^ k).left := by
      rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst (Out.mulA G k).left o
  let q := pullback.snd (Out.mulA G k).left o
  have H : IsPullback p q (Out.mulA G k).left o := IsPullback.of_hasPullback _ _
  haveI : FormallyUnramified q := MorphismProperty.of_isPullback (P := @FormallyUnramified) H ‹_›
  haveI : LocallyOfFiniteType q := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) H ‹_›
  haveI : IsSeparated q := MorphismProperty.of_isPullback (P := @IsSeparated) H ‹_›
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w (Out.mulA G k), ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  refine ⟨fun h₀ b hb => ?_, fun h₀ b hb => ?_⟩
  · have e₀ : a b₀ = a' b₀ := H.hom_ext (by rw [(hab b₀ hb₀).1, (hab' b₀ hb₀).1, h₀])
      (by rw [(hab b₀ hb₀).2, (hab' b₀ hb₀).2])
    have e := comp_eq_of_unramified q hz hB hb₀ hb (by rw [(hzb b₀ hb₀).1, (hzb b₀ hb₀).2, e₀])
    rw [(hzb b hb).1, (hzb b hb).2] at e
    apply Over.OverMorphism.ext
    rw [← (hab b hb).1, ← (hab' b hb).1, e]
  · let T : Over X := Over.mk (pullback.fst q q ≫ q)
    let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
      show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq])
    let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
      show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq, pullback.condition])
    have hu : u ^ k = 1 := (hkill T u).2 (by
      show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, Category.assoc])
    have hv : v ^ k = 1 := (hkill T v).2 (by
      show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, pullback.condition, Category.assoc])
    obtain ⟨e, hek', he⟩ := exists_weilIs_pow_eq_one hA hLB hu hv
    have hek : e.val ^ k = 1 := congrArg Units.val hek'
    have hpull : ∀ w ∈ B, Out.WeilIs G L k (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
      intro w hw
      let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
        show z w ≫ pullback.fst q q ≫ q = y w
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
      have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
        show z w ≫ pullback.fst q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
      have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
        show z w ≫ pullback.snd q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
      have := GlobalTheory.CommPairing.weilIs_pull hG hA hLB h he
      rw [e₁, e₂] at this
      exact this
    have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn c :=
      GlobalTheory.CommutatorPairing.weilIs_unique hG hA hLB (hpull b₀ hb₀) h₀
    have e₁ : Units.map (z b).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
      Units.ext ((val_map_appTop (z b) e.val).trans
        ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hk hek hb₀ hb)).trans (val_map_appTop (z b₀) e.val).symm))
    have := hpull b hb
    rw [e₁, e₀] at this
    exact this

end GlobalTheory
