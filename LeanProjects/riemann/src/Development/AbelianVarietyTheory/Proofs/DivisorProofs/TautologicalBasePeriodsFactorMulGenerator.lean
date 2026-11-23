import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautTau

section Core

variable {X X' P P' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K : Type} [Fintype K]

theorem exists_gen_across (hL : L.IsLB) (hL' : L'.IsLB) (ψ : K → (P ⟶ X)) (ψ' : K → (P' ⟶ X')) (ε : K → ℤ)
    (β₂ : P' ⟶ P) (w : LB.Iso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull β₂)) (hw : w.IsGen) (p : Y ⟶ P')
    (b : LB.Gen (LB.LinComb L (fun k => p ≫ β₂ ≫ ψ k) (fun k => -ε k))) (hb : b.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L' (fun k => p ≫ ψ' k) (fun k => -ε k)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        val u r z J' = gm (r ≫ p) z _ (w.s (fun _ k => J ((r ≫ p) ≫ β₂ ≫ ψ k), fun k => J' ((r ≫ p) ≫ ψ' k))) *
          val b r z J := by
  have hC : (LB.LinComb L ψ ε).IsLB := DVR.linComb_isLB _ hL _ _
  have hC' : (LB.LinComb L' ψ' ε).IsLB := DVR.linComb_isLB _ hL' _ _
  have pw := (isGen_iff w).1 hw

  have wchg : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j j₂ : K → L.ι) (q q₂ : K → L'.ι),
      (∀ k, (f ≫ p ≫ β₂ ≫ ψ k) z ∈ L.U (j k)) → (∀ k, (f ≫ p ≫ β₂ ≫ ψ k) z ∈ L.U (j₂ k)) →
      (∀ k, (f ≫ p ≫ ψ' k) z ∈ L'.U (q k)) → (∀ k, (f ≫ p ≫ ψ' k) z ∈ L'.U (q₂ k)) →
      gw w (f ≫ p) z j q = (∏ k, gm (f ≫ p ≫ β₂ ≫ ψ k) z _ (L.g (j k) (j₂ k)) ^ ε k) *
        (∏ k, gm (f ≫ p ≫ ψ' k) z _ (L'.g (q k) (q₂ k)) ^ ε k)⁻¹ * gw w (f ≫ p) z j₂ q₂ := by
    intro Z f z j j₂ q q₂ hj hj₂ hq hq₂
    have m₁ : β₂ ((f ≫ p) z) ∈ (LB.LinComb L ψ ε).U j := Set.mem_iInter.2 fun k => hj k
    have m₂ : β₂ ((f ≫ p) z) ∈ (LB.LinComb L ψ ε).U j₂ := Set.mem_iInter.2 fun k => hj₂ k
    have m₃ : (f ≫ p) z ∈ (LB.LinComb L' ψ' ε).U q := Set.mem_iInter.2 fun k => hq k
    have m₄ : (f ≫ p) z ∈ (LB.LinComb L' ψ' ε).U q₂ := Set.mem_iInter.2 fun k => hq₂ k
    rw [pw Z (f ≫ p) z j j₂ q q₂ m₁ m₂ m₃ m₄]
    erw [gm_linComb L ψ ε ((f ≫ p) ≫ β₂) z j j₂ m₁ m₂, gm_linComb L' ψ' ε (f ≫ p) z q q₂ m₃ m₄]
    simp only [Category.assoc]
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' (fun k => p ≫ ψ' k) q)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : K → L.ι),
        f z ∈ LB.wchart L' (fun k => p ≫ ψ' k) q → f z ∈ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j →
        gm f z _ s = gw w (f ≫ p) z j q * gm f z _ (b.s j) := by
    intro q
    let W : (K → L.ι) → Y.Opens := fun j =>
      LB.wchart L' (fun k => p ≫ ψ' k) q ⊓ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j
    have l₀ : ∀ j, W j ≤ LB.wchart L' (fun k => p ≫ ψ' k) q := fun j => inf_le_left
    have l₁ : ∀ j, W j ≤ p ⁻¹ᵁ (((LB.LinComb L ψ ε).pull β₂).U (fun _ => j) ⊓ (LB.LinComb L' ψ' ε).U q) :=
      fun j x hx => ⟨mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 k),
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.1 k⟩
    have l₂ : ∀ j, W j ≤ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j := fun j => inf_le_right
    obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Y, W j)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : K → L.ι), f z ∈ W j →
        gm f z (W j) (u j) = gw w (f ≫ p) z j q * gm f z _ (b.s j) :=
      ⟨fun j => res (l₁ j) (pullU p _ (w.s (fun _ => j, q))) * res (l₂ j) (b.s j), fun Z f z j hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f z (l₁ j) hz _).trans (gm_pull f p z _ (l₁ j hz) _)) (gm_res f z (l₂ j) hz _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        choose j hj using fun k => exists_chart hL ((p ≫ β₂ ≫ ψ k) x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hx, Set.mem_iInter.2 hj⟩) u (fun j j₂ x hx => by
        rw [hu _ (𝟙 Y) x j hx.1, hu _ (𝟙 Y) x j₂ hx.2]
        have a := wchg Y (𝟙 Y) x j j₂ q q (fun k => Set.mem_iInter.1 hx.1.2 k) (fun k => Set.mem_iInter.1 hx.2.2 k)
          (fun k => Set.mem_iInter.1 hx.1.1 k) (fun k => Set.mem_iInter.1 hx.1.1 k)
        have c := gen_trans hb (𝟙 Y) x hx.1.2 hx.2.2
        have one : (∏ k, gm (𝟙 Y ≫ p ≫ ψ' k) x _ (L'.g (q k) (q k)) ^ ε k) = 1 :=
          Finset.prod_eq_one fun k _ => by
            rw [gm_self hL' (𝟙 Y ≫ p ≫ ψ' k) x (show (𝟙 Y ≫ p ≫ ψ' k) x ∈ L'.U (q k) from Set.mem_iInter.1 hx.1.1 k),
              one_zpow]
        have hA : (∏ k, gm (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x _ (L.g (j k) (j₂ k)) ^ ε k) *
            trF (L := L) (fun k => p ≫ β₂ ≫ ψ k) (fun k => -ε k) (𝟙 Y) x j j₂ = 1 := by
          rw [trF, ← Finset.prod_mul_distrib]
          exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, _root_.mul_inv_cancel]
        rw [a, one, inv_one, _root_.mul_one]
        erw [c]
        rw [_root_.mul_mul_mul_comm, hA, _root_.one_mul]
        rfl)
    exact ⟨s, fun Z f z j hq hj => (gm_res f z (l₀ j) ⟨hq, hj⟩ s).symm.trans
      ((congrArg (gm f z (W j)) (hs j)).trans (hu Z f z j ⟨hq, hj⟩))⟩
  choose s hs using glue
  refine ⟨⟨s⟩, fun q q₂ => unit_ext fun x hx => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  swap
  · refine (hs (fun k => J' (r ≫ p ≫ ψ' k)) Z r z (fun k => J (r ≫ p ≫ β₂ ≫ ψ k)) (hJ'.mem (fun k => p ≫ ψ' k) r)
      (hJ.mem (fun k => p ≫ β₂ ≫ ψ k) r)).trans ?_
    congr 1
  choose j hj using fun k => exists_chart hL ((p ≫ β₂ ≫ ψ k) x)
  have mj : (𝟙 Y) x ∈ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j := Set.mem_iInter.2 hj
  have e₁ := hs q Y (𝟙 Y) x j hx.1 mj
  have e₂ := hs q₂ Y (𝟙 Y) x j hx.2 mj
  have c := wchg Y (𝟙 Y) x j j q q₂ hj hj (fun k => Set.mem_iInter.1 hx.1 k) (fun k => Set.mem_iInter.1 hx.2 k)
  have one : (∏ k, gm (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x _ (L.g (j k) (j k)) ^ ε k) = 1 :=
    Finset.prod_eq_one fun k _ => by
      rw [gm_self hL (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x (show (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x ∈ L.U (j k) from hj k), one_zpow]
  rw [one, _root_.one_mul] at c
  have g := gm_linComb L' (fun k => p ≫ ψ' k) (fun k => -ε k) (𝟙 Y) x q q₂ hx.1 hx.2
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx]
  erw [g, e₁, e₂, c]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  rw [_root_.mul_assoc]

end Core

section Main

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]

theorem toUnit_left' {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem ag_four {G : Type} [CommGroup G] (a b c d : G) :
    a⁻¹ * b * c * d⁻¹ = (a * b⁻¹ * c⁻¹ * d)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tauCoord_of_dataFrom (T : TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V)
    (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ))
    (hD : DataFrom T iw s ε n Q e) (a b : Q.X) :
    ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      Q.TauCoord a b k := by
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, hτ⟩ := hD
  obtain ⟨k, hk, hval⟩ := hτ a b
  refine ⟨k, hk, ?_⟩
  let h : (𝟙_ (Over (Sp V))).left ⟶ (𝟙_ (Over (Sp W))).left := spMap iw
  let p : (𝟙_ (Over (Sp V))).left ⟶ (G2 Q.B).left := (lift (Q.c a) (Q.c b)).left
  have c0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have t0 : T.c₀ 0 = 1 := mul_eq_left.1 ((T.c₀_add 0 0).symm.trans (by rw [add_zero]))
  have hF1 : p ≫ β₂ = (lift (pushPt hpb.1.w (Q.c a)) (pushPt hpb.1.w (Q.c b))).left := by
    apply pullback.hom_ext
    · show _ ≫ (fst T.B T.B).left = _ ≫ (fst T.B T.B).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      rfl
    · show _ ≫ (snd T.B T.B).left = _ ≫ (snd T.B T.B).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      rfl
  have px : (pushPt hpb.1.w (Q.c a)).left = h ≫ (T.c₀ ((n : ℤ) • e a)).left := hc a
  have py : (pushPt hpb.1.w (Q.c b)).left = h ≫ (T.c₀ ((n : ℤ) • e b)).left := hc b
  have pxy : (pushPt hpb.1.w (Q.c a) * pushPt hpb.1.w (Q.c b)).left =
      h ≫ (T.c₀ ((n : ℤ) • e a) * T.c₀ ((n : ℤ) • e b)).left := by
    have m := congrArg (fun q => q.left) (map_mul (pushHom hpb (𝟙_ (Over (Sp V)))) (Q.c a) (Q.c b))
    refine m.symm.trans ?_
    show (Q.c a * Q.c b).left ≫ β = _
    rw [← Q.c_add, hc, ← T.c₀_add, ← smul_add, ← map_add]
  have p1 : (1 : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ spMap iw) ⟶ T.B).left = h ≫ (1 : 𝟙_ (Over (Sp W)) ⟶ T.B).left := by
    have m := congrArg (fun q => q.left) (map_one (pushHom hpb (𝟙_ (Over (Sp V)))))
    refine m.symm.trans ?_
    show (1 : 𝟙_ (Over (Sp V)) ⟶ Q.B).left ≫ β = _
    have := hc 0
    rw [c0, map_zero, smul_zero, t0] at this
    exact this
  have hFT : FormEq (fun k => h ≫ lamPts (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b)) k) negε
      (fun I => p ≫ β₂ ≫ GlobalTheory.PrimCocycle.lamφ T.B I) (fun I => -GlobalTheory.PrimCocycle.lamε I) := by
    intro U _ H
    have r₁ : ∀ I, p ≫ β₂ ≫ GlobalTheory.PrimCocycle.lamφ T.B I =
        (lift (pushPt hpb.1.w (Q.c a)) (pushPt hpb.1.w (Q.c b))).left ≫ GlobalTheory.PrimCocycle.lamφ T.B I := fun I => by
      rw [← Category.assoc, hF1]
    simp only [r₁, zpow_neg, Finset.prod_inv_distrib]
    rw [GlobalTheory.PrimCocycle.prod_lam, pxy, px, py, p1, Fin.prod_univ_four]
    simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    exact ag_four _ _ _ _
  have hFQ : FormEq (fun I => p ≫ GlobalTheory.PrimCocycle.lamφ Q.B I) (fun I => -GlobalTheory.PrimCocycle.lamε I)
      (lamPts (Q.c a) (Q.c b)) negε := by
    intro U _ H
    simp only [zpow_neg, Finset.prod_inv_distrib]
    rw [GlobalTheory.PrimCocycle.prod_lam, Fin.prod_univ_four]
    simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    exact (ag_four _ _ _ _).symm
  obtain ⟨b₁, hb₁, hv₁⟩ := exists_gen T.M.isLB hFT
    (LB.pullGen T.M.L (lamPts (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b))) negε (T.τ₀ _ _) h)
    (DVR.pullGen_isGen _ _ _ _ (T.τ₀_gen _ _) h)
  obtain ⟨u₁, hu₁, hvu⟩ := exists_gen_across T.M.isLB Q.M.isLB (GlobalTheory.PrimCocycle.lamφ T.B)
    (GlobalTheory.PrimCocycle.lamφ Q.B) GlobalTheory.PrimCocycle.lamε β₂ w hw p b₁ hb₁
  obtain ⟨u, hu, hvq⟩ := exists_gen Q.M.isLB hFQ u₁ hu₁
  refine ⟨u, hu, fun z J' hJ' => ?_⟩
  choose J hJ using fun χ : (TK V).left ⟶ T.B.left => exists_chart T.M.isLB (χ z)
  have hJg : Good T.M.L z J := hJ
  rw [hval z J J' hJg hJ']
  congr 1
  rw [hvq _ _ z J' hJ', hvu _ _ z J J' hJg hJ', hv₁ _ _ z J hJg, val_pull hJg]
  have hr : (toUnit (TK V)).left ≫ p = (lift (toUnit (TK V) ≫ Q.c a) (toUnit (TK V) ≫ Q.c b)).left := by
    rw [← Over.comp_left, comp_lift]
  have hh : (toUnit (TK V)).left ≫ h = (TK V).hom ≫ spMap iw := by
    rw [toUnit_left']
  rw [hh, ← hr]
  rfl

end Main

end GlobalTheory.TautTau
