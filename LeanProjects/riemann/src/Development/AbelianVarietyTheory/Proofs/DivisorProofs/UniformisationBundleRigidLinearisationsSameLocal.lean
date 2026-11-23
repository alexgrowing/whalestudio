import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrPowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RigLinUnique

theorem eq_pull_section {X S S' : Scheme.{0}} (p : X ⟶ S) (e : S ⟶ X) (he : e ≫ p = 𝟙 S) (j : S' ⟶ S)
    (hi : Function.Injective (pullback.fst p j).appTop.hom)
    (hs : Function.Surjective (pullback.snd p j).appTop.hom) (u : Γ(X, ⊤)) :
    u = p.appTop.hom (e.appTop.hom u) := by
  have cmp : ∀ {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (x : Γ(C, ⊤)),
      a.appTop.hom (b.appTop.hom x) = (a ≫ b).appTop.hom x := fun a b x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  obtain ⟨c, hc⟩ := hs ((pullback.fst p j).appTop.hom u)
  let e' : S' ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 S') (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h1 : e' ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have h2 : e' ≫ pullback.snd p j = 𝟙 S' := pullback.lift_snd _ _ _
  have hc' : c = j.appTop.hom (e.appTop.hom u) := by
    have := congrArg e'.appTop.hom hc
    rw [cmp, cmp, h1, h2, ← cmp, Scheme.Hom.id_appTop] at this
    exact this
  apply hi
  rw [cmp, pullback.condition, ← cmp, ← hc', hc]

theorem exists_ratio {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (w₁ w₂ : LB.Iso L' (L.pull F)) (h₁ : PGen w₁) (h₂ : PGen w₂) :
    ∃ u : Γ(X', ⊤)ˣ, ∀ (Y : Scheme.{0}) (g : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), F (g y) ∈ L.U j → g y ∈ L'.U k →
      gw w₂ g y j k = gm g y ⊤ u * gw w₁ g y j k := by
  have key : ∀ (Y : Scheme.{0}) (g : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι),
      gm g y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w₂.s (fun _ => j, k) * (w₁.s (fun _ => j, k))⁻¹) =
        gw w₂ g y j k * (gw w₁ g y j k)⁻¹ := fun Y g y j k =>
    (map_mul _ _ _).trans (congrArg (gw w₂ g y j k * ·) (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit (X := X') (J := L.ι × L'.ι) ⊤ (fun p => (L.pull F).U (fun _ => p.1) ⊓ L'.U p.2)
    (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F x)
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, k), mem_pull.2 hj, hk⟩)
    (fun p => w₂.s (fun _ => p.1, p.2) * (w₁.s (fun _ => p.1, p.2))⁻¹) (fun p q x hx => by
      have a := h₁ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      have b := h₂ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      refine (key _ _ x p.1 p.2).trans (Eq.trans ?_ (key _ _ x q.1 q.2).symm)
      rw [a, b, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv])
  refine ⟨u, fun Y g y j k hj hk => ?_⟩
  have hm : g y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have : gm g y ⊤ u = gw w₂ g y j k * (gw w₁ g y j k)⁻¹ := (gm_res g y le_top hm u).symm.trans
    ((congrArg (gm g y ((L.pull F).U (fun _ => j) ⊓ L'.U k)) (hu (j, k))).trans (key Y g y j k))
  rw [this]
  exact (inv_mul_cancel_right _ _).symm

theorem gw_eq_of_rigidified : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (s : Sp R' ⟶ Sp R') (f₁ f₂ : G'.left ⟶ G'.left), f₁ = f₂ → ∀ (he₁ : eSec G' ≫ f₁ = s ≫ eSec G') (he₂ : eSec G' ≫ f₂ = s ≫ eSec G') (w₁ : LB.Iso U'.LG.L (U'.LG.L.pull f₁)) (w₂ : LB.Iso U'.LG.L (U'.LG.L.pull f₂)), w₁.IsGen → w₂.IsGen → LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₁ s he₁ U'.LG.L U'.LG.rig) → LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₂ s he₂ U'.LG.L U'.LG.rig) → ∀ (z : G'.left) (j k : U'.LG.L.ι), z ∈ U'.LG.L.U k → f₁ z ∈ U'.LG.L.U j → gw w₁ (𝟙 G'.left) z j k = gw w₂ (𝟙 G'.left) z j k := by
  intro R' _ _ _ D' A' G' _ _ hS U' s f₁ f₂ hf he₁ he₂ w₁ w₂ g₁ g₂ m₁ m₂ z j k hk hj
  subst hf
  have hL := U'.LG.isLB
  obtain ⟨u, hu⟩ := exists_ratio hL hL w₁ w₂ ((isGen_iff w₁).1 g₁) ((isGen_iff w₂).1 g₂)
  have p₁ := (maps_iff w₁ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig s _ (rigPull_le f₁ s he₁ U'.LG.L)
    (fun _ => rfl)).1 m₁
  have p₂ := (maps_iff w₂ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig s _ (rigPull_le f₁ s he₂ U'.LG.L)
    (fun _ => rfl)).1 m₂
  have he1 : pullU (eSec G') ⊤ u = 1 := by
    apply unit_ext
    intro x _
    obtain ⟨a, ha⟩ := exists_chart hL (f₁ (eSec G' x))
    obtain ⟨b, hb⟩ := exists_chart hL (eSec G' x)
    have q₁ := p₁ _ (𝟙 _) x (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    have q₂ := p₂ _ (𝟙 _) x (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    have q := mul_right_cancel (q₂.symm.trans q₁)
    rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, hu _ (𝟙 _ ≫ eSec G') x a b ha hb] at q
    rw [map_one]
    exact (gm_pull (𝟙 _) (eSec G') x ⊤ trivial u).trans (mul_eq_right.1 q)
  have := U'.smooth
  have : Flat G'.hom := inferInstance
  have : IsDominant (jK R') := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (algebraMap R' (FractionRing R')))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R' (FractionRing R'))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R')
  have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R')) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G'.hom (jK R')).flip
  have hb := GlobalFunctionsDvrPowers.bijective_of_iso U'.gen (GlobalTheory.SemiRigid.globalFns _ A'.A A'.isAb)
  have hv := eq_pull_section G'.hom (eSec G') (Over.w η[G']) (jK R')
    ((pullback.fst G'.hom (jK R')).app_injective ⊤) hb.2 u.val
  have he2 : (eSec G').appTop.hom u.val = 1 := congrArg Units.val he1
  have hu1 : u = 1 := Units.ext (hv.trans ((congrArg G'.hom.appTop.hom he2).trans (map_one _)))
  rw [hu _ (𝟙 _) z j k hj hk, hu1, map_one, _root_.one_mul]

end GlobalTheory.Mum.RigLinUnique
