import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowChart.Compare

open TopologicalSpace

section Comp

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem gm_self_of_pgen (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w) {Y : Scheme.{0}} (f : Y ⟶ X')
    (y : Y) {j : L.ι} {i : L'.ι} (hj : F (f y) ∈ L.U j) (hi : f y ∈ L'.U i) :
    gm (f ≫ F) y (L.U j ⊓ L.U j) (L.g j j) = 1 := by
  have c := hw Y f y j j i i hj hj hi hi
  rw [gm_self hL' f y hi, inv_one, _root_.mul_one] at c
  exact mul_eq_right.1 c.symm

theorem indep_comp' (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w) (hw' : PGen w')
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j : L.ι) (i i' : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hi : F' (f y) ∈ L'.U i) (hi' : F' (f y) ∈ L'.U i') (hk : f y ∈ L''.U k) :
    gw w (f ≫ F') y j i * gw w' f y i k = gw w (f ≫ F') y j i' * gw w' f y i' k := by
  have a := hw Y (f ≫ F') y j j i i' hj hj hi hi'
  have b := hw' Y f y i i' k k hi hi' hk hk
  rw [gm_self_of_pgen hL' w hw (f ≫ F') y hj hi] at a
  rw [gm_self hL'' f y hk] at b
  rw [a, b]
  generalize gm (f ≫ F') y _ (L'.g i i') = B
  generalize gw w (f ≫ F') y j i' = C
  generalize gw w' f y i' k = D
  rw [_root_.one_mul, inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]

theorem exists_comp' (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL'' : L''.IsLB) :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have glue : ∀ (j : L.ι) (k : L''.ι), ∃ s : Γ(X'', (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i → f y ∈ L''.U k →
        gm f y _ s = gw w (f ≫ F') y j i * gw w' f y i k := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : L'.ι → X''.Opens, ∀ i x, x ∈ W i ↔ F (F' x) ∈ L.U j ∧ F' x ∈ L'.U i ∧ x ∈ L''.U k :=
      ⟨fun i => F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, W i ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull₂.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.2⟩
    have l₁ : ∀ i, W i ≤ F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) := fun i x hx =>
      ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
    have l₂ : ∀ i, W i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k := fun i x hx =>
      ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.2 ((hW i x).1 hx).2.1, ((hW i x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X'', W i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), f y ∈ W i →
        gm f y (W i) (u i) = gw w (f ≫ F') y j i * gw w' f y i k :=
      ⟨fun i => res (l₁ i) (pullU F' _ (w.s (fun _ => j, i))) * res (l₂ i) (w'.s (fun _ => i, k)), fun Y f y i hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ i) hy _).trans (gm_pull f F' y _ (l₁ i hy) _)) (gm_res f y (l₂ i) hy _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
        exact Opens.mem_iSup.2 ⟨i, (hW i x).2 ⟨mem_pull₂.1 hx.1, hi, hx.2⟩⟩) u (fun i i' x hx => by
        have h₁ := (hW i x).1 hx.1
        have h₂ := (hW i' x).1 hx.2
        exact (hu _ (𝟙 X'') x i hx.1).trans ((indep_comp' w w' hw hw' hL' hL'' (𝟙 X'') x j i i' k h₁.1 h₁.2.1
          h₂.2.1 h₁.2.2).trans (hu _ (𝟙 X'') x i' hx.2).symm))
    refine ⟨s, fun Y f y i hj hi hk => ?_⟩
    have hy := (hW i (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ i) hy s).symm.trans ((congrArg (gm f y (W i)) (hs i)).trans (hu Y f y i hy))
  choose s hs using glue
  exact ⟨⟨fun p => s (p.1 PUnit.unit) p.2⟩, fun Y f y j i k hj hi hk => hs j k Y f y i hj hi hk⟩

end Comp

end GlobalTheory.LowChart.Compare

namespace GlobalTheory.LowChart

theorem exists_siegAt_of_siegPB : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : SFam h n ζ) {S S₀ : Scheme.{0}} (g : S ⟶ S₀) (s' : S ⟶ Sp o) (x : S ⟶ F.X), x ≫ F.s = s' → ∀ (c : SiegPre h n ζ s'), SiegPB c F.univ x → ∀ (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (Q : LB (G2 A₀).left) (β : c.A.left ⟶ A₀.left) (β₂ : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ g β → IsSquare β β₂ → LBIso c.P (Q.pull β₂) → ∀ (r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ c.A)), ∃ (v : S ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = s') (β₁ : (GlobalTheory.LowChart.siegAt F v s' hs).A.left ⟶ A₀.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v s' hs).A).left ⟶ (G2 A₀).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v s' hs).A A₀ g β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v s' hs).P (Q.pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v s' hs a).left ≫ β₁ = (∏ i, d i ^ a i).left ≫ β := by
  intro o _ ζ h n F S S₀ g s' x hx c hc A₀ _ _ Q β β₂ hβ hβ₂ hQ r d
  obtain ⟨φ, φ₂, hφ, hφ₂, hP, -⟩ := hc
  have hp : ∀ i, ((d i).left ≫ φ) ≫ F.univ.A.hom = x := fun i => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (d i)]
    exact Category.id_comp _
  obtain ⟨v, hv, hvc⟩ : ∃ v : S ⟶ (powA F r).left, v ≫ (powA F r).hom = x ∧
      ∀ i, v ≫ (coord F i).left = (d i).left ≫ φ :=
    ⟨lift x (fun i => (d i).left ≫ φ) hp, lift_hom _ _ _, fun i => lift_coord _ _ _ i⟩
  have hs : v ≫ toO F r = s' := by
    rw [toO, ← Category.assoc, hv, hx]
  refine ⟨v, hs, ?_⟩
  have hpb : IsGrpPullback (siegAt F v s' hs).A F.univ.A x (Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A) :=
    (Pdiv.PullbackComparison.isGrpPullback _ _).congr hv rfl
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hpb hφ
  haveI := he
  let C := siegAt F v s' hs
  let θ₂ : (G2 C.A).left ⟶ (G2 c.A).left := (CartesianMonoidalCategory.lift (fst C.A C.A ≫ e.hom) (snd C.A C.A ≫ e.hom)).left
  have hθf : θ₂ ≫ (fst c.A c.A).left = (fst C.A C.A).left ≫ e.hom.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_fst, Over.comp_left]
  have hθs : θ₂ ≫ (snd c.A c.A).left = (snd C.A C.A).left ≫ e.hom.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd, Over.comp_left]
  refine ⟨e.hom.left ≫ β, θ₂ ≫ β₂, ((isGrpPullback_of_iso e).comp hβ).congr (Category.id_comp g) rfl,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hβ₂.1, ← Category.assoc, hθf, Category.assoc]
  · rw [Category.assoc, hβ₂.2, ← Category.assoc, hθs, Category.assoc]
  · have hθ₂ : Pdiv.PullbackComparison.pφ₂ (v ≫ (powA F r).hom) F.univ.A = θ₂ ≫ φ₂ :=
      have e1 : (θ₂ ≫ φ₂) ≫ (fst F.univ.A F.univ.A).left =
          (fst C.A C.A).left ≫ Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A := by
        rw [Category.assoc, hφ₂.1, ← Category.assoc, hθf, Category.assoc, heφ]
      have e2 : (θ₂ ≫ φ₂) ≫ (snd F.univ.A F.univ.A).left =
          (snd C.A C.A).left ≫ Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A := by
        rw [Category.assoc, hφ₂.2, ← Category.assoc, hθs, Category.assoc, heφ]
      Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components (G := F.univ.A) _ _
        ((Pdiv.PullbackComparison.pφ₂_fst _ _).trans e1.symm) ((Pdiv.PullbackComparison.pφ₂_snd _ _).trans e2.symm)
    have w1 : LBIso C.P (c.P.pull θ₂) :=
      LBIso.chartPull (chartPullSame F.univ.P (fun _ : PUnit.{1} => Pdiv.PullbackComparison.pφ₂ (v ≫ (powA F r).hom) F.univ.A)
        (fun _ => φ₂) (fun _ => 1) θ₂ (fun _ => hθ₂)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P θ₂ θ₂ rfl) (LBIso.symm hP)
    obtain ⟨w, hw⟩ := hQ
    obtain ⟨w', hw'⟩ := w1
    have pw := (isGen_iff w).1 hw
    have pw' := (isGen_iff w').1 hw'
    obtain ⟨w'', T⟩ := Compare.exists_comp' c.isLB w w' pw pw' C.isLB
    exact ⟨w'', (isGen_iff w'').2 (T.pgen_comp c.isLB pw pw')⟩
  · have hpt : ∀ i, ptAt F v s' hs i ≫ e.hom = d i := fun i =>
      Over.OverMorphism.ext (hφ.1.hom_ext
        (by rw [Over.comp_left, Category.assoc, heφ, ptAt_left, hvc])
        (by rw [Over.comp_left, Category.assoc, Over.w e.hom, Over.w (ptAt F v s' hs i), Over.w (d i)]))
    let ψ : (𝟙_ (Over S) ⟶ C.A) →* (𝟙_ (Over S) ⟶ c.A) :=
      MonoidHom.mk' (· ≫ e.hom) fun a b => MonObj.mul_comp a b e.hom
    intro a
    have key : cAt F v s' hs a ≫ e.hom = ∏ i, d i ^ a i := by
      show ψ (cAt F v s' hs a) = _
      rw [cAt, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow]
      exact congrArg (· ^ a i) (hpt i)
    rw [← Category.assoc, ← Over.comp_left, key]

end GlobalTheory.LowChart
