import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PowAlongIso

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR (bw gm_linCombIso mem_finf)

section Stalk

variable {X X' X'' Y Y' Y₀ Z : Scheme.{0}}

theorem isGen_germ {L' L : LB X} (w : LB.Iso L' L) : w.IsGen ↔ ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (j j' : L.ι)
    (k k' : L'.ι), f y ∈ L.U j → f y ∈ L.U j' → f y ∈ L'.U k → f y ∈ L'.U k' →
    gm f y (L.U j ⊓ L'.U k) (w.s (j, k)) =
      gm f y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gm f y (L.U j' ⊓ L'.U k') (w.s (j', k')) := by
  constructor
  · intro hw Y f y j j' k k' hj hj' hk hk'
    have hm : f y ∈ L.U j ⊓ L'.U k ⊓ (L.U j' ⊓ L'.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have e := congrArg (gm f y (L.U j ⊓ L'.U k ⊓ (L.U j' ⊓ L'.U k'))) (hw (j, k) (j', k'))
    exact (gm_res f y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div L' L f y (j, k) (j', k') hm) (gm_res f y _ hm _))))
  · rintro h ⟨j, k⟩ ⟨j', k'⟩
    refine unit_ext fun x hx => ?_
    have := h _ (𝟙 X) x j j' k k' hx.1.1 hx.2.1 hx.1.2 hx.2.2
    exact (gm_res _ x _ hx _).trans (this.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div L' L (𝟙 X) x (j, k) (j', k') hx) (gm_res _ x _ hx _))).symm)

variable {M : LB X} {M' : LB X'} {M'' : LB X''} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem isGen_box (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) : w.IsGen ↔ ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X') (z : Z)
    (a a' : Fin j → M.ι) (b b' : M'.ι), ψ z ∈ LB.wchart M pr a → ψ z ∈ LB.wchart M pr a' → ψ z ∈ M'.U b →
    ψ z ∈ M'.U b' →
    bw w ψ z a b = (∏ i, gm (ψ ≫ pr i) z _ (M.g (a i) (a' i))) * (gm ψ z _ (M'.g b b'))⁻¹ * bw w ψ z a' b' := by
  rw [isGen_germ]
  refine forall_congr' fun Z => forall_congr' fun ψ => forall_congr' fun z => forall_congr' fun a =>
    forall_congr' fun a' => forall_congr' fun b => forall_congr' fun b' => forall_congr' fun ha =>
    forall_congr' fun ha' => forall_congr' fun hb => forall_congr' fun hb' => ?_
  have e := gm_linComb M pr (fun _ => 1) ψ z a a' ha ha'
  simp only [zpow_one] at e
  rw [← e]
  exact Iff.rfl

theorem mem_wchart_comp {E : X'' ⟶ X'} {x : X''} {a : Fin j → M.ι} :
    x ∈ LB.wchart M (fun i => E ≫ pr i) a ↔ E x ∈ LB.wchart M pr a :=
  ⟨fun h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i, fun h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i⟩

theorem exists_box_comp (hM : M.IsLB) (hM' : M'.IsLB) (hM'' : M''.IsLB) {E : X'' ⟶ X'} {pr' : Fin j → (X'' ⟶ X)}
    (hpr : ∀ i, pr' i = E ≫ pr i) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen)
    (w' : LB.Iso M'' (M'.pull E)) (hw' : w'.IsGen) :
    ∃ w'' : LB.Iso M'' (LB.LinComb M pr' (fun _ => 1)), w''.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z)
      (a : Fin j → M.ι) (b : M'.ι) (c : M''.ι), f z ∈ LB.wchart M pr' a → E (f z) ∈ M'.U b → f z ∈ M''.U c →
      bw w'' f z a c = bw w (f ≫ E) z a b * gw w' f z b c := by
  obtain rfl : pr' = fun i => E ≫ pr i := funext hpr
  rw [isGen_box] at hw
  rw [isGen_iff] at hw'
  have glue : ∀ (a : Fin j → M.ι) (c : M''.ι), ∃ s : Γ(X'', LB.wchart M (fun i => E ≫ pr i) a ⊓ M''.U c)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z) (b : M'.ι), f z ∈ LB.wchart M (fun i => E ≫ pr i) a →
        E (f z) ∈ M'.U b → f z ∈ M''.U c → gm f z _ s = bw w (f ≫ E) z a b * gw w' f z b c := by
    intro a c
    obtain ⟨W, hW⟩ : ∃ W : M'.ι → X''.Opens, ∀ b x, x ∈ W b ↔
        x ∈ LB.wchart M (fun i => E ≫ pr i) a ∧ E x ∈ M'.U b ∧ x ∈ M''.U c :=
      ⟨fun b => LB.wchart M (fun i => E ≫ pr i) a ⊓ (E ⁻¹ᵁ M'.U b ⊓ M''.U c), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ b, W b ≤ LB.wchart M (fun i => E ≫ pr i) a ⊓ M''.U c := fun b x hx =>
      ⟨((hW b x).1 hx).1, ((hW b x).1 hx).2.2⟩
    have l₁ : ∀ b, W b ≤ E ⁻¹ᵁ (LB.wchart M pr a ⊓ M'.U b) := fun b x hx =>
      ⟨mem_wchart_comp.1 ((hW b x).1 hx).1, ((hW b x).1 hx).2.1⟩
    have l₂ : ∀ b, W b ≤ (M'.pull E).U (fun _ => b) ⊓ M''.U c := fun b x hx =>
      ⟨mem_pull.2 ((hW b x).1 hx).2.1, ((hW b x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ b, Γ(X'', W b)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z) (b : M'.ι), f z ∈ W b →
        gm f z (W b) (u b) = bw w (f ≫ E) z a b * gw w' f z b c :=
      ⟨fun b => res (l₁ b) (pullU E _ (w.s (a, b))) * res (l₂ b) (w'.s (fun _ => b, c)), fun Z f z b hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f z (l₁ b) hz _).trans (gm_pull f E z _ (l₁ b hz) _)) (gm_res f z (l₂ b) hz _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨b, hb⟩ := exists_chart hM' (E x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨b, (hW b x).2 ⟨hx.1, hb, hx.2⟩⟩) u (fun b b' x hx => by
        have h₁ := (hW b x).1 hx.1
        have h₂ := (hW b' x).1 hx.2
        have ha := mem_wchart_comp.1 h₁.1
        have e₁ := hw _ (𝟙 X'' ≫ E) x a a b b' ha ha h₁.2.1 h₂.2.1
        have e₂ := hw' _ (𝟙 X'') x b b' c c h₁.2.1 h₂.2.1 h₁.2.2 h₁.2.2
        rw [Finset.prod_eq_one fun i _ => gm_self hM ((𝟙 X'' ≫ E) ≫ pr i) x (Set.mem_iInter.1 ha i)] at e₁
        rw [gm_self hM'' (𝟙 X'') x h₁.2.2] at e₂
        rw [hu _ (𝟙 X'') x b hx.1, hu _ (𝟙 X'') x b' hx.2, e₁, e₂, _root_.one_mul, inv_one, _root_.mul_one,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z f z b ha hb hc => ?_⟩
    have hz := (hW b (f z)).2 ⟨ha, hb, hc⟩
    exact (gm_res f z (l₀ b) hz s).symm.trans ((congrArg (gm f z (W b)) (hs b)).trans (hu Z f z b hz))
  choose s hs using glue
  let w'' : LB.Iso M'' (LB.LinComb M (fun i => E ≫ pr i) (fun _ => 1)) := ⟨fun p => s p.1 p.2⟩
  have T : ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z) (a : Fin j → M.ι) (b : M'.ι) (c : M''.ι),
      f z ∈ LB.wchart M (fun i => E ≫ pr i) a → E (f z) ∈ M'.U b → f z ∈ M''.U c →
      bw w'' f z a c = bw w (f ≫ E) z a b * gw w' f z b c := fun Z f z a b c ha hb hc => hs a c Z f z b ha hb hc
  refine ⟨w'', (isGen_box w'').2 fun Z f z a a' c c' ha ha' hc hc' => ?_, T⟩
  obtain ⟨b, hb⟩ := exists_chart hM' (E (f z))
  have e₁ := hw _ (f ≫ E) z a a' b b ((mem_wchart_comp (E := E)).1 ha) ((mem_wchart_comp (E := E)).1 ha') hb hb
  have e₂ := hw' _ f z b b c c' hb hb hc hc'
  rw [gm_self hM' (f ≫ E) z hb] at e₁ e₂
  rw [T Z f z a b c ha hb hc, T Z f z a' b c' ha' hb hc', e₁, e₂, inv_one, _root_.mul_one, _root_.one_mul,
    _root_.mul_mul_mul_comm]
  simp only [Category.assoc]

theorem gm_of_corr (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ}
    {h : Y' ⟶ Y} (hφ : ∀ k, φ' k = h ≫ φ k) {t : LB.Gen (LB.LinComb M φ ε)} {t' : LB.Gen (LB.LinComb M φ' ε)}
    (ht : t.IsGen) (ht' : t'.IsGen) (H : LB.Gen.Corr M _ _ _ _ t' (LB.pullGen M φ ε t h)) (r : Z ⟶ Y') (z : Z)
    {a : K → M.ι} (ha : r z ∈ LB.wchart M φ' a) :
    gm r z (LB.wchart M φ' a) (t'.s a) = gm (r ≫ h) z (LB.wchart M φ a) (t.s a) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  choose J hJ using fun χ : Z ⟶ X => exists_chart hM (χ z)
  have hJ : Good M z J := hJ
  have e := (val_corr hJ H r).trans (val_pull hJ t h r)
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])] at e
  have m := hJ.mem (fun k => h ≫ φ k) r
  rw [gen_trans ht' r z ha m, gen_trans ht (r ≫ h) z (j := a) (j' := fun k => J (r ≫ h ≫ φ k))
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 ha k) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 m k), ← e]
  simp only [trF, Category.assoc, val]

theorem box_maps_iff (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K]
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε))
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) :
    LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM →
      ∏ i, gm (r ≫ ρ i) z (LB.wchart M (φ i) (fun a => jN a i)) ((t i).s (fun a => jN a i)) =
        (∏ a, bw w (r ≫ φ' a) z (jN a) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι)
      (hm : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM),
      gm r z (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM) (res inf_le_left
        ((GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))).s jN)) =
        ∏ i, gm (r ≫ ρ i) z (LB.wchart M (φ i) (fun a => jN a i)) ((t i).s (fun a => jN a i)) := by
    intro Z r z jN jM hm
    refine (gm_res r z inf_le_left hm _).trans ((map_prod (gm r z (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN))
      (fun i => res (GeneratorPullback.box_le M pr φ' jN i)
        ((GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i)).s (fun a _ => jN a i))) Finset.univ).trans
      (Finset.prod_congr rfl fun i _ => ?_))
    have m := GeneratorPullback.box_le M pr φ' jN i hm.1
    have l := GeneratorPullback.pullAlong_le M (pr i) (ρ i) (φ i) φ' (hψ i) (fun a _ => jN a i)
    exact (gm_res r z (GeneratorPullback.box_le M pr φ' jN i) hm.1 _).trans ((gm_res r z l m _).trans (gm_pull r (ρ i) z _ (l m) _))
  constructor
  · intro H Z r z jN jM hm
    have E := congrArg (gm r z (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)) (H (jN, jM))
    exact (key Z r z jN jM hm).symm.trans (E.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linCombIso w φ' ε r z _ _ hm) (gm_res r z inf_le_right hm _))))
  · rintro H ⟨jN, jM⟩
    refine unit_ext fun y hy => ?_
    exact (key _ (𝟙 Y) y jN jM hy).trans ((H _ (𝟙 Y) y jN jM hy).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linCombIso w φ' ε (𝟙 Y) y _ _ hy) (gm_res (𝟙 Y) y inf_le_right hy _))).symm)

theorem box_maps_pull (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K]
    {φ₁ : K → (Y ⟶ X')} {φ₂ : K → (Y' ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ₁ : Fin j → (Y ⟶ Y₀)}
    {ρ₂ : Fin j → (Y' ⟶ Y₀)} {h : Y' ⟶ Y} (hφ : ∀ a, φ₂ a = h ≫ φ₁ a) (hρ : ∀ i, ρ₂ i = h ≫ ρ₁ i)
    (hψ₁ : ∀ i a, φ₁ a ≫ pr i = ρ₁ i ≫ φ i a) (hψ₂ : ∀ i a, φ₂ a ≫ pr i = ρ₂ i ≫ φ i a)
    {t₁ : LB.Gen (LB.LinComb M' φ₁ ε)} {t₂ : LB.Gen (LB.LinComb M' φ₂ ε)} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen)
    (hc : LB.Gen.Corr M' _ _ _ _ t₂ (LB.pullGen M' φ₁ ε t₁ h)) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ₁ ε) t₁
      (GeneratorPullback.boxGen M pr φ₁ ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ₁ i) (φ i) ε φ₁ (hψ₁ i) (t i)))) :
    LB.Gen.Maps (LB.linCombIso w φ₂ ε) t₂
      (GeneratorPullback.boxGen M pr φ₂ ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ₂ i) (φ i) ε φ₂ (hψ₂ i) (t i))) := by
  rw [box_maps_iff] at H ⊢
  intro Z r z jN jM hm
  rw [gm_of_corr hM' hφ h₁ h₂ hc r z hm.2]
  obtain rfl : φ₂ = fun k => h ≫ φ₁ k := funext hφ
  have := H Z (r ≫ h) z jN jM ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm.1 k,
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm.2 k⟩
  simpa only [hρ, Category.assoc] using this

theorem mapsAt_iff (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb M' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p ≫ pr i) (fun _ => n))) :
    GeneratorPullback.MapsAt M M' pr w p n a b ↔ ∀ (y : Y) (jN : Fin j → M.ι) (jL : M'.ι),
      p y ∈ LB.wchart M pr jN → p y ∈ M'.U jL →
      gm (𝟙 Y) y (LB.wchart M (fun i => p ≫ pr i) jN) (b.s jN) =
        bw w p y jN jL ^ n * gm (𝟙 Y) y ((M'.pull p).U (fun _ => jL)) (a.s (fun _ => jL)) := by
  have key : ∀ (y : Y) (jN : Fin j → M.ι) (jL : M'.ι) (hm : p y ∈ LB.wchart M pr jN ⊓ M'.U jL),
      gm (𝟙 Y) y _ ((pullU p _ (w.s (jN, jL))) ^ n * res (GeneratorPullback.mapsAt_le_a M M' pr p jN jL) (a.s (fun _ => jL))) =
        bw w p y jN jL ^ n * gm (𝟙 Y) y ((M'.pull p).U (fun _ => jL)) (a.s (fun _ => jL)) := fun y jN jL hm =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n)
      ((gm_pull (𝟙 Y) p y (LB.wchart M pr jN ⊓ M'.U jL) hm _).trans (by rw [Category.id_comp]; rfl))))
      (gm_res (𝟙 Y) y (GeneratorPullback.mapsAt_le_a M M' pr p jN jL) hm _))
  constructor
  · intro H y jN jL h₁ h₂
    exact (gm_res (𝟙 Y) y (GeneratorPullback.mapsAt_le_b M M' pr p jN jL) ⟨h₁, h₂⟩ _).symm.trans
      ((congrArg (gm (𝟙 Y) y _) (H jN jL)).trans (key y jN jL ⟨h₁, h₂⟩))
  · intro H jN jL
    exact unit_ext fun y hy => (gm_res (𝟙 Y) y (GeneratorPullback.mapsAt_le_b M M' pr p jN jL) hy _).trans
      ((H y jN jL hy.1 hy.2).trans (key y jN jL hy).symm)

theorem exists_mapsAt (hM' : M'.IsLB) {E : X'' ⟶ X'} {pr' : Fin j → (X'' ⟶ X)} (hpr : ∀ i, pr' i = E ≫ pr i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {w' : LB.Iso M'' (M'.pull E)}
    {w'' : LB.Iso M'' (LB.LinComb M pr' (fun _ => 1))}
    (T : ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z)
      (a : Fin j → M.ι) (b : M'.ι) (c : M''.ι), f z ∈ LB.wchart M pr' a → E (f z) ∈ M'.U b → f z ∈ M''.U c →
      bw w'' f z a c = bw w (f ≫ E) z a b * gw w' f z b c)
    {p : Y ⟶ X'} {p' : Y ⟶ X''} (hp : p' ≫ E = p) {a : LB.Gen (M'.pull p)} {a' : LB.Gen (M''.pull p')}
    (H : PMaps w' (K := PUnit) (fun _ => p') (fun _ => p) (fun _ => 1) a' a (𝟙 _))
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb M φ ε))
    (h : ∃ b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p ≫ pr i) (fun _ => 1)),
      GeneratorPullback.MapsAt M M' pr w p 1 a b ∧ LB.Gen.Corr M _ _ _ _ b c) :
    ∃ b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p' ≫ pr' i) (fun _ => 1)),
      GeneratorPullback.MapsAt M M'' pr' w'' p' 1 a' b ∧ LB.Gen.Corr M _ _ _ _ b c := by
  obtain rfl : pr' = fun i => E ≫ pr i := funext hpr
  subst hp
  obtain ⟨b, hb, hc⟩ := h
  have tr : ∀ ψ : Fin j → (Y ⟶ X), (fun i => (p' ≫ E) ≫ pr i) = ψ →
      ∃ b' : LB.Gen (LB.LinComb M ψ (fun _ => 1)), LB.Gen.Corr M _ _ _ _ b' c ∧ ∀ y jN,
        gm (𝟙 Y) y (LB.wchart M ψ jN) (b'.s jN) =
          gm (𝟙 Y) y (LB.wchart M (fun i => (p' ≫ E) ≫ pr i) jN) (b.s jN) := by
    rintro _ rfl
    exact ⟨b, hc, fun _ _ => rfl⟩
  obtain ⟨b', hc', hb'⟩ := tr (fun i => p' ≫ E ≫ pr i) (funext fun i => Category.assoc _ _ _)
  refine ⟨b', (mapsAt_iff _ _ _ _ _).2 fun y jN jL h₁ h₂ => ?_, hc'⟩
  obtain ⟨k, hk⟩ := exists_chart hM' (E (p' y))
  have e := H Y (𝟙 Y) y (fun _ => k) (fun _ => jL) (fun _ => hk) (fun _ => h₂)
  rw [Fintype.prod_unique, Category.id_comp, Category.id_comp] at e
  rw [hb', (mapsAt_iff _ _ _ _ _).1 hb y jN k ((mem_wchart_comp (E := E)).1 h₁) hk, T Y p' y jN k jL h₁ hk h₂, mul_zpow,
    _root_.mul_assoc]
  exact congrArg _ e

end Stalk

section Square

variable {B B' X X' X'' T T' T'' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB X} {L' : LB X'} {L'' : LB X''} {j : ℕ}
  {prB : Fin j → (B' ⟶ B)} {pr : Fin j → (X' ⟶ X)} {p : T ⟶ B} {f : T ⟶ X} {p' : T' ⟶ B'} {f' : T' ⟶ X'}

def Sq (wD : LB.Iso M' (LB.LinComb M prB (fun _ => 1))) (wL : LB.Iso L' (LB.LinComb L pr (fun _ => 1)))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) (ρ : Fin j → (T' ⟶ T)) : Prop :=
  ∀ (jNM : Fin j → M.ι) (jM' : M'.ι) (jL' : L'.ι) (jNL : Fin j → L.ι),
    res (X := T') (inf_le_left.trans (inf_le_left.trans inf_le_left) :
        p' ⁻¹ᵁ (LB.div (LB.LinComb M prB (fun _ => 1)) M').U (jNM, jM') ⊓
          (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') ⊓
          (⨅ i, ρ i ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (fun _ => jNM i, fun _ => jNL i)) ⊓
          f' ⁻¹ᵁ (LB.div (LB.LinComb L pr (fun _ => 1)) L').U (jNL, jL') ≤
        p' ⁻¹ᵁ (LB.div (LB.LinComb M prB (fun _ => 1)) M').U (jNM, jM'))
      (pullU p' _ (wD.s (jNM, jM'))) *
    res (X := T') (inf_le_left.trans (inf_le_left.trans inf_le_right)) (w'.s (fun _ => jM', fun _ => jL')) =
    (∏ i, res (X := T') (inf_le_left.trans (inf_le_right.trans (iInf_le _ i)))
      (pullU (ρ i) _ (w.s (fun _ => jNM i, fun _ => jNL i)))) *
    res (X := T') inf_le_right (pullU f' _ (wL.s (jNL, jL')))

theorem sq_iff (wD : LB.Iso M' (LB.LinComb M prB (fun _ => 1))) (wL : LB.Iso L' (LB.LinComb L pr (fun _ => 1)))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) (ρ : Fin j → (T' ⟶ T)) :
    Sq wD wL w w' ρ ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jNM : Fin j → M.ι) (jM' : M'.ι) (jL' : L'.ι)
      (jNL : Fin j → L.ι), p' (r z) ∈ LB.wchart M prB jNM → p' (r z) ∈ M'.U jM' → f' (r z) ∈ L'.U jL' →
      (∀ i, p (ρ i (r z)) ∈ M.U (jNM i)) → (∀ i, f (ρ i (r z)) ∈ L.U (jNL i)) → f' (r z) ∈ LB.wchart L pr jNL →
      bw wD (r ≫ p') z jNM jM' * gw w' r z jM' (fun _ => jL') =
        (∏ i, gw w (r ≫ ρ i) z (jNM i) (fun _ => jNL i)) * bw wL (r ≫ f') z jNL jL' := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jNM : Fin j → M.ι) (jM' : M'.ι) (jL' : L'.ι)
      (jNL : Fin j → L.ι) (V : T'.Opens) (hm : r z ∈ V)
      (l₁ : V ≤ p' ⁻¹ᵁ (LB.div (LB.LinComb M prB (fun _ => 1)) M').U (jNM, jM'))
      (l₂ : V ≤ (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL'))
      (l₃ : ∀ i, V ≤ ρ i ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (fun _ => jNM i, fun _ => jNL i))
      (l₄ : V ≤ f' ⁻¹ᵁ (LB.div (LB.LinComb L pr (fun _ => 1)) L').U (jNL, jL')),
      gm r z V (res l₁ (pullU p' _ (wD.s (jNM, jM'))) * res l₂ (w'.s (fun _ => jM', fun _ => jL'))) =
        bw wD (r ≫ p') z jNM jM' * gw w' r z jM' (fun _ => jL') ∧
      gm r z V ((∏ i, res (l₃ i) (pullU (ρ i) _ (w.s (fun _ => jNM i, fun _ => jNL i)))) *
        res l₄ (pullU f' _ (wL.s (jNL, jL')))) =
        (∏ i, gw w (r ≫ ρ i) z (jNM i) (fun _ => jNL i)) * bw wL (r ≫ f') z jNL jL' :=
    fun Z r z jNM jM' jL' jNL V hm l₁ l₂ l₃ l₄ =>
      ⟨(map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z l₁ hm _).trans (gm_pull r p' z _ (l₁ hm) _))
        (gm_res r z l₂ hm _)),
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
        (gm_res r z (l₃ i) hm _).trans (gm_pull r (ρ i) z _ (l₃ i hm) _)))
        ((gm_res r z l₄ hm _).trans (gm_pull r f' z _ (l₄ hm) _)))⟩
  constructor
  · intro H Z r z jNM jM' jL' jNL h₁ h₂ h₃ h₄ h₅ h₆
    have hm : r z ∈ p' ⁻¹ᵁ (LB.div (LB.LinComb M prB (fun _ => 1)) M').U (jNM, jM') ⊓
          (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') ⊓
          (⨅ i, ρ i ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (fun _ => jNM i, fun _ => jNL i)) ⊓
          f' ⁻¹ᵁ (LB.div (LB.LinComb L pr (fun _ => 1)) L').U (jNL, jL') :=
      ⟨⟨⟨⟨h₁, h₂⟩, mem_pull.2 h₂, mem_pull.2 h₃⟩, by
        rw [← Finset.inf_univ_eq_iInf]
        exact mem_finf _ _ _ fun i _ => ⟨mem_pull.2 (h₄ i), mem_pull.2 (h₅ i)⟩⟩, h₆, h₃⟩
    obtain ⟨k₁, k₂⟩ := key Z r z jNM jM' jL' jNL _ hm (inf_le_left.trans (inf_le_left.trans inf_le_left))
      (inf_le_left.trans (inf_le_left.trans inf_le_right))
      (fun i => inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) inf_le_right
    exact k₁.symm.trans ((congrArg (gm r z _) (H jNM jM' jL' jNL)).trans k₂)
  · intro H jNM jM' jL' jNL
    refine unit_ext fun y hy => ?_
    obtain ⟨k₁, k₂⟩ := key _ (𝟙 T') y jNM jM' jL' jNL _ hy (inf_le_left.trans (inf_le_left.trans inf_le_left))
      (inf_le_left.trans (inf_le_left.trans inf_le_right))
      (fun i => inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) inf_le_right
    have m := fun i => iInf_le (fun i => ρ i ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (fun _ => jNM i, fun _ => jNL i)) i
      hy.1.2
    exact k₁.trans ((H _ (𝟙 T') y jNM jM' jL' jNL hy.1.1.1.1 hy.1.1.1.2 hy.2.2 (fun i => mem_pull.1 (m i).1)
      (fun i => mem_pull.1 (m i).2) hy.2.1).trans k₂.symm)

theorem sq_pull (hL' : L'.IsLB) {E : X'' ⟶ X'} {pr' : Fin j → (X'' ⟶ X)} (hpr : ∀ i, pr' i = E ≫ pr i)
    {wD : LB.Iso M' (LB.LinComb M prB (fun _ => 1))} {wL : LB.Iso L' (LB.LinComb L pr (fun _ => 1))}
    {v : LB.Iso L'' (L'.pull E)} {wL' : LB.Iso L'' (LB.LinComb L pr' (fun _ => 1))}
    (hT : ∀ (Z : Scheme.{0}) (g : Z ⟶ X'') (z : Z)
      (a : Fin j → L.ι) (b : L'.ι) (c : L''.ι), g z ∈ LB.wchart L pr' a → E (g z) ∈ L'.U b → g z ∈ L''.U c →
      bw wL' g z a c = bw wL (g ≫ E) z a b * gw v g z b c)
    {p'' : T'' ⟶ B'} {f'' : T'' ⟶ X''} {h : T'' ⟶ T'} (hp : p'' = h ≫ p') (hf : h ≫ f' = f'' ≫ E)
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')}
    {w'' : LB.Iso (L''.pull f'') (M'.pull p'')} {ρ : Fin j → (T' ⟶ T)} {ρ' : Fin j → (T'' ⟶ T)}
    (hρ : ∀ i, ρ' i = h ≫ ρ i)
    (hw : ∀ (Z : Scheme.{0}) (r : Z ⟶ T'') (z : Z) (jM : M'.ι) (jL : L'.ι) (jL' : L''.ι), p'' (r z) ∈ M'.U jM →
      E (f'' (r z)) ∈ L'.U jL → f'' (r z) ∈ L''.U jL' →
      gw w'' r z jM (fun _ => jL') = gw w' (r ≫ h) z jM (fun _ => jL) * gw v (r ≫ f'') z jL jL')
    (H : Sq wD wL w w' ρ) : Sq wD wL' w w'' ρ' := by
  obtain rfl : pr' = fun i => E ≫ pr i := funext hpr
  obtain rfl : ρ' = fun i => h ≫ ρ i := funext hρ
  subst hp
  rw [sq_iff] at H ⊢
  intro Z r z jNM jM' jL' jNL h₁ h₂ h₃ h₄ h₅ h₆
  obtain ⟨k, hk⟩ := exists_chart hL' (E (f'' (r z)))
  have e : f' (h (r z)) = E (f'' (r z)) := congrArg (fun g : T'' ⟶ X' => g (r z)) hf
  have a := H Z (r ≫ h) z jNM jM' k jNL h₁ h₂ (show f' (h (r z)) ∈ _ from e ▸ hk) h₄ h₅
    (show f' (h (r z)) ∈ _ from e ▸ (mem_wchart_comp (E := E)).1 h₆)
  rw [hw Z r z jM' k jL' h₂ hk h₃, hT Z (r ≫ f'') z jNL k jL' h₆ hk h₃, ← _root_.mul_assoc, ← _root_.mul_assoc]
  simp only [Category.assoc, hf] at a ⊢
  rw [a]

end Square

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G) (U : Unif I D A G) (U' : Unif I D A G'), IsMonHom ε.hom → SameUnif ε U.toUnifPre U'.toUnifPre → ∀ (j : ℕ) (D₀ : DegData R I) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif I D₀ A₀ G₀) (pD : IsPowDeg D.toPre D₀.toPre j) (pA : IsPowPolAV A A₀ j) (pG : IsPowGrp G G₀ j) (pG' : IsPowGrp G' G₀ j), (∀ i, ε.hom ≫ pG.pr i = pG'.pr i) → Nonempty (UnifPowOf3 pD pA pG U U₀) → Nonempty (UnifPowOf3 pD pA pG' U' U₀) := by
  intro R _ _ I D A G G' _ _ _ _ ε U U' hε ⟨hgen, v, ⟨hv, hvr⟩, hS⟩ j D₀ A₀ G₀ _ _ U₀ pD pA pG pG' hpr ⟨P⟩
  have hpr' : ∀ i, (pG'.pr i).left = ε.hom.left ≫ (pG.pr i).left := fun i => congrArg (fun q => q.left) (hpr i).symm
  obtain ⟨wL, wL_gen, hT⟩ := exists_box_comp U₀.LG.isLB U.LG.isLB U'.LG.isLB hpr' P.wL P.wL_gen v hv
  have he : eSec G' ≫ ε.hom.left = eSec G := congrArg (fun q => q.left) (IsMonHom.one_hom ε.hom)
  have hρ : ∀ e i, ((Over.pullback (thick R I e)).map (pG'.pr i)).left =
      ((Over.pullback (thick R I e)).map ε.hom).left ≫ ((Over.pullback (thick R I e)).map (pG.pr i)).left :=
    fun e i => by rw [← hpr, Functor.map_comp, Over.comp_left]
  have hp : ∀ e, (U'.gt e).pG =
      (Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map ε.hom) ≫ (U.gt e).pG := fun e => by
    rw [GtCoord.pG, (hS e).1, Functor.map_comp, Category.assoc]
  have hO : ∀ e x k, D.toPre.Oφ (U'.gt e).pG x k =
      ((Over.pullback (thick R I e)).map ε.hom).left ≫ D.toPre.Oφ (U.gt e).pG x k := fun e x k => by
    rw [hp]
    exact (WeightPf.Oφ_comp ((Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map ε.hom)) (U.gt e).pG x k).symm
  refine ⟨⟨⟨⟨fun i => ?_, wL, wL_gen, exists_mapsAt U.LG.isLB hpr' hT he hvr _ P.wL_rig, fun e i => ?_⟩,
    fun e x => ?_⟩, fun e => ?_⟩⟩
  · rw [hgen, Category.assoc, P.gen_pr, ← hpr, Functor.map_comp, Category.assoc]
  · rw [(hS e).1, Category.assoc, P.q_pr, ← hpr, Functor.map_comp, Category.assoc]
  · obtain ⟨hψ, H⟩ := P.t_pr e x
    refine ⟨fun i k => ?_, box_maps_pull (Y := (thickObj R I e G).left) (Y' := (thickObj R I e G').left)
      (Y₀ := (thickObj R I e G₀).left) D.toPre.P.isLB pD.w (hO e x) (hρ e) hψ _ ((U.gt e).t_gen x)
      ((U'.gt e).t_gen x) ((hS e).2.1 x) _ H⟩
    exact (congrArg (· ≫ (pD.pw.pr i).left) (hO e x k)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (hψ i k)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hρ e i).symm))))
  · exact sq_pull (T := (thickObj R I e G₀).left) (T' := (thickObj R I e G).left) (T'' := (thickObj R I e G').left)
      U.LG.isLB hpr' hT (congrArg (fun q => q.left) (hp e)) (pullback.lift_fst _ _ _) (hρ e) (hS e).2.2 (P.w_pr e)

end GlobalTheory.PowAlongIso
