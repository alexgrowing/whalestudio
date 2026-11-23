import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem comp_ap {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C) (x : A) :
    (u ≫ v) x = v (u x) := by simp

private def lvlIso {V Y : Scheme.{0}} (f : V ⟶ Y) (p : ℕ) :
    yoneda.obj (widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f)) ≅
      widePullback (yoneda.obj Y) (fun _ : Fin (p + 1) => yoneda.obj V)
        (fun _ => yoneda.map f) :=
  preservesLimitIso yoneda (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f)) ≪≫
    HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan
      (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f) ⋙ yoneda))

private theorem lvlIso_base {V Y : Scheme.{0}} (f : V ⟶ Y) (p : ℕ) :
    (lvlIso f p).hom ≫ WidePullback.base (fun _ : Fin (p + 1) => yoneda.map f) =
      yoneda.map (WidePullback.base (fun _ : Fin (p + 1) => f)) := by
  have h := HasLimit.isoOfNatIso_hom_π (WidePullbackShape.diagramIsoWideCospan
    (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f) ⋙ yoneda)) none
  have h2 := preservesLimitIso_hom_π yoneda
    (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f)) none
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (h.trans (Category.comp_id _))).trans h2)

private theorem piece_open {V Y : Scheme.{0}} (f : V ⟶ Y) (p : ℕ) {T : Fin (p + 1) → Scheme.{0}}
    (j : ∀ i, T i ⟶ V) (h1 : ∀ i, IsOpenImmersion (j i)) (h2 : ∀ i, IsOpenImmersion (j i ≫ f))
    (O : (widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f)).Opens)
    (hO : (O : Set _) = ⋂ i, (WidePullback.π (fun _ : Fin (p + 1) => f) i) ⁻¹' Set.range (j i)) :
    IsOpenImmersion (O.ι ≫ WidePullback.base (fun _ : Fin (p + 1) => f)) := by
  have hb : ∀ (i : Fin (p + 1)) z, (WidePullback.base (fun _ : Fin (p + 1) => f)) z =
      f ((WidePullback.π (fun _ : Fin (p + 1) => f) i) z) := by
    intro i z
    rw [← comp_ap, WidePullback.π_arrow]
  have hxO : ∀ (x : O.toScheme) (i : Fin (p + 1)),
      (WidePullback.π (fun _ : Fin (p + 1) => f) i) (O.ι x) ∈ Set.range (j i) := by
    intro x i
    have hx : O.ι x ∈ (O : Set _) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
    rw [hO] at hx
    exact Set.mem_iInter.1 hx i
  let W : Y.Opens := ⟨⋂ i, Set.range (j i ≫ f),
    isOpen_iInter_of_finite fun i => (j i ≫ f).opensRange.2⟩
  have hW : ∀ (w : W.toScheme) (i : Fin (p + 1)), W.ι w ∈ Set.range (j i ≫ f) := by
    intro w i
    have hw : W.ι w ∈ (W : Set _) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩
    exact Set.mem_iInter.1 hw i
  have hr : Set.range (O.ι ≫ WidePullback.base (fun _ : Fin (p + 1) => f)) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine Set.mem_iInter.2 fun i => ?_
    obtain ⟨y, hy⟩ := hxO x i
    exact ⟨y, by rw [comp_ap, hy, comp_ap, hb i]⟩
  let r := IsOpenImmersion.lift W.ι _ hr
  have hl : ∀ i, Set.range W.ι ⊆ Set.range (j i ≫ f) := by
    rintro i _ ⟨w, rfl⟩
    exact hW w i
  let l : ∀ i, W.toScheme ⟶ T i := fun i => IsOpenImmersion.lift (j i ≫ f) W.ι (hl i)
  have hlf : ∀ i, l i ≫ j i ≫ f = W.ι := fun i => IsOpenImmersion.lift_fac _ _ _
  let L : W.toScheme ⟶ widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f) :=
    WidePullback.lift W.ι (fun i => l i ≫ j i) (fun i => by simpa using hlf i)
  have hLπ : ∀ i, L ≫ WidePullback.π (fun _ : Fin (p + 1) => f) i = l i ≫ j i :=
    fun i => WidePullback.lift_π _ _ _ _ i
  have hLb : L ≫ WidePullback.base (fun _ : Fin (p + 1) => f) = W.ι :=
    WidePullback.lift_base _ _ _ _
  have hs : Set.range L ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι, hO]
    rintro _ ⟨w, rfl⟩
    refine Set.mem_iInter.2 fun i => ?_
    refine ⟨l i w, ?_⟩
    have := congr($(hLπ i) w)
    rw [comp_ap, comp_ap] at this
    exact this.symm
  let s := IsOpenImmersion.lift O.ι L hs
  have hsO : s ≫ O.ι = L := IsOpenImmersion.lift_fac _ _ _
  have hrW : r ≫ W.ι = O.ι ≫ WidePullback.base (fun _ : Fin (p + 1) => f) :=
    IsOpenImmersion.lift_fac _ _ _
  have hm : ∀ i, Set.range (O.ι ≫ WidePullback.π (fun _ : Fin (p + 1) => f) i) ⊆
      Set.range (j i) := by
    rintro i _ ⟨x, rfl⟩
    rw [comp_ap]
    exact hxO x i
  have hrs : r ≫ s = 𝟙 _ := by
    rw [← cancel_mono O.ι, Category.assoc, hsO, Category.id_comp]
    apply WidePullback.hom_ext
    · intro i
      rw [Category.assoc, hLπ, ← IsOpenImmersion.lift_fac (j i) _ (hm i), ← Category.assoc]
      congr 1
      rw [← cancel_mono (j i ≫ f), Category.assoc, hlf, hrW,
        IsOpenImmersion.lift_fac_assoc, Category.assoc, WidePullback.π_arrow]
    · rw [Category.assoc, hLb, hrW]
  have hsr : s ≫ r = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, hrW, ← Category.assoc, hsO, hLb, Category.id_comp]
  have : IsIso r := ⟨s, hrs, hsr⟩
  rw [← hrW]
  infer_instance

theorem UpperTheory.cech_nerve_representable_disjoint :
    ∀ {V Y : Scheme.{0}} (f : V ⟶ Y), (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) → ∀ p : ℕ, ∃ (Z : Scheme.{0}) (g : Z ⟶ Y) (e : yoneda.obj Z ≅ (cech f).obj (op (SimplexCategory.mk p))),
      e.hom ≫ (cechAug f).app (op (SimplexCategory.mk p)) = yoneda.map g ∧ (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ Z), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : Z, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ g)) := by
  rintro V Y f ⟨ι, O, j, hj, hd, hc, hf⟩ p
  let π := fun i => WidePullback.π (fun _ : Fin (p + 1) => f) i
  let U : (Fin (p + 1) → ι) → (widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f)).Opens :=
    fun a => ⟨⋂ i, (π i) ⁻¹' Set.range (j (a i)),
      isOpen_iInter_of_finite fun i => (j (a i)).opensRange.2.preimage (π i).continuous⟩
  have hU : ∀ a z, z ∈ Set.range (U a).ι ↔ ∀ i, (π i) z ∈ Set.range (j (a i)) := by
    intro a z
    rw [Scheme.Opens.range_ι]
    exact Set.mem_iInter
  refine ⟨widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f),
    WidePullback.base (fun _ : Fin (p + 1) => f), lvlIso f p,
    lvlIso_base f p, Fin (p + 1) → ι, fun a => (U a).toScheme, fun a => (U a).ι,
    fun a => inferInstance, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hab
    refine Set.disjoint_left.2 fun z hza hzb => ?_
    exact Set.disjoint_left.1 (hd _ _ hi) ((hU a z).1 hza i) ((hU b z).1 hzb i)
  · intro z
    choose a ha using fun i => hc ((π i) z)
    exact ⟨a, (hU a z).2 ha⟩
  · intro a
    exact piece_open f p (fun i => j (a i)) (fun i => hj _) (fun i => hf _) (U a) rfl

end
