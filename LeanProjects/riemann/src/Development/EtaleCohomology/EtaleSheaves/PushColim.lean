import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
import Development.EtaleCohomology.EtaleSheaves.KillKerPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

abbrev PP (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) := pull (ZMod q) (sch.map (Spec.map f)) (tw q i) n
theorem PP_comp (q : ℕ) (i n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (x) :
    PP q i n (f ≫ g) x = PP q i n g (PP q i n f x) := by
  rw [PP, Spec.map_comp, Functor.map_comp, pull_comp]
theorem unit_of {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (h : IsUnit (q : A)) : IsUnit (q : B) := by
  simpa using h.map f.hom

abbrev HR (q : ℕ) (i n : ℤ) {D Y : CommRingCat.{0}} (φ : D ⟶ Y) := Hrel (ZMod q) (sch.map (Spec.map φ)) (tw q i) n

abbrev RP (q : ℕ) (i n : ℤ) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z) (ψ : E ⟶ Z)
    (h : φ ≫ u = e ≫ ψ) : HR q i n φ →+ HR q i n ψ :=
  rpl q i (Spec.map φ) (Spec.map ψ) (Spec.map u) (Spec.map e) (by rw [← Spec.map_comp, ← Spec.map_comp, h]) n

theorem RP_comp (q : ℕ) (i n : ℤ) {D Y E Z E' Z' : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z) (ψ : E ⟶ Z)
    (h : φ ≫ u = e ≫ ψ) (e' : E ⟶ E') (u' : Z ⟶ Z') (ψ' : E' ⟶ Z') (h' : ψ ≫ u' = e' ≫ ψ') (e2 : D ⟶ E') (u2 : Y ⟶ Z')
    (h2 : φ ≫ u2 = e2 ≫ ψ') (he : e ≫ e' = e2) (hu : u ≫ u' = u2) (z : HR q i n φ) :
    RP q i n φ e2 u2 ψ' h2 z = RP q i n ψ e' u' ψ' h' (RP q i n φ e u ψ h z) :=
  rpull_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [← hu, Spec.map_comp, Functor.map_comp])
    (by rw [← he, Spec.map_comp, Functor.map_comp]) n z

theorem RP_bd (q : ℕ) (i m n : ℤ) (hm : 1 + m = n) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z)
    (ψ : E ⟶ Z) (h : φ ≫ u = e ≫ ψ) (y) :
    RP q i n φ e u ψ h (bd _ _ _ m n hm y) = bd _ _ _ m n hm (PP q i m u y) := rpull_bd ..

theorem fgt_RP (q : ℕ) (i n : ℤ) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z)
    (ψ : E ⟶ Z) (h : φ ≫ u = e ≫ ψ) (z : HR q i n φ) :
    fgt _ _ _ n (RP q i n φ e u ψ h z) = PP q i n e (fgt _ _ _ n z) := relNat _ _ _ _ _ _ _ n z

theorem pushColim {A Y C Y' : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) (w : Y ⟶ Y') (φ' : C ⟶ Y')
    (hpo : IsPushout φ c w φ') {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj A ⟶ D) (s : D ⟶ (Functor.const J).obj C) (hc : IsColimit (Cocone.mk _ s))
    (ht : ∀ j, t.app j ≫ s.app j = c) :
    ∃ (E : J ⥤ CommRingCat.{0}) (p : D ⟶ E) (e : E ⟶ (Functor.const J).obj Y') (v : ∀ j, Y ⟶ E.obj j),
      Nonempty (IsColimit (Cocone.mk _ e)) ∧ (∀ j, IsPushout φ (t.app j) (v j) (p.app j)) ∧
      (∀ j, p.app j ≫ e.app j = s.app j ≫ φ') ∧ ∀ j k (f : j ⟶ k), v j ≫ E.map f = v k := by
  have : IsConnected J := IsFiltered.isConnected J
  let F : J ⥤ Under A := D.toUnder A (fun j => t.app j) (fun {j k} g => by
    have := t.naturality g
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    exact this.symm)
  let cU : Cocone F :=
    { pt := Under.mk c
      ι := { app := fun j => Under.homMk (s.app j) (ht j)
             naturality := fun j k g => by
               apply Under.UnderMorphism.ext
               exact s.naturality g } }
  have hcU : IsColimit cU := isColimitOfReflects (Under.forget A) (by exact hc)
  have h2 := isColimitOfPreserves (Under.pushout φ ⋙ Under.forget Y) hcU
  let E : J ⥤ CommRingCat.{0} := F ⋙ Under.pushout φ ⋙ Under.forget Y
  let e : E ⟶ (Functor.const J).obj Y' :=
    ((Under.pushout φ ⋙ Under.forget Y).mapCocone cU).ι ≫ (Functor.const J).map hpo.flip.isoPushout.inv
  have hE : IsColimit (Cocone.mk _ e) :=
    h2.ofIsoColimit (Cocone.ext hpo.flip.isoPushout.symm (fun j => rfl))
  let p : D ⟶ E :=
    { app := fun j => (pushout.inl (t.app j) φ : D.obj j ⟶ pushout (t.app j) φ)
      naturality := fun j k g => by
        exact (pushout.inl_desc _ _ _).symm }
  refine ⟨E, p, e, fun j => pushout.inr (t.app j) φ, ⟨hE⟩, fun j => (IsPushout.of_hasPushout (t.app j) φ).flip,
    fun j => ?_, fun j k f => pushout.inr_desc _ _ _⟩
  have key : ∀ h, pushout.inl (t.app j) φ ≫ (pushout.desc (s.app j ≫ pushout.inl c φ) (pushout.inr c φ) h ≫
      hpo.flip.isoPushout.inv) = s.app j ≫ φ' := by
    intro h; rw [← Category.assoc, pushout.inl_desc, Category.assoc, hpo.flip.inl_isoPushout_inv]
  exact key _

theorem relAt (hB1 : B1) (q : ℕ) (i n : ℤ) {D Y' O : CommRingCat.{0}} (φ' : D ⟶ Y') (hq : IsUnit (q : D)) (o : D ⟶ O)
    (hIE : IE o) (hBC : BC q i φ' o) (z : HR q i n φ') (hz : PP q i n φ' (fgt _ _ _ n z) = 0) :
    ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (s : E ⟶ O) (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z)
      (h : IsPushout φ' e u ψ), Et e ∧ e ≫ s = o ∧ RP q i n φ' e u ψ h.w z = 0 := by
  obtain ⟨J, _, _, F, t, s, hc, hts⟩ := hIE
  have hZ := IsPushout.of_hasPushout φ' o
  set ψ := pushout.inr φ' o
  have hRE := hBC _ _ _ hZ
  obtain ⟨G, p, e, v, ⟨hG⟩, hpo, hpe, hv⟩ := pushColim φ' o _ ψ hZ F t s hc (fun j => (hts j).2)
  have hnat : ∀ {j k} (f : j ⟶ k), t.app j ≫ F.map f = t.app k := fun f => by simpa using (t.naturality f).symm
  have hs : ∀ {j k} (f : j ⟶ k), F.map f ≫ s.app k = s.app j := fun f => by simpa using s.naturality f
  have he : ∀ {j k} (f : j ⟶ k), G.map f ≫ e.app k = e.app j := fun f => by simpa using e.naturality f
  have hxO : PP q i n o (fgt _ _ _ n z) = 0 := by
    apply (hRE n).1
    change PP q i n ψ _ = _
    rw [map_zero, ← PP_comp, ← hZ.w, PP_comp, hz, map_zero]
  obtain ⟨j0⟩ : Nonempty J := IsFiltered.nonempty
  obtain ⟨k, f, hk⟩ := (hB1 q F _ hc n i).2 j0 (PP q i n (t.app j0) (fgt _ _ _ n z)) (unit_of (t.app j0) hq) (by
    change PP q i n (s.app j0) _ = 0
    rw [← PP_comp, (hts j0).2, hxO])
  change PP q i n (F.map f) _ = 0 at hk
  rw [← PP_comp, hnat] at hk
  have hm : 1 + (n - 1) = n := by omega
  obtain ⟨y, hy⟩ := exists_bd _ _ _ (n - 1) n hm (RP q i n φ' (t.app k) (v k) (p.app k) (hpo k).w z)
    (by rw [fgt_RP]; exact hk)
  obtain ⟨a, ha⟩ := (hRE (n - 1)).2 (PP q i (n - 1) (e.app k) y)
  obtain ⟨j, b, rfl⟩ := (hB1 q F _ hc (n - 1) i).1 a (unit_of o hq)
  change PP q i (n - 1) ψ (PP q i (n - 1) (s.app j) b) = _ at ha
  obtain ⟨l, g, hl⟩ := (hB1 q G _ hG (n - 1) i).2 (IsFiltered.max j k)
    (PP q i (n - 1) (G.map (IsFiltered.rightToMax j k)) y -
      PP q i (n - 1) (F.map (IsFiltered.leftToMax j k) ≫ p.app _) b) (unit_of (t.app _ ≫ p.app _) hq) (by
    change PP q i (n - 1) (e.app _) _ = 0
    rw [map_sub, ← PP_comp, ← PP_comp, he, Category.assoc, hpe, ← Category.assoc, hs, PP_comp, ha, sub_self])
  change PP q i (n - 1) (G.map g) _ = 0 at hl
  rw [map_sub, sub_eq_zero, ← PP_comp, ← PP_comp, ← G.map_comp, Category.assoc, ← p.naturality g,
    ← Category.assoc, PP_comp q i (n - 1) _ (p.app l)] at hl
  refine ⟨F.obj l, t.app l, s.app l, G.obj l, v l, p.app l, hpo l, (hts l).1, (hts l).2, ?_⟩
  rw [RP_comp q i n φ' (t.app k) (v k) (p.app k) (hpo k).w (F.map (IsFiltered.rightToMax j k ≫ g))
    (G.map (IsFiltered.rightToMax j k ≫ g)) (p.app l) (p.naturality _).symm _ _ _ (hnat _) (hv _ _ _), ← hy, RP_bd, hl]
  exact bd_pull ..

end LateralTheory.E.KernelLocalization
