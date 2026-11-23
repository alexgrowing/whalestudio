import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
import Development.AutomorphicArithmetic.CommutativeAlgebra.CechNerveRepresentableDisjoint
import Development.AutomorphicArithmetic.CommutativeAlgebra.CechNerveRestrictOpen
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem conn_mono {R : Type} [CommRing R] {F : Shv R} {c c' : ℤ} (h : c' ≤ c) {E E' : Spc} {f : E ⟶ E'}
    (hf : Conn R F c f) : Conn R F c' f :=
  fun n => ⟨fun hn => (hf n).1 (by omega), fun hn => (hf n).2 (by omega)⟩

private theorem conn_square {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {E₁ E₂ E₃ E₄ : Spc} {u : E₁ ⟶ E₂}
    {v : E₃ ⟶ E₄} {a : E₁ ⟶ E₃} {b : E₂ ⟶ E₄} (w : u ≫ b = a ≫ v) (ha : Eqv R a F) (hb : Eqv R b F)
    (hu : Conn R F c u) : Conn R F c v := by
  have key : ∀ (n : ℤ) (x : H R E₄ F n), pull R a F n (pull R v F n x) = pull R u F n (pull R b F n x) := by
    intro n x
    rw [← pull_comp, ← pull_comp, w]
  have inj : ∀ n : ℤ, Function.Injective (pull R u F n) → Function.Injective (pull R v F n) := by
    intro n hi x y h
    exact (hb n).1 (hi ((key n x).symm.trans ((congrArg _ h).trans (key n y))))
  have sur : ∀ n : ℤ, Function.Surjective (pull R u F n) → Function.Surjective (pull R v F n) := by
    intro n hs y
    obtain ⟨z, hz⟩ := hs (pull R a F n y)
    obtain ⟨x, rfl⟩ := (hb n).2 z
    exact ⟨x, (ha n).1 ((key n x).trans hz)⟩
  intro n
  exact ⟨fun hn => ⟨inj n ((hu n).1 hn).1, sur n ((hu n).1 hn).2⟩, fun hn => inj n ((hu n).2 hn)⟩

private theorem eqv_of_iso {R : Type} [CommRing R] {F : Shv R} {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

private theorem conn_level {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {P Q : PSh} (ψ : P ⟶ Q) {Z Z' : Scheme.{0}}
    (k : Z' ⟶ Z) (e : yoneda.obj Z ≅ Q) (e' : yoneda.obj Z' ≅ P) (h : e'.hom ≫ ψ = yoneda.map k ≫ e.hom)
    (hk : Conn R F c (sch.map k)) : Conn R F c (disc.map ψ) := by
  refine conn_square (u := sch.map k) (a := (disc.mapIso e').hom) (b := (disc.mapIso e).hom) ?_
    (eqv_of_iso _) (eqv_of_iso _) hk
  change disc.map (yoneda.map k) ≫ disc.map e.hom = disc.map e'.hom ≫ disc.map ψ
  rw [← Functor.map_comp, ← Functor.map_comp, h]

private theorem cech_zero {V Y : Scheme.{0}} (f : V ⟶ Y) :
    ∃ e : yoneda.obj V ≅ (cech f).obj (op (SimplexCategory.mk 0)),
      e.hom ≫ (cechAug f).app (op (SimplexCategory.mk 0)) = yoneda.map f := by
  let π₀ : Fin 1 → (yoneda.obj V ⟶ yoneda.obj Y) := fun _ => yoneda.map f
  let h : yoneda.obj V ⟶ widePullback (yoneda.obj Y) (fun _ : Fin 1 => yoneda.obj V) π₀ :=
    WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  let k : widePullback (yoneda.obj Y) (fun _ : Fin 1 => yoneda.obj V) π₀ ⟶ yoneda.obj V :=
    WidePullback.π π₀ 0
  have hk : h ≫ k = 𝟙 _ := WidePullback.lift_π _ _ _ _ _
  have hb : h ≫ WidePullback.base π₀ = yoneda.map f := WidePullback.lift_base _ _ _ _
  have kh : k ≫ h = 𝟙 _ := by
    apply WidePullback.hom_ext
    · intro j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [Category.assoc, Category.id_comp]
      change k ≫ h ≫ k = k
      rw [hk, Category.comp_id]
    · rw [Category.assoc, hb, Category.id_comp]
      exact WidePullback.π_arrow π₀ 0
  exact ⟨⟨h, k, hk, kh⟩, hb⟩

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_of_cover {V Y : Scheme.{0}} (f : V ⟶ Y)
    (hcov : ∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) :
    Smooth f := by
  obtain ⟨ι, O, j, hj, -, hc, hf⟩ := hcov
  let 𝒰 : V.OpenCover := Scheme.Cover.mkOfCovers ι O j (fun y => by
    obtain ⟨a, x, hx⟩ := hc y
    exact ⟨a, x, hx⟩)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 fun a => ?_
  have := hf a
  change Smooth (j a ≫ f)
  infer_instance

theorem UpperTheory.connectivity_of_cech_disjoint_cover :
    LeafLevel → A1 → A2 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {V Y : Scheme.{0}} (f : V ⟶ Y) [Surjective f], (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) → ∀ W : Y.Opens,
      Conn R F c (sch.map (f ⁻¹ᵁ W).ι) → (∀ (Z : Scheme.{0}) (g : Z ⟶ Y), (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ Z), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : Z, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ g)) → Conn R F (c - 1) (sch.map (g ⁻¹ᵁ W).ι)) → Conn R F c (sch.map W.ι) := by
  intro hL a1 a2 R _ F c V Y f _ hcov W h0 hp
  obtain ⟨ψ, hψ, hlev⟩ := UpperTheory.cech_nerve_restrict_open f W
  have hsm : Smooth f := smooth_of_cover f hcov
  have hsmW : Smooth (f ∣_ W) := MorphismProperty.of_isPullback (P := @Smooth) (isPullback_morphismRestrict f W).flip hsm
  have hsuW : Surjective (f ∣_ W) := MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict f W).flip inferInstance
  have eV := a2 R f F
  have eW := a2 R (f ∣_ W) F
  have hψc : Conn R F c ψ := by
    refine hL a1 R F c ψ fun p => ?_
    rcases p with _ | p
    · obtain ⟨e, he⟩ := cech_zero f
      obtain ⟨e', he'⟩ := hlev 0 V f e he
      have h0' : Conn R F (c - ((0 : ℕ) : ℤ)) (sch.map (f ⁻¹ᵁ W).ι) := by simpa using h0
      exact conn_level _ _ e e' he' h0'
    · obtain ⟨Z, g, e, hg, hc⟩ := UpperTheory.cech_nerve_representable_disjoint f hcov (p + 1)
      obtain ⟨e', he'⟩ := hlev (p + 1) Z g e hg
      exact conn_level _ _ e e' he' (conn_mono (by push_cast; omega) (hp Z g hc))
  exact conn_square hψ eW eV hψc

end
