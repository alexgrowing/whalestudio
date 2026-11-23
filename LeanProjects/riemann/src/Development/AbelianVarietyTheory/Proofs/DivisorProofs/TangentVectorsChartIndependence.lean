import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanDescent

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem dualMapR_comp_dualMapR {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMapR g).comp (dualMapR f) = dualMapR (g.comp f) := by
  apply RingHom.ext; intro x; ext <;> simp [dualMapR]

theorem dualMapR_comp_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (dualMapR f).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp f := by
  apply RingHom.ext; intro x; ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMapR {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualMapR f) = f.comp (TrivSqZeroExt.fstHom A A A).toRingHom := by
  apply RingHom.ext; intro x; simp [dualMapR]

theorem dualMapR_comp_epsMul {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    (dualMapR f).comp (epsMul a) = (epsMul (f a)).comp (dualMapR f) := by
  apply RingHom.ext; intro x; ext <;> simp [dualMapR, epsMul, _root_.mul_comm]

theorem epsMul_comp_alg {A : Type} [CommRing A] (a : A) :
    (epsMul a).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  apply RingHom.ext; intro x; ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem epi_of_local {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (d : A →+* B)
    [IsLocalHom d] (hd : Function.Injective d) : Epi (spMap d) := by
  refine ⟨fun {X} a b h => ?_⟩
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective b
  have h1 : IsLocalHom (f ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d f.hom
  have h2 : IsLocalHom (g ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d g.hom
  have h3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, _, h1⟩ =
      (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, _, h2⟩ := by
    simpa [SpecToEquivOfLocalRing] using h
  have h4 := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.injective h3
  obtain rfl : x = y := congrArg Sigma.fst h4
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj h4).2)
  obtain rfl : f = g := by
    ext s
    exact hd (congrArg (fun k => k.hom s) h5)
  rfl

theorem epi_dualMapR {K L : Type} [Field K] [Field L] (φ : K →+* L) : Epi (spMap (dualMapR φ)) := by
  have : IsLocalHom (dualMapR φ) := ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero] at ha ⊢
    intro h
    exact ha (by simp [dualMapR, h])⟩
  refine epi_of_local _ fun a b h => ?_
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  ext
  · exact φ.injective (by simpa [dualMapR] using h1)
  · exact φ.injective (by simpa [dualMapR] using h2)

theorem epi_spMap_field {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  haveI : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (show Module.Flat K L from inferInstance)
  haveI : Surjective (spMap f) := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem mem_range_of_fixed {K : Type} [Field K] (ι : K →+* GlobalTheory.ShFam.Pad.Qb) (a : GlobalTheory.ShFam.Pad.Qb)
    (h : ∀ σ : GlobalTheory.ShFam.Pad.Qb →+* GlobalTheory.ShFam.Pad.Qb, (∀ k, σ (ι k) = ι k) → σ a = a) : a ∈ Set.range ι := by
  letI : Algebra K GlobalTheory.ShFam.Pad.Qb := ι.toAlgebra
  haveI : CharZero K := RingHom.charZero ι
  haveI hQ : IsAlgClosure ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgClosure ℚ ℂ
  haveI : IsAlgClosed GlobalTheory.ShFam.Pad.Qb := hQ.isAlgClosed
  haveI : IsScalarTower ℚ K GlobalTheory.ShFam.Pad.Qb := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap ℚ GlobalTheory.ShFam.Pad.Qb x = ι (algebraMap ℚ K x)
    simp [eq_ratCast, map_ratCast]
  haveI : Algebra.IsAlgebraic ℚ GlobalTheory.ShFam.Pad.Qb := hQ.isAlgebraic
  haveI : Algebra.IsAlgebraic K GlobalTheory.ShFam.Pad.Qb := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K GlobalTheory.ShFam.Pad.Qb := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K GlobalTheory.ShFam.Pad.Qb := inferInstance
  obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) a).2 fun σ =>
    h σ.toRingEquiv.toRingHom fun k => σ.commutes k
  exact ⟨k, hk⟩

section Tangent

open MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem comp_listProd {B : Scheme.{0}} {G : Over B} [MonObj G] {X Y : Over B} (e : X ⟶ Y) (L : List (Y ⟶ G)) :
    e ≫ L.prod = (L.map (e ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one e
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem one_bc {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x0 : Sp A ⟶ X0) :
    spMap f ≫ (1 : Over.mk x0 ⟶ t.G).left = (1 : Over.mk (spMap f ≫ x0) ⟶ t.G).left := by
  let e : Over.mk (spMap f ≫ x0) ⟶ Over.mk x0 := Over.homMk (spMap f) rfl
  show (e ≫ (1 : Over.mk x0 ⟶ t.G)).left = _
  rw [MonObj.comp_one]

theorem isTan_bc {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x0 : Sp A ⟶ X0}
    {v : Sp (DualNumber A) ⟶ t.G.left} (h : IsTanAtG t x0 v) :
    IsTanAtG t (spMap f ≫ x0) (spMap (dualMapR f) ≫ v) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, sp_comp, dualMapR_comp_alg, ← sp_comp, Category.assoc]
  · rw [← Category.assoc, sp_comp, fst_comp_dualMapR, ← sp_comp, Category.assoc, h2, one_bc]

theorem isTan_desc {K L : Type} [Field K] [Field L] (f : K →+* L) {x0 : Sp K ⟶ X0}
    {v : Sp (DualNumber K) ⟶ t.G.left} (h : IsTanAtG t (spMap f ≫ x0) (spMap (dualMapR f) ≫ v)) :
    IsTanAtG t x0 v := by
  obtain ⟨h1, h2⟩ := h
  haveI := epi_dualMapR f
  haveI := epi_spMap_field f
  refine ⟨?_, ?_⟩
  · apply (cancel_epi (spMap (dualMapR f))).1
    rw [← Category.assoc, h1, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, dualMapR_comp_alg]
  · apply (cancel_epi (spMap f)).1
    rw [← Category.assoc, sp_comp, ← fst_comp_dualMapR, ← sp_comp, Category.assoc, h2, one_bc]

theorem comb_bc {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
    {x : Sp S ⟶ X0} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMapR ψ) ≫ v j) (fun j => ψ (a j))
      (spMap (dualMapR ψ) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  have he : spMap (dualMapR ψ) ≫ (tEpsG x).hom = (tEpsG (spMap ψ ≫ x)).hom := by
    show spMap (dualMapR ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, dualMapR_comp_alg]
  let e : tEpsG (spMap ψ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMapR ψ)) he
  refine ⟨fun i => e ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMapR ψ) ≫ (u i).left = spMap (epsMul (ψ (a i))) ≫ spMap (dualMapR ψ) ≫ v i
    rw [hu i, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, dualMapR_comp_epsMul]
  · have hl : (List.ofFn fun i => e ≫ u i) = (List.ofFn u).map (e ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [hl, ← comp_listProd, Over.comp_left, hw]
    rfl

theorem comb_eq {S : Type} [CommRing S] {x : Sp S ⟶ X0} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    {c : Fin m → S} {w w' : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v c w) (h' : IsCombAtG t x v c w') :
    w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [this]

theorem comb_exists {S : Type} [CommRing S] {x : Sp S ⟶ X0} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hv : ∀ j, IsTanAtG t x (v j)) (c : Fin m → S) : ∃ w, IsCombAtG t x v c w := by
  let u : Fin m → (tEpsG x ⟶ t.G) := fun i => Over.homMk (spMap (epsMul (c i)) ≫ v i) (by
    show (spMap (epsMul (c i)) ≫ v i) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [Category.assoc, (hv i).1, ← Category.assoc, sp_comp, epsMul_comp_alg])
  exact ⟨((List.ofFn u).prod).left, u, fun i => rfl, rfl⟩

end Tangent

theorem basis_descent : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}} (t : ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H X0) {K : Type} [Field K] (ι : K →+* Qb) (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ X0) {m : ℕ} (uK : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ t.G.left)), (∀ j, Formalism.L2.Pj.IsTanAtG t (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ x0) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ uK j)) → (∀ w, Formalism.L2.Pj.IsTanAtG t (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ x0) w → ∃! a : Fin m → Qb, Formalism.L2.Pj.IsCombAtG t (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ x0) (fun j => ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ uK j) a w) → (∀ j, Formalism.L2.Pj.IsTanAtG t x0 (uK j)) ∧ ∀ w, Formalism.L2.Pj.IsTanAtG t x0 w → ∃! c : Fin m → K, Formalism.L2.Pj.IsCombAtG t x0 uK c w := by
  intro E _ _ _ H X0 t K _ ι x0 m uK hT hU
  have hTK : ∀ j, IsTanAtG t x0 (uK j) := fun j => isTan_desc t ι (hT j)
  refine ⟨hTK, fun w hw => ?_⟩
  obtain ⟨a, ha, huniq⟩ := hU _ (isTan_bc t ι hw)
  have hfix : ∀ j, a j ∈ Set.range ι := fun j => mem_range_of_fixed ι (a j) fun σ hσ => by
    have hσι : σ.comp ι = ι := RingHom.ext hσ
    have h1 := comb_bc t σ ha
    have e1 : spMap σ ≫ spMap ι ≫ x0 = spMap ι ≫ x0 := by rw [← Category.assoc, sp_comp, hσι]
    have e2 : ∀ z : Sp (DualNumber K) ⟶ t.G.left,
        spMap (dualMapR σ) ≫ spMap (dualMapR ι) ≫ z = spMap (dualMapR ι) ≫ z := fun z => by
      rw [← Category.assoc, sp_comp, dualMapR_comp_dualMapR, hσι]
    simp only [e2] at h1
    rw [e1] at h1
    exact congrFun (huniq _ h1) j
  choose c hc using hfix
  obtain ⟨w0, hw0⟩ := comb_exists t hTK c
  have hb := comb_bc t ι hw0
  have hac : (fun j => ι (c j)) = a := funext hc
  rw [hac] at hb
  haveI := epi_dualMapR ι
  have hw0w : w0 = w := (cancel_epi (spMap (dualMapR ι))).1 (comb_eq t hb ha)
  refine ⟨c, hw0w ▸ hw0, fun c' hc' => ?_⟩
  have h' := huniq _ (comb_bc t ι hc')
  funext j
  apply ι.injective
  exact (congrFun h' j).trans (hc j).symm

end GlobalTheory.TanDescent
