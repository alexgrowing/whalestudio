import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

namespace TorsionRat

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_epi {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    letI := i.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (inferInstance : Module.Flat K L)
  have : Surjective (spMap i) := ⟨fun x => ⟨(⊥ : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_finset_of_field {K F : Type} [Field K] [Field F] [Algebra K F] {Y : Scheme.{0}} (s : Y ⟶ Sp K)
    [LocallyOfFiniteType s] (p : Sp F ⟶ Y) (hp : p ≫ s = spMap (algebraMap K F)) :
    ∃ S : Finset F, ∀ L : IntermediateField K F, (S : Set F) ⊆ L →
      ∃ q : Sp L ⟶ Y, spMap (algebraMap L F) ≫ q = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint F))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(Y, U) ⟶ CommRingCat.of F, Spec.map f ≫ hU.fromSpec = p := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum F) y (IsLocalRing.closedPoint F)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of K ⟶ Γ(Y, U), Spec.map g = hU.fromSpec ≫ s :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap K F) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf]
      exact hp)
  have hV : ∀ r : K, f.hom (g.hom r) = algebraMap K F r := fun r => congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra K Γ(Y, U) := g.hom.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType K Γ(Y, U) from hft).out
  refine ⟨t.image f.hom, fun L hL => ?_⟩
  have hr : ∀ a, f.hom a ∈ L := fun a => by
    have ha : a ∈ Algebra.adjoin K (t : Set Γ(Y, U)) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hL (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ L.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(Y, U) ⟶ CommRingCat.of L := CommRingCat.ofHom (f.hom.codRestrict L hr)
  refine ⟨Spec.map f' ≫ hU.fromSpec, ?_⟩
  change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
  rw [← hf, ← Spec.map_comp_assoc]
  rfl

theorem exists_finset_over {K F : Type} [Field K] [Field F] [Algebra K F] {X : Scheme.{0}} (G : Over X)
    [LocallyOfFiniteType G.hom] (x : Sp K ⟶ X) (p : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ G) :
    ∃ S : Finset F, ∀ L : IntermediateField K F, (S : Set F) ⊆ L →
      ∃ q : Over.mk (spMap (algebraMap K L) ≫ x) ⟶ G, spMap (algebraMap L F) ≫ q.left = p.left := by
  obtain ⟨S, hS⟩ := exists_finset_of_field (pullback.snd G.hom x)
    (pullback.lift p.left (spMap (algebraMap K F)) (Over.w p)) (pullback.lift_snd _ _ _)
  refine ⟨S, fun L hL => ?_⟩
  obtain ⟨q, hq⟩ := hS L hL
  have h1 : spMap (algebraMap L F) ≫ q ≫ pullback.fst G.hom x = p.left := by
    rw [← Category.assoc, hq]; exact pullback.lift_fst _ _ _
  refine ⟨Over.homMk (q ≫ pullback.fst G.hom x) ?_, h1⟩
  haveI := sp_epi (algebraMap L F)
  rw [← cancel_epi (spMap (algebraMap L F))]
  change spMap (algebraMap L F) ≫ (q ≫ pullback.fst G.hom x) ≫ G.hom =
    spMap (algebraMap L F) ≫ spMap (algebraMap K L) ≫ x
  rw [← Category.assoc, h1, ← Category.assoc, sp_comp]
  exact Over.w p

theorem comp_injective {X : Scheme.{0}} {G : Over X} {K L : Type} [Field K] [Field L] {x : Sp K ⟶ X} {y : Sp L ⟶ X}
    (ψ : K →+* L) (g : Over.mk y ⟶ Over.mk x) (hg : g.left = spMap ψ) {a b : Over.mk x ⟶ G}
    (h : g ≫ a = g ≫ b) : a = b := by
  haveI := sp_epi ψ
  have h' : spMap ψ ≫ a.left = spMap ψ ≫ b.left := hg ▸ congrArg CommaMorphism.left h
  exact Over.OverMorphism.ext ((cancel_epi _).1 h')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_level_of_isAlgClosed (Xo : Moduli Dw l) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X)
    {M : ℕ} (hM : 0 < M) :
    ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧
      (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧
      ∀ w : ptO Xo x ⟶ Xo.univ.t.G, w ^ M = 1 ↔ ∃ a, ev a = w := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ Xo.s)
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x β.hom hβ.symm
  exact ⟨I.ev M, I.add M, I.lin M, I.ker M hM, I.onto M hM⟩

theorem exists_enum (Xo : Moduli Dw l) {M : ℕ} (hM : 0 < M) :
    ∃ (J : Type) (_ : Finite J), ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X),
      ∃ u : J → (ptO Xo x ⟶ Xo.univ.t.G), Function.Injective u ∧ ∀ w, w ^ M = 1 ↔ ∃ j, u j = w := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient Dw M hM
  refine ⟨J, inferInstance, fun K _ _ x => ?_⟩
  obtain ⟨ev, hadd, -, hker, honto⟩ := exists_level_of_isAlgClosed Xo x hM
  have hI : ∀ a b, ev a = ev b ↔ π a = π b := fun a b => by
    have h : ev a = ev (a - b) * ev b := by rw [← hadd, sub_add_cancel]
    rw [hπ, h, mul_eq_right, hker]
  refine ⟨fun j => ev (r j), fun i j hij => ?_, fun w => (honto w).trans ⟨?_, ?_⟩⟩
  · have := (hI _ _).1 hij
    rwa [hr, hr] at this
  · rintro ⟨a, rfl⟩
    exact ⟨π a, (hI _ _).2 (hr _)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, rfl⟩

theorem exists_eq_comp_of_isAlgClosed (Xo : Moduli Dw l) {M : ℕ} (hM : 0 < M) {K L : Type} [Field K] [Field L]
    [IsAlgClosed K] [IsAlgClosed L] {x : Sp K ⟶ Xo.X} {y : Sp L ⟶ Xo.X} (ψ : K →+* L) (g : ptO Xo y ⟶ ptO Xo x)
    (hg : g.left = spMap ψ) (w : ptO Xo y ⟶ Xo.univ.t.G) (hw : w ^ M = 1) :
    ∃ a : ptO Xo x ⟶ Xo.univ.t.G, a ^ M = 1 ∧ g ≫ a = w := by
  obtain ⟨J, _, hJ⟩ := exists_enum Xo hM
  obtain ⟨u, hu, hu'⟩ := hJ K x
  obtain ⟨v, -, hv'⟩ := hJ L y
  have hp : ∀ j, u j ^ M = 1 := fun j => (hu' _).2 ⟨j, rfl⟩
  choose τ hτ using fun j => (hv' (g ≫ u j)).1 (by rw [← MonObj.comp_pow, hp, MonObj.comp_one])
  have hτi : Function.Injective τ := fun i j hij =>
    hu (comp_injective ψ g hg (by rw [← hτ, ← hτ, hij]))
  obtain ⟨j, rfl⟩ := (hv' w).1 hw
  obtain ⟨i, rfl⟩ := Finite.surjective_of_injective hτi j
  exact ⟨u i, hp i, (hτ i).symm⟩

theorem allRat_of_isAlgClosure (Xo : Moduli Dw l) {M : ℕ} (hM : 0 < M) {L F : Type} [Field L] [Field F] [Algebra L F]
    [IsAlgClosed F] [Algebra.IsAlgebraic L F] (x : Sp L ⟶ Xo.X) (y : Sp F ⟶ Xo.X)
    (hy : spMap (algebraMap L F) ≫ x = y)
    (h : ∀ w : ptO Xo y ⟶ Xo.univ.t.G, w ^ M = 1 →
      ∃ a : ptO Xo x ⟶ Xo.univ.t.G, spMap (algebraMap L F) ≫ a.left = w.left) : AllRat Xo x M := by
  intro Ω _ ψ w hw
  let Ω' := AlgebraicClosure Ω
  let i : Ω →+* Ω' := algebraMap Ω Ω'
  letI : Algebra L Ω' := (i.comp ψ).toAlgebra
  let σ : F →ₐ[L] Ω' := IsAlgClosed.lift
  have hσ : (σ : F →+* Ω').comp (algebraMap L F) = i.comp ψ := σ.comp_algebraMap
  let g₁ : ptO Xo (spMap i ≫ spMap ψ ≫ x) ⟶ ptO Xo (spMap ψ ≫ x) := Over.homMk (spMap i) rfl
  let g₂ : ptO Xo (spMap i ≫ spMap ψ ≫ x) ⟶ ptO Xo y := Over.homMk (spMap (σ : F →+* Ω')) (by
    change spMap (σ : F →+* Ω') ≫ y = spMap i ≫ spMap ψ ≫ x
    rw [← hy, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, hσ])
  obtain ⟨b, hb, hb'⟩ := exists_eq_comp_of_isAlgClosed Xo hM (σ : F →+* Ω') g₂ rfl (g₁ ≫ w)
    (by rw [← MonObj.comp_pow, hw, MonObj.comp_one])
  obtain ⟨a, ha⟩ := h b hb
  refine ⟨a, ?_⟩
  haveI := sp_epi i
  have h1 : spMap (σ : F →+* Ω') ≫ b.left = spMap i ≫ w.left := congrArg CommaMorphism.left hb'
  refine (cancel_epi (spMap i)).1 (h1.symm.trans ?_)
  rw [← ha, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, hσ]

theorem exists_finite_allRat (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) {M : ℕ} (hM : 0 < M) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧
      AllRat Xo (spMap (algebraMap K L) ≫ x) M := by
  let F := AlgebraicClosure K
  haveI := Xo.univ.proper
  obtain ⟨J, _, hJ⟩ := exists_enum Xo hM
  obtain ⟨u, -, hu⟩ := hJ F (spMap (algebraMap K F) ≫ x)
  choose S hS using fun j => exists_finset_over Xo.univ.t.G x (u j)
  let s : Set F := ⋃ j, (S j : Set F)
  haveI : Finite s := (Set.finite_iUnion fun j => (S j).finite_toSet).to_subtype
  let L := IntermediateField.adjoin K s
  refine ⟨L, inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  refine allRat_of_isAlgClosure Xo hM (F := F) _ (spMap (algebraMap K F) ≫ x) ?_ fun w hw => ?_
  · rw [← Category.assoc, sp_comp]
    rfl
  · obtain ⟨j, rfl⟩ := (hu w).1 hw
    exact hS j L ((Set.subset_iUnion (fun j => (S j : Set F)) j).trans (IntermediateField.subset_adjoin _ _))

theorem allRat_baseChange (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {M : ℕ} (h : AllRat Xo x M)
    (L : Type) [Field L] (ψ : K →+* L) : AllRat Xo (spMap ψ ≫ x) M := by
  have key : ∀ (Ω : Type) [Field Ω] (ψ : K →+* Ω) (y : Sp Ω ⟶ Xo.X), y = spMap ψ ≫ x →
      ∀ w : ptO Xo y ⟶ Xo.univ.t.G, w ^ M = 1 → ∃ a : ptO Xo x ⟶ Xo.univ.t.G, w.left = spMap ψ ≫ a.left := by
    intro Ω _ ψ y hy
    subst hy
    exact h Ω ψ
  intro Ω _ χ w hw
  obtain ⟨a, ha⟩ := key Ω (χ.comp ψ) _ (by rw [← Category.assoc, sp_comp]) w hw
  let g' : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
  have h1 : (g' ≫ a).left = spMap ψ ≫ a.left := rfl
  refine ⟨g' ≫ a, ha.trans ?_⟩
  exact (congrArg (· ≫ a.left) (sp_comp ψ χ).symm).trans
    ((Category.assoc _ _ _).trans (congrArg (spMap χ ≫ ·) h1.symm))

theorem exists_level_of_allRat (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {M : ℕ} (hM : 0 < M)
    (h : AllRat Xo x M) :
    ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧
      (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧
      ∀ w : ptO Xo x ⟶ Xo.univ.t.G, w ^ M = 1 → ∃ a, ev a = w := by
  let F := AlgebraicClosure K
  let ψ : K →+* F := algebraMap K F
  let g : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
  have inj : ∀ {a b : ptO Xo x ⟶ Xo.univ.t.G}, g ≫ a = g ≫ b → a = b := fun h => comp_injective ψ g rfl h
  obtain ⟨ev, hadd, hlin, hker, honto⟩ := exists_level_of_isAlgClosed Xo (spMap ψ ≫ x) hM
  choose e he using fun a => h F ψ (ev a) ((honto _).2 ⟨a, rfl⟩)
  have he' : ∀ a, g ≫ e a = ev a := fun a => Over.OverMorphism.ext (he a).symm
  refine ⟨e, fun a b => inj ?_, fun o a => inj ?_, fun a => ?_, fun w hw => ?_⟩
  · rw [MonObj.comp_mul, he', he', he', hadd]
  · rw [← Category.assoc, he', he', hlin]
  · rw [← hker, ← he']
    exact ⟨fun h1 => by rw [h1, MonObj.comp_one], fun h1 => inj (by rw [h1, MonObj.comp_one])⟩
  · obtain ⟨a, ha⟩ := (honto (g ≫ w)).1 (by rw [← MonObj.comp_pow, hw, MonObj.comp_one])
    exact ⟨a, inj ((he' a).trans ha)⟩

end TorsionRat

open TorsionRat in

theorem torsion_rational_over_finite_extension :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ), 0 < M → (∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ AllRat Xo (spMap (algebraMap K L) ≫ x) M) ∧ (AllRat Xo x M → (∀ (L : Type) [Field L] (ψ : K →+* L), AllRat Xo (spMap ψ ≫ x) M) ∧ ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧ ∀ w : (ptO Xo x ⟶ Xo.univ.t.G), w ^ M = 1 → ∃ a, ev a = w) :=
  fun _ _ _ _ _ _ _ Xo _ _ x _ hM =>
    ⟨exists_finite_allRat Xo x hM, fun h => ⟨fun L _ ψ => allRat_baseChange Xo h L ψ, exists_level_of_allRat Xo hM h⟩⟩

end GlobalTheory
