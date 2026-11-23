import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateLatticeLeOmegaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroupStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeTateFunctionalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquivStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongOrderDividesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongGroupPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongUniqueUpToIsoStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HTPull

theorem dual_sq {A B : Type} [CommRing A] [CommRing B] (c : A →+* B) :
    (dualMap c).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp c := by
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    (dualMap d).comp (dualMap c) = dualMap (d.comp c) := by
  ext r <;> simp [dualMap]

theorem lieBC {S : Scheme.{0}} {G : Over S} [GrpObj G] {A B : Type} [CommRing A] [CommRing B] (c : A →+* B)
    (x : Sp A ⟶ S) (y : Sp B ⟶ S) (hy : y = Spec.map (CommRingCat.ofHom c) ≫ x) (hsm : Smooth G.hom)
    {E E' : Type} [AddCommGroup E] [Module A E] [AddCommGroup E'] [Module B E']
    (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) ∧
      (∀ (a : A) e, j (a • e) = c a • j e) ∧ Submodule.span B (Set.range j) = ⊤ ∧
      ∀ l : Module.Dual A E, ∃ l' : Module.Dual B E', ∀ e, l' (j e) = c (l e) := by
  subst hy
  letI : Algebra A B := c.toAlgebra
  letI : Module A E' := Module.compHom E' c
  haveI : IsScalarTower A B E' := ⟨fun a b e => by
    show (c a * b) • e = c a • b • e
    rw [mul_smul]⟩
  haveI : Smooth G.hom := hsm
  obtain ⟨j, h1, h2, -⟩ := GlobalTheory.T.lie_model_base_change_map S G A B x E E' M M'
  let β : E →ₗ[A] E' := { toFun := j, map_add' := map_add j, map_smul' := fun a e => h2 a e }
  have hbc : IsBaseChange B β := (GlobalTheory.T.lie_model_finite_base_change S G A x E M).2.2 B E' M' β h1
  refine ⟨j, h1, h2, ?_, ?_⟩
  · refine eq_top_iff.2 fun e _ => ?_
    refine hbc.inductionOn e (fun z => z ∈ Submodule.span B (Set.range j)) (Submodule.zero_mem _) ?_ ?_ ?_
    · exact fun m => Submodule.subset_span ⟨m, rfl⟩
    · exact fun s n h => Submodule.smul_mem _ s h
    · exact fun a b ha hb => Submodule.add_mem _ ha hb
  · intro l
    refine ⟨hbc.lift ((Algebra.linearMap A B).comp l), fun e => ?_⟩
    exact hbc.lift_eq _ e

theorem isHT_move {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (hφ : IsPullback φ G'.hom G.hom f) {x' : Sp R ⟶ S'} {y : Sp R ⟶ S} {i₁ : Γ.G.left ⟶ G.left}
    {i' : Γ.G.left ⟶ G'.left} (hi' : i' ≫ φ = i₁) (hover : i' ≫ G'.hom = Γ.G.hom ≫ x') {L : Type} [AddCommGroup L]
    [Module R L] {Ma : LieModel G y L} {Mb : LieModel G' x' L} (h : ∀ e, (Mb.pt e).left ≫ φ = (Ma.pt e).left)
    {N : ℕ} {χ : T →* Rˣ} {w : Module.Dual R L} (H : Γ.IsHT i₁ Ma N χ w) : Γ.IsHT i' Mb N χ w := by
  obtain ⟨s, hs, hv⟩ := H
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := hv e
  refine ⟨v, h1, ?_, h3⟩
  refine hφ.hom_ext ?_ ?_
  · rw [Category.assoc, hi', h2, Category.assoc, h]
  · have w₁ := Over.w (Mb.pt e)
    rw [Category.assoc, hover, ← Category.assoc, h1, Category.assoc, w₁]
    show _ = _ ≫ Spec.map _ ≫ x'
    rw [← Category.assoc _ _ x', ← Spec.map_comp, ← CommRingCat.ofHom_comp, dual_sq]

theorem isHT_lie {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {i : Γ.G.left ⟶ G.left} {L₁ L₂ : Type} [AddCommGroup L₁]
    [Module R L₁] [AddCommGroup L₂] [Module R L₂] {M₁ : LieModel G x L₁} {M₂ : LieModel G x L₂} (g : L₁ ≃ₗ[R] L₂)
    (hg : ∀ e, M₂.pt (g e) = M₁.pt e) {N : ℕ} {χ : T →* Rˣ} {w : Module.Dual R L₂} (H : Γ.IsHT i M₂ N χ w) :
    Γ.IsHT i M₁ N χ (w.comp g.toLinearMap) := by
  obtain ⟨s, hs, hv⟩ := H
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := hv (g e)
  exact ⟨v, h1, by rw [h2, hg], h3⟩

theorem char_descends {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] (s : R →+* R')
    (hs : Function.Injective s) {T : Type} [CommGroup T] {N : ℕ} (hN : 0 < N) {z : R} (hz : IsPrimitiveRoot z N)
    (hT : ∀ t : T, t ^ N = 1) (χ' : T →* R'ˣ) :
    ∃ χ : T →* Rˣ, (Units.map (s : R →* R')).comp χ = χ' := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hz' : IsPrimitiveRoot (s z) N := hz.map_of_injective hs
  let zu : Rˣ := (hz.isUnit hN.ne').unit
  have hinj : Function.Injective (Units.map (s : R →* R')) := Units.map_injective hs
  have ex : ∀ t, ∃ u : Rˣ, Units.map (s : R →* R') u = χ' t := fun t => by
    have e : ((χ' t : R'ˣ) : R') ^ N = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hT t, map_one, Units.val_one]
    obtain ⟨m, -, hm⟩ := hz'.eq_pow_of_pow_eq_one e
    refine ⟨zu ^ m, Units.ext ?_⟩
    simpa [zu] using hm
  choose c hc using ex
  refine ⟨MonoidHom.mk' c fun a b => hinj (by rw [map_mul, hc, hc, hc, map_mul]), ?_⟩
  ext t
  simp [hc]

theorem core {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
    (hs : Function.Injective (algebraMap R R')) {X X' : Scheme.{0}} (x : Sp R ⟶ X) (x' : Sp R' ⟶ X') (f : X' ⟶ X)
    (hx : x' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x)
    {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] (φ : G'.left ⟶ G.left)
    (hφ : IsGrpPullback G' G f φ) (hsm : Smooth G.hom) {T : Type} [CommGroup T] [Finite T] (Γ : BT.QFGroup R T)
    (N : ℕ) (i : Γ.G.left ⟶ G.left) (hi : Γ.IsTorsionAlong G x N i)
    {L L' : Type} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R' L']
    (M₀ : LieModel G x L) (M₀' : LieModel G' x' L') :
    ∃ (Γ' : BT.QFGroup R' T) (i' : Γ'.G.left ⟶ G'.left) (β : L →+ L'), Γ'.IsTorsionAlong G' x' N i' ∧
      (∀ e, (M₀'.pt (β e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M₀.pt e).left) ∧
      Submodule.span R' (Set.range β) = ⊤ ∧
      (∀ l : Module.Dual R L, ∃ l' : Module.Dual R' L', ∀ e, l' (β e) = algebraMap R R' (l e)) ∧
      ∀ (χ : T →* Rˣ) (w₀ : Module.Dual R L) (w₀' : Module.Dual R' L'), (∀ e, w₀' (β e) = algebraMap R R' (w₀ e)) →
        Γ.IsHT i M₀ N χ w₀ → Γ'.IsHT i' M₀' N ((Units.map (algebraMap R R' : R →* R')).comp χ) w₀' := by
  obtain ⟨Γ', F, hF⟩ := GlobalTheory.T.exists_base_change_group R T Γ R' (algebraMap R R') hs
  have tor₁ := GlobalTheory.T.torsion_along_base_change R T Γ X G x N i hi R' (algebraMap R R') Γ' F hF
  obtain ⟨i', hi', tor'⟩ := GlobalTheory.T.torsion_along_group_pullback R' T Γ' X X' G G' f φ x' _ N (F ≫ i) hφ hx tor₁
  have key : ∀ y : Sp R' ⟶ X, x' ≫ f = y → ∃ M₂ : LieModel G y L', ∀ e, (M₀'.pt e).left ≫ φ = (M₂.pt e).left := by
    rintro _ rfl
    exact ⟨LieMove.pushModel hφ M₀', fun _ => rfl⟩
  obtain ⟨M₂, hM₂⟩ := key _ hx
  obtain ⟨β, hβ, -, hsp, hext⟩ := lieBC (algebraMap R R') x _ rfl hsm M₀ M₂
  refine ⟨Γ', i', β, tor', fun e => ?_, hsp, hext, fun χ w₀ w₀' hw H => ?_⟩
  · rw [hM₂, hβ]
  · have H' := GlobalTheory.T.hodge_tate_functional_base_change R T Γ X G x N i hi L M₀ R' Γ' F hF tor₁ L' M₂ β hβ hsp χ w₀ w₀' hw H
    exact isHT_move Γ' hφ.1 hi' tor'.isOver hM₂ H'

section Setup

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
  {X X' : Scheme.{0}} {x : Sp R ⟶ X} {x' : Sp R' ⟶ X'} {f : X' ⟶ X}
  {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}
  {Ω Ω' : Type} [Field Ω] [Field Ω'] {k : R →+* Ω} {k' : R' →+* Ω'} {i : Ω →+* Ω'}
  {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
  {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {j : V →+ V'}

theorem tan_eq (hφ : IsGrpPullback G' G f φ) {a b : V'}
    (h : (M'.pt a).left ≫ φ = (M'.pt b).left ≫ φ) : a = b := by
  refine M'.inj (Over.OverMorphism.ext (hφ.1.hom_ext h ?_))
  exact (Over.w (M'.pt a)).trans (Over.w (M'.pt b)).symm

theorem j_comm (hφ : IsGrpPullback G' G f φ) (hk : ∀ r, k' (algebraMap R R' r) = i (k r))
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    {L L' : Type} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R' L']
    {M₀ : LieModel G x L} {M₀' : LieModel G' x' L'} {β : L →+ L'}
    (hβ : ∀ e, (M₀'.pt (β e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M₀.pt e).left)
    {j₀ : L → V} (hj₀ : ∀ e, (M.pt (j₀ e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    {j' : L' → V'} (hj' : ∀ e, (M'.pt (j' e)).left = Spec.map (CommRingCat.ofHom (dualMap k')) ≫ (M₀'.pt e).left)
    (l : L) : j' (β l) = j (j₀ l) := by
  refine tan_eq (M' := M') hφ ?_
  rw [hj, hj₀, hj', Category.assoc, hβ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, dualMap_comp, dualMap_comp]
  have e : k'.comp (algebraMap R R') = i.comp k := RingHom.ext hk
  rw [e]

theorem form_eq (hk : ∀ r, k' (algebraMap R R' r) = i (k r))
    {L L' : Type} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R' L'] {β : L →+ L'}
    (hsp : Submodule.span R' (Set.range β) = ⊤) {j₀ : L → V} {j' : L' →+ V'}
    (hjs : ∀ (a : R') e, j' (a • e) = k' a • j' e) (hjj : ∀ l, j' (β l) = j (j₀ l))
    {w : Module.Dual Ω V} {w' : Module.Dual Ω' V'} (hww : ∀ e, w' (j e) = i (w e))
    {w₀ : Module.Dual R L} {w₀' : Module.Dual R' L'} (hw : ∀ l, w (j₀ l) = k (w₀ l))
    (hw₀ : ∀ l, w₀' (β l) = algebraMap R R' (w₀ l)) (e : L') : w' (j' e) = k' (w₀' e) := by
  have he : e ∈ Submodule.span R' (Set.range β) := by rw [hsp]; trivial
  induction he using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨l, rfl⟩ := h
    rw [hjj, hww, hw, hw₀, hk]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul a b _ hb => simp [hjs, hb]

theorem forward (hs : Function.Injective (algebraMap R R'))
    (hx : x' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x)
    (hφ : IsGrpPullback G' G f φ) (hsm : Smooth G.hom)
    (hk : ∀ r, k' (algebraMap R R' r) = i (k r)) (hξ' : ξ' = Spec.map (CommRingCat.ofHom k') ≫ x')
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    {N : ℕ} {w : Module.Dual Ω V} {w' : Module.Dual Ω' V'} (hww : ∀ e, w' (j e) = i (w e))
    (H : M.IsHTFormOver N x k w) : M'.IsHTFormOver N x' k' w' := by
  have hsm' : Smooth G'.hom := MorphismProperty.of_isPullback hφ.1 hsm
  obtain ⟨_, T, _, Γ, i₀, L, _, _, M₀, j₀, χ, w₀, tor, hj₀, hHT, hw⟩ := H
  haveI := GlobalTheory.T.quasi_finite_group_finite R T Γ
  obtain ⟨L', _, _, ⟨M₀'⟩⟩ := lieModel_exists X' G' R' x'
  obtain ⟨Γ', i', β, tor', hβ, hsp, hext, hcore⟩ := core hs x x' f hx φ hφ hsm Γ N i₀ tor M₀ M₀'
  obtain ⟨j', hj', hjs, -, -⟩ := lieBC k' x' ξ' hξ' hsm' M₀' M'
  obtain ⟨w₀', hw₀⟩ := hext w₀
  refine ⟨inferInstance, T, _, Γ', i', L', _, _, M₀', j', (Units.map (algebraMap R R' : R →* R')).comp χ, w₀', tor',
    hj', hcore χ w₀ w₀' hw₀ hHT, ?_⟩
  exact form_eq hk hsp hjs (j_comm hφ hk hj hβ hj₀ hj') hww hw hw₀

end Setup

section Back

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
  {X X' : Scheme.{0}} {x : Sp R ⟶ X} {x' : Sp R' ⟶ X'} {f : X' ⟶ X}
  {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}
  {Ω Ω' : Type} [Field Ω] [Field Ω'] {k : R →+* Ω} {k' : R' →+* Ω'} {i : Ω →+* Ω'}
  {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
  {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {j : V →+ V'}

theorem backward [IsIntegrallyClosed R] [IsNoetherianRing R] (hs : Function.Injective (algebraMap R R'))
    (hx : x' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x)
    (hφ : IsGrpPullback G' G f φ) (hsm : Smooth G.hom)
    (hk : ∀ r, k' (algebraMap R R' r) = i (k r)) (hξ : ξ = Spec.map (CommRingCat.ofHom k) ≫ x)
    (hξ' : ξ' = Spec.map (CommRingCat.ofHom k') ≫ x')
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    {N : ℕ} (hN : 0 < N) (hN0 : (N : R') ≠ 0) {z : R} (hz : IsPrimitiveRoot z N)
    (h0 : M.IsHTFormOver N x k 0)
    (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (hjd : ∀ w e, jd w (j e) = i (w e))
    {w' : Module.Dual Ω' V'} (H : M'.IsHTFormOver N x' k' w') :
    ∃ w, M.IsHTFormOver N x k w ∧ ∃ u' : Module.Dual Ω' V', w' = jd w + N • u' ∧
      ∀ (e : V') (v : epsAt x' ⟶ G'), IsTanAt G' x' v →
        (M'.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k')) ≫ v.left → u' e ∈ k'.range := by
  have hsm' : Smooth G'.hom := MorphismProperty.of_isPullback hφ.1 hsm
  obtain ⟨_, T, _, Γ, i₀, L, _, _, M₀, -, -, -, tor, -, -, -⟩ := h0
  haveI := GlobalTheory.T.quasi_finite_group_finite R T Γ
  obtain ⟨_, T₂, _, Γ₂, i₂, L₂, _, _, M₂, j₂, χ₂, w₂, tor₂, hj₂, hHT₂, hw₂⟩ := H
  obtain ⟨L', _, _, ⟨M₀'⟩⟩ := lieModel_exists X' G' R' x'
  obtain ⟨Γ', i', β, tor', hβ, hsp, hext, hcore⟩ := core hs x x' f hx φ hφ hsm Γ N i₀ tor M₀ M₀'
  obtain ⟨b, hb⟩ := GlobalTheory.T.torsion_along_unique_up_to_iso R' T₂ T Γ₂ Γ' X' G' x' N i₂ i' tor₂ tor'
  have H₁ := hb L₂ M₂ χ₂ w₂ hHT₂
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv X' G' R' x' L' L₂ M₀' M₂
  have H₂ := isHT_lie Γ' g hg H₁
  obtain ⟨χ, hχ⟩ := char_descends (algebraMap R R') hs hN hz (GlobalTheory.T.torsion_along_order_divides R T Γ X G x N i₀ tor)
    (χ₂.comp b.symm.toMonoidHom)
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.exists_hodge_tate_functional R T Γ X G x N i₀ tor hsm L M₀ χ
  obtain ⟨j₁, hj₁, -, -, hj₁ext⟩ := lieBC k x ξ hξ hsm M₀ M
  obtain ⟨w, hw⟩ := hj₁ext w₀
  obtain ⟨w₀', hw₀'⟩ := hext w₀
  have H₃ := hcore χ w₀ w₀' hw₀' hw₀
  rw [hχ] at H₃
  obtain ⟨u, hu⟩ := (GlobalTheory.T.hodge_tate_functional_unique_mod_smul R' T Γ' X' G' x' N i' tor' hsm' hN0 L' M₀' _ w₀' _ H₃).1 H₂
  obtain ⟨j', hj', hjs, hjsp, hjext⟩ := lieBC k' x' ξ' hξ' hsm' M₀' M'
  obtain ⟨u', hu'⟩ := hjext u
  refine ⟨w, ⟨inferInstance, T, _, Γ, i₀, L, _, _, M₀, j₁, χ, w₀, tor, hj₁, hw₀, hw⟩, u', ?_, ?_⟩
  · have hd := form_eq (w := w) (w' := jd w) hk hsp hjs (j_comm hφ hk hj hβ hj₁ hj') (hjd w) hw hw₀'
    refine LinearMap.ext_on hjsp ?_
    rintro _ ⟨e, rfl⟩
    have a1 : j₂ (g e) = j' e := M'.inj (Over.OverMorphism.ext (by rw [hj₂, hg, hj']))
    have a2 := hw₂ (g e)
    have a3 := LinearMap.congr_fun hu e
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smul_apply] at a3
    rw [a1, a3] at a2
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    rw [a2, hd, hu', map_add, map_nsmul]
  · intro e v hv he
    obtain ⟨l, rfl⟩ := M₀'.onto v hv
    have : e = j' l := M'.inj (Over.OverMorphism.ext (he.trans (hj' l).symm))
    subst this
    exact ⟨u l, (hu' l).symm⟩

end Back

theorem om_decomp {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {Ω Ω' : Type} [Field Ω] [Field Ω'] {k : R →+* Ω} {ξ : Sp Ω ⟶ X}
    {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] {M : LieModel G ξ V}
    (hξ : ξ = Spec.map (CommRingCat.ofHom k) ≫ x) (hsm : Smooth G.hom) (i : Ω →+* Ω') (j : V →+ V')
    (hjs : ∀ (a : Ω) e, j (a • e) = i a • j e) (hspan : Submodule.span Ω' (Set.range j) = ⊤)
    (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (hjd : ∀ w e, jd w (j e) = i (w e)) :
    ∃ (n : ℕ) (δ : Fin n → Module.Dual Ω V) (b : Fin n → V),
      (∀ a, ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧
        (M.pt (b a)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left) ∧
      (∀ a e (v : epsAt x ⟶ G), IsTanAt G x v →
        (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left → δ a e ∈ k.range) ∧
      ∀ u' : Module.Dual Ω' V', u' = ∑ a, u' (j (b a)) • jd (δ a) := by
  obtain ⟨L, _, _, ⟨M₀⟩⟩ := lieModel_exists X G R x
  haveI : Smooth G.hom := hsm
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_model_finite_base_change X G R x L M₀
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R L := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis R L
  obtain ⟨j₁, hj₁, hj₁s, hj₁sp, hj₁ext⟩ := lieBC k _ ξ hξ hsm M₀ M
  choose δ hδ using fun a => hj₁ext (b.coord a)
  refine ⟨_, δ, fun a => j₁ (b a), fun a => ⟨M₀.pt (b a), M₀.tan _, hj₁ _⟩, ?_, ?_⟩
  · intro a e v hv hev
    obtain ⟨l, rfl⟩ := M₀.onto v hv
    have : e = j₁ l := M.inj (Over.OverMorphism.ext (hev.trans (hj₁ l).symm))
    subst this
    rw [hδ]
    exact ⟨_, rfl⟩
  · intro u'
    obtain ⟨P, hP⟩ : ∃ P, P = u' - ∑ a, u' (j (j₁ (b a))) • jd (δ a) := ⟨_, rfl⟩
    have A0 : ∀ a', P (j (j₁ (b a'))) = 0 := by
      intro a'
      rw [hP, LinearMap.sub_apply, LinearMap.sum_apply, Finset.sum_eq_single a']
      · rw [LinearMap.smul_apply, hjd, hδ]
        simp
      · intro a _ hne
        rw [LinearMap.smul_apply, hjd, hδ]
        simp [Module.Basis.coord_apply, Finsupp.single_apply, hne.symm]
      · simp
    have A : ∀ l, P (j (j₁ l)) = 0 := fun l => by
      have hl : l ∈ Submodule.span R (Set.range b) := by
        rw [b.span_eq]; trivial
      induction hl using Submodule.span_induction with
      | mem _ h => obtain ⟨a, rfl⟩ := h; exact A0 a
      | zero => simp
      | add a b _ _ ha hb => simp [ha, hb]
      | smul r a _ ha => rw [hj₁s, hjs, map_smul, ha, smul_zero]
    have B : ∀ v, P (j v) = 0 := fun v => by
      have hv : v ∈ Submodule.span Ω (Set.range j₁) := by rw [hj₁sp]; trivial
      induction hv using Submodule.span_induction with
      | mem _ h => obtain ⟨a, rfl⟩ := h; exact A a
      | zero => simp
      | add a b _ _ ha hb => simp [ha, hb]
      | smul r a _ ha => rw [hjs, map_smul, ha, smul_zero]
    have C : P = 0 := LinearMap.ext_on hspan (by rintro _ ⟨v, rfl⟩; simpa using B v)
    rw [hP] at C
    exact sub_eq_zero.1 C

end GlobalTheory.CompanionTheory.Ar.HTPull

theorem GlobalTheory.CompanionTheory.Ar.HTPull.main : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → Smooth G.hom → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → ∀ (jd : Module.Dual Ω V →+ Module.Dual Ω' V'), (∀ w e, jd w (j e) = i (w e)) → ∀ (N : ℕ), 0 < N → ∀ (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), IsIntegrallyClosed (X.presheaf.stalk (f p'.1)) → IsNoetherianRing (X.presheaf.stalk (f p'.1)) → (∃ ζ : Ω, IsPrimitiveRoot ζ N) → M.IsHTFormAt N ⟨f p'.1, h⟩ 0 → M'.htLat N p' = (M.htLat N).pull ξ' f jd p' := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ _ _ φ V V' _ _ _ _ M M' j gen gen' dom hφ hsm hj jd hjd N hN p' h hic hnoe
    hroot h0
  obtain ⟨ζ, hζ⟩ := hroot
  obtain ⟨hext, hspan, hlat⟩ := GlobalTheory.T.lie_lattice_dominant_compat X X' Ω Ω' ξ ξ' f i G G' φ V V' M M' j gen gen' dom hφ hsm hj
  have hsm' : Smooth G'.hom := MorphismProperty.of_isPullback hφ.1 hsm
  let p : Cpt ξ := ⟨f p'.1, h⟩
  let k := genMap ξ p
  let k' := genMap ξ' p'
  have hkinj : Function.Injective k := gen.inj p
  have hk'inj : Function.Injective k' := gen'.inj p'
  haveI : IsDomain (X.presheaf.stalk (f p'.1)) := hkinj.isDomain k
  haveI : IsDomain (X'.presheaf.stalk p'.1) := hk'inj.isDomain k'
  letI : Algebra (X.presheaf.stalk (f p'.1)) (X'.presheaf.stalk p'.1) := (f.stalkMap p'.1).hom.toAlgebra
  have hk : ∀ r, k' (algebraMap (X.presheaf.stalk (f p'.1)) (X'.presheaf.stalk p'.1) r) = i (k r) :=
    GlobalTheory.CompanionTheory.Ar.Flat.PullReg.stalkMap_comp_genMap dom p' h
  have hs : Function.Injective (algebraMap (X.presheaf.stalk (f p'.1)) (X'.presheaf.stalk p'.1)) := by
    intro a b e
    exact hkinj (i.injective (by rw [← hk, ← hk, e]))
  have hx : X'.fromSpecStalk p'.1 ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk (f p'.1)) (X'.presheaf.stalk p'.1))) ≫ X.fromSpecStalk (f p'.1) :=
    (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
  have hξ : ξ = Spec.map (CommRingCat.ofHom k) ≫ X.fromSpecStalk (f p'.1) := (RegAtDom.spec_genMap ξ _ h).symm
  have hξ' : ξ' = Spec.map (CommRingCat.ofHom k') ≫ X'.fromSpecStalk p'.1 :=
    (RegAtDom.spec_genMap ξ' p'.1 p'.2).symm
  haveI := hic
  haveI := hnoe
  haveI : NeZero N := ⟨hN.ne'⟩

  have hfr := RegAtRing.regAt_ring X Ω ξ gen p
  haveI : IsFractionRing (regAt ξ p) Ω := hfr.1
  haveI : IsIntegrallyClosed (regAt ξ p) := hfr.2.2 hic
  have hζint : IsIntegral (regAt ξ p) ζ :=
    IsIntegral.of_pow hN (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hζint
  obtain ⟨z, hz⟩ := y.2
  have hkz : k z = ζ := hz.trans hy
  have hzp : IsPrimitiveRoot z N := IsPrimitiveRoot.of_map_of_injective (by rw [hkz]; exact hζ : IsPrimitiveRoot (k z) N) hkinj
  have hN0 : (N : X'.presheaf.stalk p'.1) ≠ 0 := by
    intro e
    have e' : (N : Ω') = 0 := by simpa using congrArg k' e
    have e'' : (N : Ω) = 0 := i.injective (by simpa using e')
    exact (hζ.neZero').out e''
  have hjds : ∀ (a : Ω) (w : Module.Dual Ω V), jd (a • w) = i a • jd w := by
    intro a w
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨e, rfl⟩
    rw [hjd, LinearMap.smul_apply, LinearMap.smul_apply, hjd, smul_eq_mul, smul_eq_mul, map_mul]
  have hreg : ∀ c ∈ regAt ξ p, i c ∈ regAt ξ' p' := by
    rintro _ ⟨r, rfl⟩
    exact ⟨_, hk r⟩
  have hC : ∀ u' ∈ M'.omLat p', N • u' ∈ (M.htLat N).pull ξ' f jd p' := by
    intro u' hu'
    have hu'' : ∀ e ∈ M'.lat p', u' e ∈ regAt ξ' p' := hu'
    obtain ⟨n, δ, b, hb, hδ, hdec⟩ := HTPull.om_decomp (M := M) hξ hsm i j hext.1 hspan jd hjd
    have hδom : ∀ a, δ a ∈ M.omLat p := by
      intro a
      show ∀ e ∈ M.lat p, δ a e ∈ regAt ξ p
      intro e he
      obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X G Ω ξ V M p).1 e).1 he
      exact hδ a e v hv hev
    have hNδ : ∀ a, (N : Ω) • δ a ∈ M.htLat N p := fun a =>
      (GlobalTheory.T.hodge_tate_lattice_le_omega X Ω ξ G V M N p gen hsm).2 h0 (δ a) (hδom a)
    have hc : ∀ a, u' (j (b a)) ∈ regAt ξ' p' := by
      intro a
      apply hu''
      rw [hlat]
      exact Submodule.subset_span ⟨h, b a, Submodule.subset_span (hb a), rfl⟩
    rw [hdec u', Finset.smul_sum]
    refine sum_mem fun a _ => ?_
    have e1 : N • (u' (j (b a)) • jd (δ a)) = u' (j (b a)) • jd ((N : Ω) • δ a) := by
      rw [Nat.cast_smul_eq_nsmul, map_nsmul, smul_comm]
    rw [e1]
    exact Submodule.smul_mem _ (⟨_, hc a⟩ : regAt ξ' p') (Submodule.subset_span ⟨h, _, hNδ a, rfl⟩)
  apply le_antisymm
  · refine Submodule.span_le.2 fun w' hw' => ?_
    obtain ⟨w, hwF, u', rfl, hu⟩ := HTPull.backward (M := M) (M' := M') hs hx hφ hsm hk hξ hξ' hj hN hN0 hzp h0 jd hjd hw'
    have hu' : u' ∈ M'.omLat p' := by
      intro e he
      obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X' G' Ω' ξ' V' M' p').1 e).1 he
      exact hu e v hv hev
    exact add_mem (Submodule.subset_span ⟨h, w, Submodule.subset_span hwF, rfl⟩) (hC u' hu')
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨h', e, he, rfl⟩
    show jd e ∈ M'.htLat N p'
    have he' : e ∈ M.htLat N p := he
    clear he
    induction he' using Submodule.span_induction with
    | mem w hw =>
      exact Submodule.subset_span (HTPull.forward (M := M) (M' := M') hs hx hφ hsm hk hξ' hj (hjd w) hw)
    | zero => simp
    | add a b _ _ ha hb => simpa using add_mem ha hb
    | smul c a _ ha =>
      have e1 : jd (c • a) = i c • jd a := hjds c a
      rw [e1]
      exact Submodule.smul_mem _ (⟨i c, hreg c c.2⟩ : regAt ξ' p') ha
