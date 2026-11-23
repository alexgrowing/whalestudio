import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsumSmulEqOneOfTame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantTowerAlgebraMapInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfTameDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemMapKerOfOneTmulEqZeroOfFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientIsFiniteLocallyOfFiniteTypeDescendStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.TameDescent

theorem specMap_fromSpec_comp_eq_iff {X : Scheme.{0}} (t : X ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : U ≤ t ⁻¹ᵁ U) {k : CommRingCat.{0}} (a : Γ(X, U) ⟶ k) :
    (Spec.map a ≫ hU.fromSpec) ≫ t = Spec.map a ≫ hU.fromSpec ↔
      ∀ b, a.hom ((t.appLE U U h).hom b - b) = 0 := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec t hU hU h, ← Category.assoc,
    cancel_mono, ← Spec.map_comp, Spec.map_injective.eq_iff]
  simp only [map_sub, sub_eq_zero]
  exact ⟨fun e b => congr(($e).hom b), fun e => CommRingCat.hom_ext (RingHom.ext e)⟩

theorem appLE_sub_mem_map {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] (t : Y ⟶ Y) {U : X.Opens}
    {W : Y.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U)
    (h : W ≤ t ⁻¹ᵁ W) {k : Type} [Field k] (a : Γ(X, U) →+* k)
    (ht : pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec) ≫ t =
      pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec)) (c : Γ(Y, W)) :
    (t.appLE W W h).hom c - c ∈ (RingHom.ker a).map (p.appLE U W e).hom := by
  let := a.toAlgebra
  let := (p.appLE U W e).hom.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, W) := p.flat_appLE hU hW e
  refine mem_map_ker_of_one_tmul_eq_zero_of_flat Γ(X, U) Γ(Y, W) k _ ?_
  let r : Γ(Y, W) ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let l : CommRingCat.of k ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  have w : (Spec.map r ≫ hW.fromSpec) ≫ p =
      Spec.map l ≫ Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec := by
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hU hW e,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    exact (CommRingCat.isPushout_tensorProduct Γ(X, U) k Γ(Y, W)).w.symm
  refine (specMap_fromSpec_comp_eq_iff t hW h r).1 ?_ c
  rw [← pullback.lift_fst _ _ w, Category.assoc, ht]

theorem isPullback_specMap_app {X X' : Scheme.{0}} (π : X ⟶ X') [IsAffineHom π] {V : X'.Opens}
    (hV : IsAffineOpen V) :
    IsPullback (Spec.map (π.app V)) (hV.preimage π).fromSpec hV.fromSpec π :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec]) (by simp)

theorem isPullback_of_isPushout_app {X X' Y Y' : Scheme.{0}} (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsAffineHom π] [IsAffineHom φ] (w : φ ≫ p' = p ≫ π)
    (H : ∀ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V → IsAffineOpen W →
      ∀ (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V),
      IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e')) :
    IsPullback φ p p' π := by
  have h : ∀ y : Y', ∃ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V ∧ IsAffineOpen W ∧
      y ∈ W ∧ W ≤ p' ⁻¹ᵁ V := fun y => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p' y)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hy, hle⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ p' ⁻¹ᵁ V from hx) (p' ⁻¹ᵁ V).isOpen
    exact ⟨V, W, hV, hW, hy, hle⟩
  choose V W hV hW hy hle using h
  let 𝒰 : Y'.OpenCover := Scheme.Cover.mkOfCovers Y' (fun y => Spec Γ(Y', W y))
    (fun y => (hW y).fromSpec) (fun y => ⟨y, by
      have : y ∈ Set.range (hW y).fromSpec := by
        rw [IsAffineOpen.range_fromSpec]; exact hy y
      exact this⟩)
  refine Scheme.isPullback_of_openCover φ p p' π 𝒰 fun y => ?_
  have e' : φ ⁻¹ᵁ W y ≤ p ⁻¹ᵁ π ⁻¹ᵁ V y := by
    rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
    exact φ.preimage_mono (hle y)
  have H1 := isPullback_specMap_app φ (hW y)
  have H2 := (isPullback_SpecMap_of_isPushout _ _ _ _
    (H _ _ (hV y) (hW y) (hle y) e')).paste_vert (isPullback_specMap_app π (hV y)).flip.flip
  rw [IsAffineOpen.SpecMap_appLE_fromSpec p _ ((hW y).preimage φ),
    IsAffineOpen.SpecMap_appLE_fromSpec p' _ (hW y)] at H2
  refine H2.of_iso H1.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by simp)
  · exact (Category.comp_id _).trans (H1.flip.isoPullback_hom_snd).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    congr 1
    exact (H1.flip.isoPullback_hom_fst).symm

theorem isPushout_and_flat {Γ : Type} [Group Γ] [Finite Γ] {X X' Y Y' : Scheme.{0}}
    [IsLocallyNoetherian Y'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsFinite π] [IsFinite φ] [Flat p]
    (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hπ' : ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
      (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (π.app V).hom)
    (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hφ' : ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    (w : φ ≫ p' = p ≫ π) (hp : ∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom)
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X),
      (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x →
      pullback.fst p x ≫ (τ g).hom = pullback.fst p x)
    (V : X'.Opens) (W : Y'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V) :
    IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e') ∧
      (p'.appLE V W e).hom.Flat := by
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hU' : IsAffineOpen (φ ⁻¹ᵁ W) := hW.preimage φ
  have hst := preimage_le_of_invariant ρ π hπ V
  have hst' := preimage_le_of_invariant τ φ hφ W
  let := sectionsAction ρ _ hst
  let := sectionsAction τ _ hst'
  let := (π.app V).hom.toAlgebra
  let := (φ.app W).hom.toAlgebra
  let := (p'.appLE V W e).hom.toAlgebra
  let := (p.appLE _ _ e').hom.toAlgebra
  let := (p'.appLE V W e ≫ φ.app W).hom.toAlgebra
  have sq : p'.appLE V W e ≫ φ.app W = π.app V ≫ p.appLE _ _ e' := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, w]
  have : IsScalarTower Γ(X', V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) :=
    .of_algebraMap_eq' congr(($sq).hom)
  have : SMulCommClass Γ Γ(X', V) Γ(X, π ⁻¹ᵁ V) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(X', V) Γ(X, π ⁻¹ᵁ V) a = algebraMap _ _ a :=
      (isInvariantSection_app ρ π hπ V a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : SMulCommClass Γ Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) a = algebraMap _ _ a :=
      (isInvariantSection_app τ φ hφ W a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ := ⟨fun s hs ↦
    (hπ' V).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩
  have : Algebra.IsInvariant Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    (hφ' W).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (τ g⁻¹⁻¹).hom.appLE _ _ (hst' _) s = s from hs g⁻¹)⟩
  have heq : ∀ (g : Γ) (b : Γ(X, π ⁻¹ᵁ V)), g • algebraMap _ Γ(Y, φ ⁻¹ᵁ W) b =
      algebraMap _ Γ(Y, φ ⁻¹ᵁ W) (g • b) := fun g b => by
    change (τ g⁻¹).hom.appLE _ _ (hst' _) (p.appLE _ _ e' b) =
      p.appLE _ _ e' ((ρ g⁻¹).hom.appLE _ _ (hst _) b)
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hp]
  have hflat : Module.Flat Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) := p.flat_appLE hU hU' e'
  have key : ∀ q : Ideal Γ(X, π ⁻¹ᵁ V), q.IsPrime → ((Nat.card (q.inertia Γ) : Γ(X, π ⁻¹ᵁ V)) ∉ q) ∧
      ∀ g ∈ q.inertia Γ, ∀ c : Γ(Y, φ ⁻¹ᵁ W), g • c - c ∈ q.map (algebraMap _ Γ(Y, φ ⁻¹ᵁ W)) := by
    intro q hq
    let k := AlgebraicClosure q.ResidueField
    let a : Γ(X, π ⁻¹ᵁ V) →+* k := (algebraMap q.ResidueField k).comp (algebraMap _ _)
    have ha : ∀ b, a b = 0 ↔ b ∈ q := fun b => by
      simp [a]
    have hker : RingHom.ker a = q := Ideal.ext ha
    let x : Sp k ⟶ X := Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec
    have hx : ∀ g, x ≫ (ρ g⁻¹).hom = x ↔ g ∈ q.inertia Γ := fun g =>
      (specMap_fromSpec_comp_eq_iff _ hU (hst _) _).trans (forall_congr' fun b => ha _)
    refine ⟨fun h => htame k x ?_, fun g hg c => ?_⟩
    · rw [← Nat.card_congr ((Equiv.inv Γ).subtypeEquiv (p := fun g => g ∈ q.inertia Γ)
        (q := fun g => x ≫ (ρ g).hom = x) fun g => (hx g).symm), ← map_natCast a]
      exact (ha _).2 h
    · rw [← hker]
      exact appLE_sub_mem_map p _ hU hU' e' (hst' _) a (hfix k x _ ((hx g).2 hg)) c
  have hpo : Algebra.IsPushout Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) :=
    GlobalTheory.T.invariant_tower_isPushout Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq
      (IsLocallyNoetherian.component_noetherian ⟨W, hW⟩) (π.finite_app V hV) (φ.finite_app W hW)
      hflat (fun q hq => (key q hq).1) (fun q hq => (key q hq).2)
  refine ⟨CommRingCat.isPushout_iff_isPushout.2 hpo.symm, ?_⟩
  exact flat_of_tame_descent Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq hpo hflat
    (exists_finsum_smul_eq_one_of_tame Γ _ fun q hq => (key q hq).1)

theorem isPullback_flat_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsAffineHom φ ∧ (∀ g, (τ g).hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → φ ≫ p' = p ≫ π → (∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom) → IsFinite π → Flat p → LocallyOfFiniteType p → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst p x ≫ (τ g).hom = pullback.fst p x) → IsPullback φ p p' π ∧ Flat p' ∧ LocallyOfFiniteType p' := by
  intro Γ _ _ X X' Y Y' _ ρ τ π φ p p' hπ hφ w hp _ _ _ htame hfix
  obtain ⟨_, _, -⟩ := GlobalTheory.T.quotient_isFinite_and_descends_finiteness_properties Γ Y Y' τ φ hφ X' p' (by rw [w]; infer_instance)
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p'
  have H := isPushout_and_flat ρ τ π φ p p' hπ.2.1 hπ.2.2 hφ.2.1 hφ.2.2 w hp htame hfix
  refine ⟨isPullback_of_isPushout_app π φ p p' w fun V W hV hW e e' => (H V W hV hW e e').1,
    ⟨fun {V} hV {W} hW e => (H V W hV hW e ?_).2⟩, inferInstance⟩
  rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  exact φ.preimage_mono e

end GlobalTheory.TameDescent
