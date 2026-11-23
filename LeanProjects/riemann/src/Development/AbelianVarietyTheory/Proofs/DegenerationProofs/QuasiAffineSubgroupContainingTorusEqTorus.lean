import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsClosedImageOfIsClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.QuasiAffineTorus

section Algebra

variable {k : Type} [Field k] [IsAlgClosed k] {X : Type} [AddCommGroup X]

theorem exists_extend (M : AddSubgroup X) (φ : M →+ Additive kˣ) :
    ∃ t : Multiplicative X →* kˣ, ∀ m : M, t (Multiplicative.ofAdd (m : X)) = (φ m).toMul := by
  letI : RootableBy kˣ ℕ := rootableByOfPowLeftSurj _ _ fun {n} hn u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : k) (Nat.pos_of_ne_zero hn)
    have h0 : z ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [← hz, zero_pow hn])
    exact ⟨Units.mk0 z h0, Units.ext (by simpa using hz)⟩
  letI : RootableBy kˣ ℤ := Group.rootableByIntOfRootableByNat _
  letI : DivisibleBy (Additive kˣ) ℤ :=
    { div := fun a n => Additive.ofMul (RootableBy.root a.toMul n)
      div_zero := fun a => congrArg Additive.ofMul (RootableBy.root_zero a.toMul)
      div_cancel := fun a hn => congrArg Additive.ofMul (RootableBy.root_cancel a.toMul hn) }
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive kˣ)).extension_property_addMonoidHom
    M.subtype M.subtype_injective φ
  exact ⟨AddMonoidHom.toMultiplicativeLeft h, fun m => congrArg Additive.toMul (DFunLike.congr_fun hh m)⟩

theorem linearIndependent_chars [Module.Free ℤ X] :
    LinearIndependent k fun (χ : X) (t : Multiplicative X →* kˣ) =>
      (t (Multiplicative.ofAdd χ) : k) := by
  let v : X → ((Multiplicative X →* kˣ) →* k) := fun χ =>
    (Units.coeHom k).comp (MonoidHom.eval (Multiplicative.ofAdd χ))
  refine (linearIndependent_monoidHom (Multiplicative X →* kˣ) k).comp v fun χ ψ h => ?_
  let b := Module.Free.chooseBasis ℤ X
  refine b.ext_elem fun j => ?_
  classical
  by_contra hne
  obtain ⟨z, hz, hz0⟩ : ∃ z : k, z ^ (b.repr χ j - b.repr ψ j).natAbs ≠ 1 ∧ z ≠ 0 := by
    have hn : 0 < (b.repr χ j - b.repr ψ j).natAbs := Int.natAbs_pos.2 (sub_ne_zero.2 hne)
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
      (insert (0 : k) (Polynomial.nthRoots (b.repr χ j - b.repr ψ j).natAbs (1 : k)).toFinset)
    simp only [Finset.mem_insert, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn, not_or] at hz
    exact ⟨z, hz.2, hz.1⟩
  let t : Multiplicative X →* kˣ :=
    (zpowersHom kˣ (Units.mk0 z hz0)).comp (AddMonoidHom.toMultiplicative (b.coord j).toAddMonoidHom)
  have h1 : t (Multiplicative.ofAdd χ) = t (Multiplicative.ofAdd ψ) :=
    Units.ext (DFunLike.congr_fun h t)
  have h2 : Units.mk0 z hz0 ^ (b.repr χ j - b.repr ψ j) = 1 := by
    rw [zpow_sub, mul_inv_eq_one]
    exact h1
  have h3 := congrArg Units.val (pow_natAbs_eq_one.2 h2)
  exact hz (by simpa using h3)

variable {H : Type} [CommGroup H] (τ : (Multiplicative X →* kˣ) →* H) (A : Subalgebra k (H → k))

theorem exists_weight_decomposition [Module.Free ℤ X] {U : Type} (j : U → H)
    (hU : ∀ f ∈ A, (∀ u, f (j u) = 0) → f = 0)
    (htr : ∀ f ∈ A, ∀ t, (fun y => f (τ t * y)) ∈ A) {f : H → k} (hf : f ∈ A) (S : Finset X)
    (a : X → U → k)
    (ha : ∀ u t, f (τ t * j u) = ∑ χ ∈ S, (t (Multiplicative.ofAdd χ) : k) * a χ u) :
    ∃ g : S → H → k, (∀ χ, g χ ∈ A ∧
      ∀ t y, g χ (τ t * y) = (t (Multiplicative.ofAdd (χ : X)) : k) * g χ y) ∧ f = ∑ χ, g χ := by
  classical
  have hsp := span_flip_eq_top_iff_linearIndependent.2
    ((linearIndependent_chars (k := k) (X := X)).comp (Subtype.val : S → X) Subtype.val_injective)
  have key : ∀ w : S → k, ∃ g ∈ A, ∀ u t, g (τ t * j u) =
      ∑ χ : S, w χ * ((t (Multiplicative.ofAdd (χ : X)) : k) * a χ u) := by
    intro w
    have hw : w ∈ (⊤ : Submodule k (S → k)) := trivial
    rw [← hsp] at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨s, rfl⟩ := hw
      refine ⟨_, htr f hf s, fun u t => ?_⟩
      rw [← _root_.mul_assoc, ← map_mul, ha u, ← Finset.sum_coe_sort]
      simp [flip, _root_.mul_assoc]
    | zero => exact ⟨0, A.zero_mem, fun u t => by simp⟩
    | add w w' _ _ h h' =>
      obtain ⟨g, hg, h⟩ := h
      obtain ⟨g', hg', h'⟩ := h'
      exact ⟨g + g', A.add_mem hg hg', fun u t => by
        simp [h u, h' u, add_mul, Finset.sum_add_distrib]⟩
    | smul c w _ h =>
      obtain ⟨g, hg, h⟩ := h
      exact ⟨c • g, A.smul_mem hg c, fun u t => by
        simp [h u, Finset.mul_sum, _root_.mul_assoc]⟩
  choose g hgA hg using fun χ : S => key (Pi.single χ 1)
  have hg' : ∀ χ : S, ∀ u t, g χ (τ t * j u) =
      (t (Multiplicative.ofAdd (χ : X)) : k) * a χ u := fun χ u t => by
    rw [hg χ u, Finset.sum_eq_single χ (fun ψ _ h => by simp [h]) (by simp)]
    simp
  have hg1 : ∀ χ : S, ∀ u, g χ (j u) = a χ u := fun χ u => by simpa using hg' χ u 1
  refine ⟨g, fun χ => ⟨hgA χ, fun t y => ?_⟩, ?_⟩
  · have := hU _ (A.sub_mem (htr _ (hgA χ) t)
      (A.smul_mem (hgA χ) (t (Multiplicative.ofAdd (χ : X)) : k))) fun u => by
        simp [hg' χ u, hg1 χ u]
    simpa [sub_eq_zero] using congrFun this y
  · rw [← sub_eq_zero]
    refine hU _ (A.sub_mem hf (A.sum_mem fun χ _ => hgA χ)) fun u => ?_
    have := ha u 1
    rw [← Finset.sum_coe_sort] at this
    simpa [sub_eq_zero, hg1 _ u] using this

theorem exists_point_of_weights (hdom : ∀ f ∈ A, ∀ g ∈ A, f * g = 0 → f = 0 ∨ g = 0)
    (hinv : ∀ f ∈ A, (fun y => f y⁻¹) ∈ A)
    (hc : ∀ f ∈ A, (∀ t y, f (τ t * y) = f y) → ∀ y, f y = f 1) (x : H) :
    ∃ t, ∀ g ∈ A, ∀ χ : X, (∀ t y, g (τ t * y) = (t (Multiplicative.ofAdd χ) : k) * g y) →
      g x = g (τ t) := by
  let Wt : (H → k) → X → Prop := fun g χ =>
    g ∈ A ∧ ∀ t y, g (τ t * y) = (t (Multiplicative.ofAdd χ) : k) * g y
  have hneg : ∀ g χ, Wt g χ → Wt (fun y => g y⁻¹) (-χ) := fun g χ h =>
    ⟨hinv g h.1, fun t y => by
      simp only [mul_inv, ← map_inv τ, h.2, ofAdd_neg, map_inv t]
      rfl⟩
  have hmul : ∀ g χ g' χ', Wt g χ → Wt g' χ' → Wt (g * g') (χ + χ') := fun g χ g' χ' h h' =>
    ⟨A.mul_mem h.1 h'.1, fun t y => by
      simp only [Pi.mul_apply, h.2, h'.2, ofAdd_add, map_mul, Units.val_mul]
      ring⟩
  have hone : Wt 1 0 := ⟨A.one_mem, fun t y => by simp⟩
  have hpair : ∀ g g' χ, Wt g χ → Wt g' χ → ∀ y, g y * g' y⁻¹ = g 1 * g' 1 := by
    intro g g' χ h h' y
    have h1 := hmul _ _ _ _ h (hneg _ _ h')
    simpa using hc _ h1.1 (fun t y => by rw [h1.2]; simp) y
  let M : AddSubgroup X :=
    { carrier := {χ | ∃ g, Wt g χ ∧ g 1 = 1}
      zero_mem' := ⟨1, hone, rfl⟩
      add_mem' := by
        rintro χ χ' ⟨g, h, e⟩ ⟨g', h', e'⟩
        exact ⟨_, hmul _ _ _ _ h h', by simp [e, e']⟩
      neg_mem' := by
        rintro χ ⟨g, h, e⟩
        exact ⟨_, hneg _ _ h, by simpa using e⟩ }
  choose u hu hu1 using fun m : M => (m.2 : ∃ g, Wt g m ∧ g 1 = 1)
  have hux : ∀ m, u m x * u m x⁻¹ = 1 := fun m => by simpa [hu1] using hpair _ _ _ (hu m) (hu m) x
  have huniq : ∀ (m : M) g, Wt g m → g x = g 1 * u m x := fun m g h => by
    have h1 := hpair _ _ _ h (hu m) x
    rw [hu1, _root_.mul_one] at h1
    rw [← h1, _root_.mul_assoc, mul_comm (u m x⁻¹), hux, _root_.mul_one]
  let φ : M →+ Additive kˣ := AddMonoidHom.mk'
    (fun m => Additive.ofMul (Units.mk0 (u m x) (left_ne_zero_of_mul_eq_one (hux m))))
    fun m m' => congrArg Additive.ofMul (Units.ext (by
      simpa [hu1] using (huniq (m + m') _ (hmul _ _ _ _ (hu m) (hu m'))).symm))
  obtain ⟨t, ht⟩ := exists_extend M φ
  refine ⟨t, fun g hg χ hχ => ?_⟩
  have h : Wt g χ := ⟨hg, hχ⟩
  by_cases h1 : g 1 = 0
  · have h0 : g * (fun y => g y⁻¹) = 0 := funext fun y => by simpa [h1] using hpair _ _ _ h h y
    have : g = 0 := by
      rcases hdom _ hg _ (hinv g hg) h0 with e | e
      · exact e
      · funext y
        simpa using congrFun e y⁻¹
    simp [this]
  · have hm : χ ∈ M := ⟨(g 1)⁻¹ • g, ⟨A.smul_mem hg _, fun t y => by simp [hχ]; ring⟩, by simp [h1]⟩
    have h2 := hχ t 1
    rw [_root_.mul_one] at h2
    rw [h2, huniq ⟨χ, hm⟩ g h, ht ⟨χ, hm⟩, mul_comm]
    rfl

end Algebra

section Geometry

open RationalPoint

variable {k : Type} [Field k]

noncomputable def ev {N : Over (Sp k)} (x : 𝟙_ (Over (Sp k)) ⟶ N) : Γ(N.left, ⊤) →+* k :=
  (Scheme.ΓSpecIso (.of k)).hom.hom.comp (Scheme.Hom.appTop (X := Sp k) x.left).hom

theorem ev_comp {N N' : Over (Sp k)} (x : 𝟙_ (Over (Sp k)) ⟶ N) (g : N ⟶ N') (f : Γ(N'.left, ⊤)) :
    ev (x ≫ g) f = ev x (g.left.appTop.hom f) := rfl

noncomputable def const (N : Over (Sp k)) : k →+* Γ(N.left, ⊤) :=
  N.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

theorem ev_const {N : Over (Sp k)} (x : 𝟙_ (Over (Sp k)) ⟶ N) (r : k) : ev x (const N r) = r := by
  have h : x.left ≫ N.hom = 𝟙 (Sp k) := Over.w x
  have h1 : ∀ a, (Scheme.Hom.appTop (X := Sp k) x.left).hom (N.hom.appTop.hom a) = a := fun a => by
    have := FunDescent.comp_appTop_apply x.left N.hom a
    rw [h] at this
    exact this.symm
  change (Scheme.ΓSpecIso (.of k)).hom.hom (_) = r
  erw [h1]
  simp

theorem appTop_eq_of_ev_eq {N : Over (Sp k)} {x y : 𝟙_ (Over (Sp k)) ⟶ N} {f g : Γ(N.left, ⊤)}
    (h : ev x f = ev y g) : x.left.appTop.hom f = y.left.appTop.hom g :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).hom).1 h

theorem ev_ne_zero {N : Over (Sp k)} (x : 𝟙_ (Over (Sp k)) ⟶ N) {f : Γ(N.left, ⊤)}
    (h : pt x ∈ N.left.basicOpen f) : ev x f ≠ 0 := fun e => by
  have h1 : x.left.appTop.hom f = 0 := by
    rw [appTop_eq_of_ev_eq (y := x) (g := 0) (by rw [e, map_zero]), map_zero]
  have h2 : IsLocalRing.closedPoint k ∈ x.left ⁻¹ᵁ N.left.basicOpen f := h
  rw [Scheme.preimage_basicOpen_top] at h2
  erw [h1, Scheme.basicOpen_zero] at h2
  exact h2

theorem eq_of_ev_eq {N : Over (Sp k)} [N.left.IsQuasiAffine] {x y : 𝟙_ (Over (Sp k)) ⟶ N}
    (h : ∀ f, ev x f = ev y f) : x = y := by
  have h1 : x.left.appTop = y.left.appTop := by
    ext f
    exact appTop_eq_of_ev_eq (h f)
  ext1
  rw [← cancel_mono N.left.toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h1]

variable [IsAlgClosed k]

theorem exists_pt_mem_open {N : Over (Sp k)} [LocallyOfFiniteType N.hom] {W : Set N.left}
    (hW : IsOpen W) (hne : W.Nonempty) : ∃ x : 𝟙_ (Over (Sp k)) ⟶ N, pt x ∈ W := by
  have : JacobsonSpace N.left := LocallyOfFiniteType.jacobsonSpace N.hom
  obtain ⟨c, hc, hcc⟩ := nonempty_inter_closedPoints hne hW.isLocallyClosed
  obtain ⟨x, hx⟩ := exists_pt_mem (Z := {c}) hcc ⟨c, rfl⟩
  exact ⟨x, (show pt x = c from hx) ▸ hc⟩

theorem eq_zero_of_ev {N : Over (Sp k)} [LocallyOfFiniteType N.hom] [IsReduced N.left]
    {f : Γ(N.left, ⊤)} (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, ev x f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  obtain ⟨x, hx⟩ := exists_pt_mem_open (N.left.basicOpen f).isOpen
    (Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e))
  exact ev_ne_zero x hx (h x)

theorem exists_lift {T N G : Over (Sp k)} [LocallyOfFiniteType T.hom] [IsReduced T.left]
    [IsReduced N.left] (ν : N ⟶ G) [IsClosedImmersion ν.left] (g : T ⟶ G)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ T, Set.range (x ≫ g).left ⊆ Set.range ν.left) :
    ∃ l : T ⟶ N, l ≫ ν = g := by
  have h1 := ReducedSubgroup.range_subset_of_points g ν.left.isClosedEmbedding.isClosed_range h
  have h2 : ν.left.ker ≤ g.left.ker := by
    refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun U a ha => ?_
    rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
    intro t ht
    obtain ⟨n, hn⟩ := h1 ⟨t, rfl⟩
    have h3 : n ∈ ν.left ⁻¹ᵁ G.left.basicOpen a := by
      change ν.left n ∈ G.left.basicOpen a
      rw [hn]
      exact ht
    rw [Scheme.preimage_basicOpen, show ν.left.app U a = 0 from ν.left.ideal_ker_le U ha,
      Scheme.basicOpen_zero] at h3
    exact h3
  have h3 := IsClosedImmersion.lift_fac ν.left g.left h2
  refine ⟨Over.homMk (IsClosedImmersion.lift ν.left g.left h2) ?_, ?_⟩
  · rw [← Over.w ν, ← Category.assoc, h3, Over.w]
  · ext1
    exact h3

theorem exists_const_of_invariant {G B T N : Over (Sp k)} [GrpObj G] [GrpObj B] [GrpObj T]
    [GrpObj N] (i : T ⟶ G) (q : G ⟶ B) (ν : N ⟶ G) (i' : T ⟶ N) [IsMonHom q] [IsMonHom ν]
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper B.hom] [Smooth T.hom]
    [Smooth N.hom] [QuasiCompact N.hom] [IsIntegral N.left] [IsClosedImmersion ν.left]
    (hk : IsPullback i (toUnit _) q η[B]) (hi : i' ≫ ν = i) (f : Γ(N.left, ⊤))
    (hf : ∀ (t : 𝟙_ (Over (Sp k)) ⟶ T) (y : 𝟙_ (Over (Sp k)) ⟶ N),
      ev ((t ≫ i') * y) f = ev y f) : ∃ r, const N r = f := by
  have : Mono ν := Over.mono_of_mono_left ν
  have hsat : ∀ {Z : Over (Sp k)} (g : Z ⟶ G) (n : Z ⟶ N), g ≫ q = n ≫ ν ≫ q →
      ∃ t : Z ⟶ T, ((t ≫ i') * n) ≫ ν = g := by
    intro Z g n e
    have w : (g * (n ≫ ν)⁻¹) ≫ q = toUnit Z ≫ η[B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, e, Category.assoc, mul_inv_cancel]
      rfl
    exact ⟨hk.lift _ _ w, by
      rw [MonObj.mul_comp, Category.assoc, hi, hk.lift_fst, inv_mul_cancel_right]⟩
  have hf' : ∀ {Z : Over (Sp k)} (t : Z ⟶ T) (n : Z ⟶ N),
      ((t ≫ i') * n).left.appTop.hom f = n.left.appTop.hom f := by
    intro Z t n
    have : Smooth (T ⊗ N).hom := inferInstanceAs (Smooth (pullback.fst T.hom N.hom ≫ T.hom))
    have : IsReduced (T ⊗ N).left := isReduced_of_smooth_of_isReduced (T ⊗ N).hom
    have h0 : ((fst T N ≫ i') * snd T N).left.appTop.hom f = (snd T N).left.appTop.hom f := by
      rw [← sub_eq_zero]
      refine eq_zero_of_ev fun x => ?_
      rw [map_sub, ← ev_comp, ← ev_comp, MonObj.comp_mul, ← Category.assoc, hf, sub_self]
    have h1 : (t ≫ i') * n = lift t n ≫ ((fst T N ≫ i') * snd T N) := by
      simp [MonObj.comp_mul]
    rw [h1, Over.comp_left, FunDescent.comp_appTop_apply, h0, ← FunDescent.comp_appTop_apply,
      ← Over.comp_left, lift_snd]
  obtain ⟨Z, hZ, hZ'⟩ := exists_isClosed_image_of_isClosed_subgroup k N B (ν ≫ q) inferInstance
    inferInstance inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ (by simp)
  let φ : (𝟙_ (Over (Sp k)) ⟶ N) →* (𝟙_ (Over (Sp k)) ⟶ B) :=
    MonoidHom.mk' (fun x => x ≫ ν ≫ q) fun x y => MonObj.mul_comp x y _
  obtain ⟨Y, _, β, -, hβ, hY, hr⟩ := ReducedSubgroup.exists_smooth_closed_subgroup k B
    inferInstance φ.range Z hZ fun y => by
      rw [← hZ']
      exact ⟨fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
  have : IsReduced Y.left := isReduced_of_smooth_of_isReduced Y.hom
  obtain ⟨m, hm⟩ := exists_lift β (ν ≫ q) fun x => by
    rw [hr, ← hZ']
    exact ⟨x, trivial, rfl⟩
  let P : Over (Sp k) := Over.mk (pullback.snd q.left β.left ≫ Y.hom)
  let π : P ⟶ Y := Over.homMk (pullback.snd q.left β.left) rfl
  let p : P ⟶ G := Over.homMk (pullback.fst q.left β.left) (by
    change _ = pullback.snd q.left β.left ≫ Y.hom
    rw [← Over.w q, pullback.condition_assoc, Over.w])
  have hP : p ≫ q = π ≫ β := Over.OverMorphism.ext pullback.condition
  have : Smooth P.hom := inferInstanceAs (Smooth (pullback.snd q.left β.left ≫ Y.hom))
  have : IsReduced P.left := isReduced_of_smooth_of_isReduced P.hom
  obtain ⟨l, hl⟩ := exists_lift ν p fun x => by
    obtain ⟨n, -, hn⟩ := (hZ' (x ≫ π ≫ β)).2 (by
      rw [← hr]
      rintro _ ⟨a, rfl⟩
      exact ⟨(x ≫ π).left a, rfl⟩)
    obtain ⟨t, ht⟩ := hsat (x ≫ p) n (by rw [Category.assoc, hP, hn])
    rw [← ht]
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := FunDescent.exists_appTop_eq (pullback.snd q.left β.left)
    (l.left.appTop.hom f) fun W g₁ g₂ e => by
      let W' : Over (Sp k) := Over.mk (g₂ ≫ P.hom)
      let k₂ : W' ⟶ P := Over.homMk g₂ rfl
      let k₁ : W' ⟶ P := Over.homMk g₁ (by
        change g₁ ≫ pullback.snd q.left β.left ≫ Y.hom = g₂ ≫ pullback.snd q.left β.left ≫ Y.hom
        rw [reassoc_of% e])
      have e' : k₁ ≫ π = k₂ ≫ π := Over.OverMorphism.ext e
      obtain ⟨t, ht⟩ := hsat ((k₁ ≫ l) ≫ ν) (k₂ ≫ l) (by
        simp only [Category.assoc, reassoc_of% hl, hP, reassoc_of% e'])
      have := hf' t (k₂ ≫ l)
      rw [(cancel_mono ν).1 ht] at this
      exact this
  let s : N ⟶ P := Over.homMk (pullback.lift ν.left m.left (congrArg (·.left) hm).symm) (by
    change _ ≫ pullback.snd q.left β.left ≫ Y.hom = _
    rw [pullback.lift_snd_assoc, Over.w])
  have hs : s ≫ l = 𝟙 N := by
    rw [← cancel_mono ν, Category.assoc, hl, Category.id_comp]
    exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have hsm : s.left ≫ pullback.snd q.left β.left = m.left := pullback.lift_snd _ _ _
  have hfa : f = m.left.appTop.hom a := by
    rw [← hsm]
    erw [FunDescent.comp_appTop_apply, ha, ← FunDescent.comp_appTop_apply, ← Over.comp_left, hs]
    rfl
  have : IsProper Y.hom := by rw [← Over.w β]; infer_instance
  have hint : (const Y).IsIntegral :=
    RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
      (isIntegral_appTop_of_universallyClosed Y.hom)
  have hc : m.left.appTop.hom.comp (const Y) = const N := by
    ext r
    change m.left.appTop.hom (Y.hom.appTop.hom _) = _
    rw [← FunDescent.comp_appTop_apply, Over.w]
    rfl
  have hfi : (const N).IsIntegralElem f := by
    rw [hfa, ← hc]
    exact (hint a).map _
  letI := (const N).toAlgebra
  exact minpoly.mem_range_of_degree_eq_one k f (IsAlgClosed.degree_eq_one_of_irreducible k
    (minpoly.irreducible hfi))

end Geometry

section Main

open RationalPoint

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

noncomputable def torusPt (k : Type) [Field k] (X : Type) [AddCommGroup X] :
    (Multiplicative X →* kˣ) ≃* (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :=
  ((splitTorusPointsEquiv (Sp k) X (𝟙_ (Over (Sp k)))).trans (MulEquiv.monoidHomCongrRight
    (Units.mapEquiv (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv))).symm

theorem ev_torusPt (t : Multiplicative X →* kˣ) (χ : X) :
    ev (torusPt k X t) (charUnit (Sp k) X χ).val = t (Multiplicative.ofAdd χ) := by
  obtain ⟨s, rfl⟩ := (torusPt k X).symm.surjective t
  rw [MulEquiv.apply_symm_apply]
  exact congrArg (Scheme.ΓSpecIso (.of k)).hom.hom (splitTorusPointsEquiv_val _ _ _ s χ).symm

theorem exists_expansion {U : Over (Sp k)} [IsAffine U.left]
    (F : Γ((splitTorus (Sp k) X ⊗ U).left, ⊤)) :
    ∃ (S : Finset X) (a : X → Γ(U.left, ⊤)), ∀ (u : 𝟙_ (Over (Sp k)) ⟶ U)
      (t : Multiplicative X →* kˣ), ev (lift (torusPt k X t) u) F =
        ∑ χ ∈ S, (t (Multiplicative.ofAdd χ) : k) * ev u (a χ) := by
  have : IsIso (lift (fst (splitTorus (Sp k) X) U) (snd _ U)) := by
    rw [lift_fst_snd]; infer_instance
  let c := splitTorusPointsEquiv (Sp k) X _ (fst (splitTorus (Sp k) X) U)
  let ψ : AddMonoidAlgebra Γ(U.left, ⊤) X →+* Γ((splitTorus (Sp k) X ⊗ U).left, ⊤) :=
    AddMonoidAlgebra.liftNCRingHom (snd (splitTorus (Sp k) X) U).left.appTop.hom
      ((Units.coeHom _).comp c) (fun _ _ => Commute.all _ _)
  have hψ : ∀ χ a, ψ (AddMonoidAlgebra.single χ a) =
      (snd (splitTorus (Sp k) X) U).left.appTop.hom a *
        (fst (splitTorus (Sp k) X) U).left.appTop.hom (charUnit (Sp k) X χ).val := fun χ a => by
    rw [← splitTorusPointsEquiv_val]
    exact AddMonoidAlgebra.liftNC_single _ _ χ a
  obtain ⟨-, h⟩ := TorusTrivial.isAffine_and_bijective (fst (splitTorus (Sp k) X) U) (snd _ U)
    (Iso.refl Γ(U.left, ⊤)) ψ (fun a => by
      refine (AddMonoidAlgebra.liftNC_single _ _ 0 a).trans ?_
      exact (congrArg (_ * ·) (((Units.coeHom _).comp c).map_one)).trans (_root_.mul_one _))
    (fun χ => by rw [hψ, map_one, _root_.one_mul])
  obtain ⟨p, rfl⟩ := h.2 F
  refine ⟨p.coeff.support, p.coeff, fun u t => ?_⟩
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  rw [Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [hψ, map_mul, ← ev_comp, ← ev_comp, lift_fst, lift_snd, ev_torusPt, mul_comm]

end Main

open RationalPoint in

theorem main : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G →  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → IsAbelianScheme B → ∀ (N : Over (Sp k)) [GrpObj N] (ν : N ⟶ G) (i' : splitTorus (Sp k) X ⟶ N), SmConn N → IsMonHom ν → IsClosedImmersion ν.left → i' ≫ ν = i → (∀ x : N.left, ∃ f : Γ(N.left, ⊤), x ∈ N.left.basicOpen f ∧ IsAffineOpen (N.left.basicOpen f)) → ∀ x : (𝟙_ (Over (Sp k)) ⟶ N), ∃ t : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X), t ≫ i = x ≫ ν := by
  intro k _ _ G _ hG X _ _ _ B _ i q hq hB N _ ν i' hN hν hcl hi haff x
  obtain ⟨hi₀, hq₀, hfl, hsu, haf, hk, -⟩ := hq
  obtain ⟨hcomm, hsm, -, hqc, hgc⟩ := hN
  have := hB.proper
  have : Smooth q.left := (torusExtension_smooth_geometricallyConnected G
    ⟨X, B, hB, q, hq₀, hfl, hsu, inferInstance, i, hi₀, hk⟩).1
  have : Smooth (splitTorus (Sp k) X).hom := (ReciprocityTheory.ChartRestriction.G.H1.torus_dim (Sp k) X).smooth
  have : IsIntegral N.left := isIntegral_of_smooth_of_geometricallyConnected N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : N.left.IsQuasiAffine := .of_forall_exists_mem_basicOpen _ fun y =>
    (haff y).imp fun _ h => h.symm
  have : Mono ν := Over.mono_of_mono_left ν
  let τ : (Multiplicative X →* kˣ) →* (𝟙_ (Over (Sp k)) ⟶ N) :=
    MonoidHom.mk' (fun t => torusPt k X t ≫ i') fun s t => by
      rw [← cancel_mono ν]
      simp only [MonObj.mul_comp, Category.assoc, hi, map_mul]
  let E : Γ(N.left, ⊤) →+* ((𝟙_ (Over (Sp k)) ⟶ N) → k) := RingHom.pi fun y => ev y
  have hE : ∀ f, E f = 0 → f = 0 := fun f h => eq_zero_of_ev fun y => congrFun h y
  let A : Subalgebra k ((𝟙_ (Over (Sp k)) ⟶ N) → k) :=
    { E.range.toSubsemiring with
      algebraMap_mem' := fun r => ⟨const N r, funext fun y => ev_const y r⟩ }
  have hA : ∀ (g : N ⟶ N), ∀ f ∈ A, (fun y => f (y ≫ g)) ∈ A := by
    rintro g _ ⟨f, rfl⟩
    exact ⟨g.left.appTop.hom f, rfl⟩
  have htr : ∀ f ∈ A, ∀ t, (fun y => f (τ t * y)) ∈ A := fun f hf t => by
    convert hA ((toUnit N ≫ τ t) * 𝟙 N) f hf using 3 with y
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit N) (𝟙 _),
      Category.id_comp]
  obtain ⟨t, ht⟩ := exists_point_of_weights τ A
    (by
      rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩ h
      rw [← map_mul] at h
      exact (mul_eq_zero.1 (hE _ h)).imp (fun e => by rw [e, map_zero]) fun e => by rw [e, map_zero])
    (fun f hf => by
      convert hA (𝟙 N)⁻¹ f hf using 3 with y
      rw [GrpObj.comp_inv, Category.comp_id])
    (by
      rintro _ ⟨f, rfl⟩ h y
      obtain ⟨r, rfl⟩ := exists_const_of_invariant i q ν i' hk hi f fun s z => by
        obtain ⟨s, rfl⟩ := (torusPt k X).surjective s
        exact h s z
      exact (ev_const y r).trans (ev_const 1 r).symm) x
  refine ⟨torusPt k X t, ?_⟩
  rw [← hi, ← Category.assoc]
  congr 1
  refine eq_of_ev_eq fun f => ?_
  obtain ⟨V, hxV, hV⟩ : ∃ V : N.left.Opens, pt x ∈ V ∧ IsAffineOpen V := by
    obtain ⟨f₀, h₀⟩ := haff (pt x)
    exact ⟨_, h₀⟩
  let U : Over (Sp k) := Over.mk (V.ι ≫ N.hom)
  let j : U ⟶ N := Over.homMk V.ι rfl
  have : IsAffine U.left := hV
  have : LocallyOfFiniteType U.hom := inferInstanceAs (LocallyOfFiniteType (V.ι ≫ N.hom))
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : IsReduced U.left := isReduced_of_isOpenImmersion V.ι
  obtain ⟨S, a, ha⟩ := exists_expansion (X := X)
    (((fst _ U ≫ i') * (snd _ U ≫ j)).left.appTop.hom f)
  obtain ⟨g, hg, hs⟩ := exists_weight_decomposition τ A
    (fun u : 𝟙_ (Over (Sp k)) ⟶ U => u ≫ j)
    (by
      rintro _ ⟨f, rfl⟩ h
      have h1 : f = 0 := by
        rw [← basicOpen_eq_bot_iff]
        by_contra hne
        obtain ⟨z, hz1, hz2⟩ := nonempty_preirreducible_inter (N.left.basicOpen f).isOpen V.isOpen
          (Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)) ⟨_, hxV⟩
        obtain ⟨u, hu⟩ := exists_pt_mem_open (N := U) (j.left ⁻¹ᵁ N.left.basicOpen f).isOpen
          ⟨⟨z, hz2⟩, hz1⟩
        exact ev_ne_zero (u ≫ j) hu (h u)
      rw [h1, map_zero])
    htr (f := E f) ⟨f, rfl⟩ S (fun χ u => ev u (a χ)) fun u s => by
      rw [← ha, ← ev_comp, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
      rfl
  change E f (τ t) = E f x
  rw [hs, Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun χ _ => (ht _ (hg χ).1 _ (hg χ).2).symm

end GlobalTheory.QuasiAffineTorus
