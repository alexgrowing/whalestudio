import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

namespace GlobalTheory.LocLift

noncomputable section

section Hol

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {X Y : Scheme.{0}}

theorem isHolTo_comp_hom {B : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) :
    IsHolTo B (fun b => y b ≫ φ) := by
  intro U f
  have := h (φ ⁻¹ᵁ U) ((φ.app U).hom f)
  simpa only [valAt'_comp, ← top_le_preimage_comp] using this

theorem isHolTo_comp {B : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) {C : Set W} (hC : IsOpen C) {β : W → V}
    (hβ : DifferentiableOn ℂ β C) (hm : Set.MapsTo β C B) : IsHolTo C (fun w => y (β w)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, h2.comp (hβ.mono fun w hw => hw.1) fun w hw => ⟨hm hw.1, hw.2⟩⟩
  have := hβ.continuousOn.isOpen_inter_preimage hC h1
  convert this using 1
  ext w
  exact ⟨fun hw => ⟨hw.1, hm hw.1, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩

theorem isHolTo_congr {B : Set V} {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (e : ∀ b ∈ B, y' b = y b) :
    IsHolTo B y' := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [e b hb]
  rw [this]
  exact ⟨h1, h2.congr fun b hb => by rw [e b hb.1]⟩

theorem isHolTo_mono {B C : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (hC : IsOpen C) (hCB : C ⊆ B) :
    IsHolTo C y :=
  isHolTo_comp (β := id) h hC differentiableOn_id hCB

end Hol

section Grp

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Q : Type} [Group Q]

theorem hom_zero {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) : e 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem hom_sub_eq_one {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) {z w : A} :
    e (z - w) = 1 ↔ e z = e w := by
  have := h (z - w) w
  rw [sub_add_cancel] at this
  rw [this, mul_eq_right]

theorem hom_nsmul {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) (z : A) (n : ℕ) :
    e (n • z) = e z ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, hom_zero h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

def homKer {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) : AddSubgroup A :=
  (AddMonoidHom.mk' (G := Additive Q) (fun z => Additive.ofMul (e z)) fun z w => congrArg _ (h z w)).ker

theorem mem_homKer {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) {z : A} :
    z ∈ homKer h ↔ e z = 1 := Iff.rfl

theorem isDiscrete_of_norm {K : AddSubgroup W} {r : ℝ} (hr : 0 < r) (h : ∀ z ∈ K, ‖z‖ < r → z = 0) :
    IsDiscrete (K : Set W) := by
  have : DiscreteTopology K := DiscreteTopology.of_forall_le_norm (E := K) hr fun x hx =>
    not_lt.1 fun h' => hx (Subtype.ext (h x x.2 h'))
  exact DiscreteTopology.isDiscrete

theorem linear_lift_unique {e : W → Q} (h : ∀ z w, e (z + w) = e z * e w) {r : ℝ} (hr : 0 < r)
    (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {L L' : V →ₗ[ℂ] W} (hL : ∀ z, e (L z) = e (L' z)) : L = L' := by
  have := realLinear_eq_of_sub_mem_discrete (Γ := homKer h) (isDiscrete_of_norm hr fun z hz hn => hk z hn hz)
    (L := L.restrictScalars ℝ) (L' := L'.restrictScalars ℝ) fun x => (hom_sub_eq_one h).2 (hL x)
  ext z
  exact DFunLike.congr_fun this z

theorem fderiv_lift {x : V → Q} {e : W → Q} (hx : ∀ z w, x (z + w) = x z * x w) (h : ∀ z w, e (z + w) = e z * e w)
    (hs : Function.Surjective e) {r : ℝ} (hr : 0 < r) (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {ζ : V → W}
    (hd : DifferentiableAt ℂ ζ 0) (hζ : ∀ᶠ z in 𝓝 0, e (ζ z) = x z) (z : V) : e (fderiv ℂ ζ 0 z) = x z := by
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := fun a b => by
      obtain ⟨a, rfl⟩ := hs a
      obtain ⟨b, rfl⟩ := hs b
      rw [← h, ← h, add_comm] }
  exact apply_fderiv_eq_of_germ (𝕜 := ℂ) (A := Additive Q)
    (ex := AddMonoidHom.mk' (fun z => Additive.ofMul (x z)) fun z w => congrArg _ (hx z w))
    (ex' := AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => congrArg _ (h z w))
    (isDiscrete_of_norm hr fun z hz hn => hk z hn hz) hd hζ z

theorem exists_linearEquiv_lift [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {x : V → Q} {e : W → Q}
    (hx : ∀ z w, x (z + w) = x z * x w) (h : ∀ z w, e (z + w) = e z * e w) (hsx : Function.Surjective x)
    (hs : Function.Surjective e) (hkx : IsDiscrete {z | x z = 1})
    {r : ℝ} (hr : 0 < r) (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {ζ : V → W}
    (hd : DifferentiableAt ℂ ζ 0) (hζ : ∀ᶠ z in 𝓝 0, e (ζ z) = x z) : ∃ L : V ≃L[ℂ] W, ∀ z, e (L z) = x z := by
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := fun a b => by
      obtain ⟨a, rfl⟩ := hs a
      obtain ⟨b, rfl⟩ := hs b
      rw [← h, ← h, add_comm] }
  obtain ⟨L, hL, -⟩ := existsUnique_linearEquiv_of_uniformisations (𝕜 := ℂ) (A := Additive Q)
    (ex := AddMonoidHom.mk' (fun z => Additive.ofMul (x z)) fun z w => congrArg _ (hx z w))
    (ex' := AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => congrArg _ (h z w))
    hkx (isDiscrete_of_norm hr fun z hz hn => hk z hn hz) (fun q _ => hsx q) hd hζ
  exact ⟨L, hL.1⟩

theorem eq_zero_of_small {T : Type} [TopologicalSpace T] {B : Set T} (hB : IsPreconnected B) {d : T → W}
    (hd : ContinuousOn d B) {r : ℝ} (hr : 0 < r) (h : ∀ b ∈ B, ‖d b‖ < r → d b = 0) {b₀ : T} (hb₀ : b₀ ∈ B)
    (h0 : d b₀ = 0) : ∀ b ∈ B, d b = 0 := by
  intro b hb
  refine h b hb (not_le.1 fun hle => ?_)
  obtain ⟨c, hc, hc'⟩ := hB.intermediate_value hb₀ hb hd.norm
    (show r / 2 ∈ Set.Icc ‖d b₀‖ ‖d b‖ from ⟨by rw [h0, norm_zero]; positivity, by linarith⟩)
  have hc'' : ‖d c‖ = r / 2 := hc'
  have := h c hc (by linarith)
  rw [this, norm_zero] at hc''
  linarith

end Grp

section Exp

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

def IsExp (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)

def HasLifts (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X))
    (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) : Prop :=
  ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G)
    (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B →
    IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ →
    ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w

omit [GrpObj G] in
theorem HasLifts.lift {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} (h : HasLifts B y e) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {W : Set V} {β : V → (Fin m → ℂ)} (x : ∀ w, Over.mk (y (β w)) ⟶ G)
    {w₀ : V} {z₀ : Fin g → ℂ} (hW : IsOpen W) (hw₀ : w₀ ∈ W) (hβ : DifferentiableOn ℂ β W)
    (hm : Set.MapsTo β W B) (hx : IsHolTo W (fun w => (x w).left)) (h0 : e (β w₀) z₀ = x w₀) :
    ∃ ζ : V → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w := by
  let φ : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨u₀, rfl⟩ := φ.symm.surjective w₀
  have hW' : IsOpen (φ.symm ⁻¹' W) := hW.preimage φ.symm.continuous
  obtain ⟨ζ, h1, h2, h3⟩ := h _ (φ.symm ⁻¹' W) (fun u => β (φ.symm u)) (fun u => x (φ.symm u)) u₀ z₀ hW' hw₀
    (hβ.comp φ.symm.differentiableOn fun _ hu => hu) (fun _ hu => hm hu)
    (isHolTo_comp hx hW' φ.symm.differentiableOn fun _ hu => hu) h0
  refine ⟨fun w => ζ (φ w), by simpa using h1, ?_, ?_⟩
  · exact AnalyticAt.comp_of_eq h2 (φ.toContinuousLinearMap.analyticAt (φ.symm u₀)) (by simp)
  · have ht : map φ.symm (𝓝 u₀) = 𝓝 (φ.symm u₀) := φ.symm.toHomeomorph.map_nhds_eq u₀
    rw [← ht, eventually_map]
    simpa only [φ.apply_symm_apply] using h3

theorem isDerivAt0_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (h z)) w v ↔ IsDerivAt0 e (h w) v := by
  have key : ∀ (U : X.Opens) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (h z)) U f) 0 w =
      fderiv ℂ (fun z => valAt' (e z) U f) 0 (h w) := fun U f => by
    have := h.comp_right_fderiv (f := fun z => valAt' (e z) U f) (x := 0)
    rw [map_zero] at this
    exact DFunLike.congr_fun this w
  simp only [IsDerivAt0, key, map_zero]

theorem IsExp.comp {y : Sp ℂ ⟶ X} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp y e)
    (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : IsExp y (fun z => e (h z)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := he
  refine ⟨fun z w => by simp only [map_add, h1], h2.comp h.surjective,
    isHolTo_comp h3 isOpen_univ h.differentiableOn (Set.mapsTo_univ _ _), fun w => ?_, fun v hv => ?_⟩
  · simpa only [isDerivAt0_comp (e := fun z => (e z).left)] using h4 (h w)
  · simp only [isDerivAt0_comp (e := fun z => (e z).left)]
    obtain ⟨w, hw, hu⟩ := h5 v (by simpa only [map_zero] using hv)
    exact ⟨h.symm w, by simpa using hw, fun w' hw' => by rw [← hu _ hw', h.symm_apply_apply]⟩

theorem one_left (y : Sp ℂ ⟶ X) : (1 : Over.mk y ⟶ G).left = y ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem eq_one_of_mem_range [IsSeparated G.hom] {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G)
    (hx : x.left (default : PrimeSpectrum ℂ) ∈ Set.range η[G].left) : x = 1 := by
  have hw : η[G].left ≫ G.hom = 𝟙 _ := Over.w η[G]
  haveI : IsClosedImmersion (η[G].left ≫ G.hom) := hw ▸ inferInstance
  haveI : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  haveI : IsReduced (Over.mk y).left := inferInstanceAs (IsReduced (Sp ℂ))
  haveI : Surjective (pullback.fst x.left η[G].left) := ⟨fun p => by
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst this
    change _ ∈ Set.range _
    rw [Scheme.Pullback.range_fst]
    exact hx⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst x.left η[G].left)
  have e : x.left = (inv (pullback.fst x.left η[G].left) ≫ pullback.snd _ _) ≫ η[G].left := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have e' : inv (pullback.fst x.left η[G].left) ≫ pullback.snd _ _ = y := by
    have := Over.w x
    rw [e, Category.assoc, hw] at this
    exact (Category.comp_id _).symm.trans this
  rw [e'] at e
  exact Over.OverMorphism.ext (e.trans (one_left y).symm)

theorem isOpen_ne_one [IsSeparated G.hom] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} {x : ∀ b, Over.mk (y b) ⟶ G} (hx : IsHolTo B (fun b => (x b).left)) :
    IsOpen {b ∈ B | x b ≠ 1} := by
  have hw : η[G].left ≫ G.hom = 𝟙 _ := Over.w η[G]
  haveI : IsClosedImmersion (η[G].left ≫ G.hom) := hw ▸ inferInstance
  haveI : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  let U : G.left.Opens := ⟨(Set.range η[G].left)ᶜ, η[G].left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  convert (hx U 0).1 using 3 with b
  refine and_congr_right fun _ => ?_
  rw [top_le_preimage_iff_mem]
  refine not_congr ⟨fun h => ?_, eq_one_of_mem_range _⟩
  beta_reduce
  rw [h, one_left]
  exact ⟨y b (default : PrimeSpectrum ℂ), rfl⟩

end Exp

end

end GlobalTheory.LocLift
