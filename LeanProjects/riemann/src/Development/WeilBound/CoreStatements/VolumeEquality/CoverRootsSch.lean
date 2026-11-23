import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed

noncomputable section

namespace SheetDecomposition.CovSch

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {X Y : Scheme.{0}} {F : Type} [Field F]

theorem top_le_iff (x : Sp F ⟶ X) (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ centre x ∈ U :=
  ⟨fun h => h (show IsLocalRing.closedPoint F ∈ (⊤ : (Sp F).Opens) from trivial),
    fun h => (Scheme.preimage_eq_top_of_closedPoint_mem x h).ge⟩

def val (x : Sp F ⟶ X) (U : X.Opens) (h : centre x ∈ U) : Γ(X, U) →+* F :=
  (Scheme.stalkClosedPointTo x).hom.comp (X.presheaf.germ U (centre x) h).hom

theorem val_eq (x : Sp F ⟶ X) (U : X.Opens) (h : centre x ∈ U) (s : Γ(X, U)) :
    val x U h s = (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((x.appLE U ⊤ ((top_le_iff x U).2 h)).hom s) := by
  have := congrArg (fun φ => φ.hom s) (Scheme.germ_stalkClosedPointTo x U h)
  exact this

theorem valAt'_eq (p : Sp ℂ ⟶ X) (U : X.Opens) (h : centre p ∈ U) (s : Γ(X, U)) : valAt' p U s = val p U h s := by
  rw [val_eq, valAt', dif_pos ((top_le_iff p U).2 h)]
  rfl

theorem val_res (x : Sp F ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : centre x ∈ V) (s : Γ(X, U)) :
    val x V h ((X.presheaf.map (homOfLE hVU).op).hom s) = val x U (hVU h) s := by
  have := X.presheaf.germ_res_apply (homOfLE hVU) (centre x) h s
  exact congrArg (Scheme.stalkClosedPointTo x).hom this

theorem val_comp (x : Sp F ⟶ X) (f : X ⟶ Y) (U : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ U) (h : centre x ∈ W)
    (h' : centre (x ≫ f) ∈ U) (s : Γ(Y, U)) : val x W h ((f.appLE U W hW).hom s) = val (x ≫ f) U h' s := by
  rw [val_eq, val_eq, ← Scheme.Hom.appLE_comp_appLE x f U W ⊤ hW ((top_le_iff x W).2 h)]
  rfl

theorem val_congr {x x' : Sp F ⟶ X} (e : x = x') (U : X.Opens) (h : centre x ∈ U) (h' : centre x' ∈ U)
    (s : Γ(X, U)) : val x U h s = val x' U h' s := by
  subst e
  rfl

theorem val_spMap {F' : Type} [Field F'] (i : F →+* F') (x : Sp F ⟶ X) (U : X.Opens) (h : centre x ∈ U)
    (h' : centre (spMap i ≫ x) ∈ U) (s : Γ(X, U)) : val (spMap i ≫ x) U h' s = i (val x U h s) := by
  rw [val_eq, val_eq, ← Scheme.Hom.appLE_comp_appLE (spMap i) x U ⊤ ⊤ ((top_le_iff x U).2 h) le_rfl]
  have := congrArg (fun φ => φ.hom ((x.appLE U ⊤ ((top_le_iff x U).2 h)).hom s))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom i))
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
  exact this

theorem centre_spMap {F' : Type} [Field F'] (i : F →+* F') (x : Sp F ⟶ X) : centre (spMap i ≫ x) = centre x := by
  have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  show x (spMap i _) = x _
  congr 1
  exact Subsingleton.elim _ _

theorem eq_of_val {U : X.Opens} (hU : IsAffineOpen U) {x x' : Sp F ⟶ X} (h : centre x ∈ U) (h' : centre x' ∈ U)
    (e : ∀ s, val x U h s = val x' U h' s) : x = x' := by
  have e1 : x.appLE U ⊤ ((top_le_iff x U).2 h) = x'.appLE U ⊤ ((top_le_iff x' U).2 h') := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of F)).hom]
    ext s
    have := e s
    rw [val_eq, val_eq] at this
    exact this
  have a := hU.SpecMap_appLE_fromSpec x (isAffineOpen_top _) ((top_le_iff x U).2 h)
  have b := hU.SpecMap_appLE_fromSpec x' (isAffineOpen_top _) ((top_le_iff x' U).2 h')
  rw [e1, b, IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem exists_of_hom {U : X.Opens} (hU : IsAffineOpen U) (χ : Γ(X, U) →+* F) :
    ∃ (x : Sp F ⟶ X) (h : centre x ∈ U), ∀ s, val x U h s = χ s := by
  let x : Sp F ⟶ X := Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec
  have h : centre x ∈ U := by
    have : centre x ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rwa [hU.range_fromSpec] at this
  refine ⟨x, h, fun s => ?_⟩
  rw [val_eq, ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom χ)) hU.fromSpec U ⊤ ⊤
    hU.fromSpec_preimage_self.ge le_rfl]
  have e1 : hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ ((Spec Γ(X, U)).presheaf.map_id _)).trans (Category.comp_id _)
  rw [e1]
  have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom s))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ))
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
  refine this.trans ?_
  exact congrArg χ (congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id)

variable {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_germ' (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U) (hg : centre ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq s) = val ξ U hg s := RegAtRing.genMap_germ q U hq hg s

theorem val_injective (hξ : IsCptGen ξ) (U : X.Opens) (hg : centre ξ ∈ U) (hU : ∀ q ∈ U, genPt ξ ⤳ q) :
    Function.Injective (val ξ U hg) := by
  intro s s' e
  refine TopCat.Presheaf.section_ext X.sheaf U s s' fun q hq => ?_
  apply hξ.inj ⟨q, hU q hq⟩
  exact (genMap_germ' ⟨q, hU q hq⟩ U hq hg s).trans (e.trans (genMap_germ' ⟨q, hU q hq⟩ U hq hg s').symm)

theorem exists_open (hξ : IsCptGen ξ) (T : Set Ω) (hT : T.Finite) (U₁ : X.Opens) (h₁ : centre ξ ∈ U₁) :
    ∃ (U : X.Opens) (h : centre ξ ∈ U), U ≤ U₁ ∧ T ⊆ Set.range (val ξ U h) := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨U₁, h₁, le_rfl, Set.empty_subset _⟩
  | @insert a T _ _ ih =>
    obtain ⟨U, h, hU, hT⟩ := ih
    obtain ⟨g, rfl⟩ := hξ.bij.2 a
    obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq g
    refine ⟨U ⊓ V, ⟨h, hV⟩, inf_le_left.trans hU, Set.insert_subset ⟨_, val_res ξ inf_le_right _ s⟩ ?_⟩
    intro b hb
    obtain ⟨s', rfl⟩ := hT hb
    exact ⟨_, val_res ξ inf_le_left _ s'⟩

variable {z : Sp ℂ ⟶ X}

theorem valAt_sec (hz : genPt ξ ⤳ centre z) (U : X.Opens) (h : centre z ∈ U) (hg : centre ξ ∈ U) (s : Γ(X, U)) :
    ValAt ξ z (val ξ U hg s) (val z U h s) :=
  ⟨hz, X.presheaf.germ U (centre z) h s, genMap_germ' ⟨centre z, hz⟩ U h hg s, rfl⟩

theorem v_mul {a b : Ω} {r t : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z b t) : ValAt ξ z (a * b) (r * t) := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', rfl, rfl⟩ := hb
  exact ⟨h, s * s', map_mul _ _ _, map_mul _ _ _⟩

theorem v_unique (hξ : IsCptGen ξ) {a : Ω} {r t : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z a t) : r = t := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', e, rfl⟩ := hb
  rw [hξ.inj _ e]

theorem v_inv {a : Ω} {r : ℂ} (ha : ValAt ξ z a r) (hr : r ≠ 0) : a ≠ 0 ∧ ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  have hs : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.mpr hr)
  obtain ⟨u, rfl⟩ := hs
  exact ⟨(u.isUnit.map (genMap ξ ⟨centre z, h⟩)).ne_zero, h,
    ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)),
    map_units_inv (genMap ξ ⟨centre z, h⟩) u, map_units_inv (Scheme.stalkClosedPointTo z).hom u⟩

theorem exists_frac {U : X.Opens} (hU : IsAffineOpen U) (x : Sp F ⟶ X) (h : centre x ∈ U)
    (g : X.presheaf.stalk (centre x)) : ∃ a b : Γ(X, U), val x U h b ≠ 0 ∧
      g * X.presheaf.germ U (centre x) h b = X.presheaf.germ U (centre x) h a := by
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := U) ⟨centre x, h⟩
  have := hU.isLocalization_stalk ⟨centre x, h⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨centre x, h⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk (centre x)) g
  have hu := IsLocalization.map_units (M := (hU.primeIdealOf ⟨centre x, h⟩).asIdeal.primeCompl)
    (X.presheaf.stalk (centre x)) s
  exact ⟨r, s.1, (hu.map (Scheme.stalkClosedPointTo x).hom).ne_zero, hrs⟩

variable {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω}

theorem coordsAt_of_val (c : ∀ k, J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) {w : (Σ k, J k) → ℂ}
    (hw : ∀ s, ValAt ξ z (y s / y ⟨s.1, c s.1⟩) (w s)) (hw1 : ∀ k, w ⟨k, c k⟩ = 1) : CoordsAt ξ y z w := by
  refine ⟨fun k => ⟨c k, by rw [hw1]; exact isUnit_one⟩, fun k c' hu => ?_⟩
  obtain ⟨h0, hr⟩ := v_inv (hw ⟨k, c'⟩) hu.ne_zero
  have hy' : y ⟨k, c'⟩ ≠ 0 := fun e => h0 (by rw [e, zero_div])
  refine ⟨hy', fun i => ⟨w ⟨k, i⟩ * (w ⟨k, c'⟩)⁻¹, ?_, ?_⟩⟩
  · have h1 := v_mul (hw ⟨k, i⟩) hr
    have h2 : y ⟨k, i⟩ / y ⟨k, c k⟩ * (y ⟨k, c'⟩ / y ⟨k, c k⟩)⁻¹ = y ⟨k, i⟩ / y ⟨k, c'⟩ := by
      have := hy k
      field_simp
    exact h2 ▸ h1
  · rw [inv_mul_cancel_right₀ hu.ne_zero]

theorem val_of_coordsAt (c : ∀ k, J k) {w : (Σ k, J k) → ℂ} (hw : CoordsAt ξ y z w) (hw1 : ∀ k, w ⟨k, c k⟩ = 1)
    (s : Σ k, J k) : ValAt ξ z (y s / y ⟨s.1, c s.1⟩) (w s) := by
  obtain ⟨k, i⟩ := s
  obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (by rw [hw1]; exact isUnit_one)).2 i
  rw [hw1, mul_one] at e
  exact e ▸ hr

end SheetDecomposition.CovSch
