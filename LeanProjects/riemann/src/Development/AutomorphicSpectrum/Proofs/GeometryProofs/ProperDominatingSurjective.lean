import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

section Surj

variable {X : Scheme.{0}}

theorem germ_closedPoint_eq_appLE {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X) (U : X.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp only [Scheme.Hom.appLE]
  rfl

theorem val_comp_spec {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S] (φ : R ⟶ S) (z : Spec R ⟶ X)
    (w : Spec S ⟶ X) (hw : Spec.map φ ≫ z = w) (U : X.Opens)
    (h1 : z (IsLocalRing.closedPoint R) ∈ U) (h2 : w (IsLocalRing.closedPoint S) ∈ U) (t : Γ(X, U)) :
    φ.hom ((Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ U _ h1).hom t)) =
      (Scheme.stalkClosedPointTo w).hom ((X.presheaf.germ U _ h2).hom t) := by
  subst hw
  have key : (Spec.map φ ≫ z).appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem _ h2).ge ≫
      (Scheme.ΓSpecIso S).hom =
      z.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem z h1).ge ≫ (Scheme.ΓSpecIso R).hom ≫ φ := by
    have e₂ : (⊤ : (Spec S).Opens) ≤ (Spec.map φ) ⁻¹ᵁ ⊤ := by simp
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) z U ⊤ ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem z h1).ge e₂,
      Category.assoc, ← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have e1 := congrArg (fun g => (g ≫ φ).hom t) (germ_closedPoint_eq_appLE z U h1)
  have e2 := congrArg (fun g => g.hom t) (germ_closedPoint_eq_appLE (Spec.map φ ≫ z) U h2)
  have e3 := congrArg (fun g => g.hom t) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1 e2 e3
  rw [e1, e2, e3]

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Ω' : Type} [Field Ω']

def DomAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω') (A : ValuationSubring Ω') (p : Cpt ξ) : Prop :=
  ∃ ν : X.presheaf.stalk p.1 →+* A, IsLocalHom ν ∧ ∀ s, (ν s : Ω') = i (genMap ξ p s)

theorem DomAt.inv_mem {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p : Cpt ξ} (h : DomAt ξ i A p) {a : Ω}
    (h0 : a ≠ 0) (ha : a ∈ regAt ξ p) (hi : i a⁻¹ ∈ A) : a⁻¹ ∈ regAt ξ p := by
  obtain ⟨ν, hloc, hν⟩ := h
  obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
  have hu : IsUnit (ν s) := by
    refine IsUnit.of_mul_eq_one (a := ν s) ⟨i (genMap ξ p s)⁻¹, hi⟩ ?_
    apply Subtype.ext
    show (ν s : Ω') * i (genMap ξ p s)⁻¹ = 1
    rw [hν s, ← map_mul, mul_inv_cancel₀ h0, map_one]
  have hs : IsUnit s := (isUnit_map_iff ν s).mp hu
  refine RingHom.mem_range.mpr ⟨↑hs.unit⁻¹, ?_⟩
  rw [map_units_inv, IsUnit.unit_spec]

theorem genMap_germ (r : Cpt ξ) {U : X.Opens} (hr : r.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ r ((X.presheaf.germ U r.1 hr).hom t) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) (r.2.mem_open U.isOpen hr)).hom t) := by
  have e := congrArg (fun g => g.hom t) (X.presheaf.germ_stalkSpecializes hr r.2)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes r.2).hom ((X.presheaf.germ U r.1 hr).hom t)) = _
  rw [e]

theorem DomAt.eq_of_mem_affine {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p p' : Cpt ξ} (h : DomAt ξ i A p)
    (h' : DomAt ξ i A p') {U : X.Opens} (hU : IsAffineOpen U) (hp : p.1 ∈ U) (hp' : p'.1 ∈ U) : p.1 = p'.1 := by
  obtain ⟨ν, hν1, hν⟩ := h
  obtain ⟨ν', hν1', hν'⟩ := h'
  have key : ∀ b : Γ(X, U), p.1 ∈ X.basicOpen b ↔ p'.1 ∈ X.basicOpen b := by
    intro b
    have e : ν ((X.presheaf.germ U p.1 hp).hom b) = ν' ((X.presheaf.germ U p'.1 hp').hom b) := by
      apply Subtype.ext
      simp only [hν, hν', genMap_germ]
    rw [X.mem_basicOpen b p.1 hp, X.mem_basicOpen b p'.1 hp', ← isUnit_map_iff ν, ← isUnit_map_iff ν', e]
  have sp : ∀ {a c : X}, a ∈ U → c ∈ U → (∀ b : Γ(X, U), a ∈ X.basicOpen b → c ∈ X.basicOpen b) → c ⤳ a := by
    intro a c ha hc hab
    rw [specializes_iff_forall_open]
    intro s hs has
    obtain ⟨b, hb, hab'⟩ := hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨a, has⟩ ha
    exact hb (hab b hab')
  exact ((sp hp' hp (fun b => (key b).2)).antisymm (sp hp hp' (fun b => (key b).1))).eq

theorem domAt_of_spec {i : Ω →+* Ω'} {A : ValuationSubring Ω'} (z : Spec (CommRingCat.of A) ⟶ X)
    (hz : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ z = Spec.map (CommRingCat.ofHom i) ≫ ξ)
    (h : genPt ξ ⤳ z (IsLocalRing.closedPoint A)) :
    DomAt ξ i A ⟨z (IsLocalRing.closedPoint A), h⟩ := by
  refine ⟨(Scheme.stalkClosedPointTo z).hom, inferInstance, fun s => ?_⟩
  obtain ⟨U, hU, t, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg : genPt ξ ∈ U := h.mem_open U.isOpen hU
  have hw : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') ∈ U := by
    rw [← hz]
    exact ((IsLocalRing.specializes_closedPoint _).map z.continuous).mem_open U.isOpen hU
  have e1 := val_comp_spec (CommRingCat.ofHom (algebraMap A Ω')) z _ hz U hU hw t
  have e2 := val_comp_spec (CommRingCat.ofHom i) ξ _ rfl U hg hw t
  have e3 := congrArg i (genMap_germ (ξ := ξ) ⟨z (IsLocalRing.closedPoint A), h⟩ hU t)
  exact e1.trans (e2.symm.trans e3.symm)

private theorem exists_domAt_of_injective_genMap (i : Ω →+* Ω') (p : Cpt ξ) (hinj : Function.Injective (genMap ξ p)) :
    ∃ A : ValuationSubring Ω', DomAt ξ i A p := by
  let g : X.presheaf.stalk p.1 →+* Ω' := i.comp (genMap ξ p)
  have hg : Function.Injective g := i.injective.comp hinj
  obtain ⟨A, hA⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range g)
  obtain ⟨hle, hloc⟩ := hA
  have hmem : ∀ s, g s ∈ A.toSubring := fun s => hle ⟨s, rfl⟩
  refine ⟨A, g.codRestrict A.toSubring hmem, ⟨fun s hs => ?_⟩, fun s => rfl⟩
  obtain ⟨v, hv⟩ := hs.exists_right_inv
  have hv' : g s * (v : Ω') = 1 := congrArg Subtype.val hv
  let y : (LocalSubring.range g).toSubring := ⟨g s, ⟨s, rfl⟩⟩
  have hy : IsUnit y := by
    apply hloc.map_nonunit
    refine IsUnit.of_mul_eq_one ⟨v, v.2⟩ ?_
    exact Subtype.ext hv'
  obtain ⟨w, hw⟩ := hy.exists_right_inv
  obtain ⟨s', hs'⟩ := w.2
  refine IsUnit.of_mul_eq_one s' ?_
  apply hg
  rw [map_mul, map_one, hs']
  exact congrArg Subtype.val hw

private theorem inChart_of_domAt_of_div_mem {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p : Cpt ξ} (h : DomAt ξ i A p)
    {κ : Type} {x : κ → Ω} {c : κ} (hxc : x c ≠ 0) (hA : ∀ c', i (x c' / x c) ∈ A) {c'' : κ}
    (h'' : InChart ξ x c'' p) : InChart ξ x c p := by
  refine ⟨hxc, fun c' => ?_⟩
  have hc'' : x c'' ≠ 0 := h''.1
  have h1 : x c / x c'' ∈ regAt ξ p := h''.2 c
  have h0 : x c / x c'' ≠ 0 := div_ne_zero hxc hc''
  have h2 : (x c / x c'')⁻¹ ∈ regAt ξ p := h.inv_mem h0 h1 (by rw [inv_div]; exact hA c'')
  have e : x c' / x c = (x c' / x c'') * (x c / x c'')⁻¹ := by
    rw [inv_div, div_mul_div_cancel₀ hc'']
  rw [e]
  exact mul_mem (h''.2 c') h2

private theorem div_mem_of_valuation_le {K : Type} [Field K] (A : ValuationSubring K) {a b : K} (hb : b ≠ 0)
    (h : A.valuation a ≤ A.valuation b) : a / b ∈ A := by
  rw [← A.valuation_le_one_iff, map_div₀]
  have hb' : A.valuation b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  exact div_le_one_of_le₀ h zero_le'

theorem surjective_of_dominates (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type)
    [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (s' : X' ⟶ Spec (CommRingCat.of ℤ)) (f : X' ⟶ X) (i : Ω →+* Ω') (hc : CoordTie ℤ ξ x)
    (hg : ∀ q : X, genPt ξ ⤳ q) (hp : IsProper s') (hd : Dominates ξ' ξ f i) : Function.Surjective f := by
  intro q
  obtain ⟨A, hdom⟩ := exists_domAt_of_injective_genMap i ⟨q, hg q⟩ (hc.gen.inj ⟨q, hg q⟩)
  have hex : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s' := by
    rw [← UniversallyClosed.eq_valuativeCriterion]
    infer_instance
  let S : ValuativeCommSq s' :=
    { R := A, K := Ω', i₁ := ξ', i₂ := specZIsTerminal.from _, commSq := ⟨specZIsTerminal.hom_ext _ _⟩ }
  obtain ⟨⟨l, hl1, -⟩⟩ := (hex.1 S).exists_lift
  have hl : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ l = ξ' := hl1
  have hz : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ (l ≫ f) = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
    rw [← Category.assoc, hl]
    exact hd
  have hdom' := domAt_of_spec (i := i) (A := A) (l ≫ f) hz (hg _)
  obtain ⟨c₁, hc₁⟩ := hc.cover ⟨q, hg q⟩
  have : Nonempty κ := ⟨c₁⟩
  obtain ⟨c, hcmax⟩ := Finite.exists_max (fun c => A.valuation (i (x c)))
  have hxc : x c ≠ 0 := by
    intro h0
    have h1 := hcmax c₁
    simp only [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hc₁.1 ((map_eq_zero i).1 h1)
  have hA : ∀ c', i (x c' / x c) ∈ A := fun c' => by
    rw [map_div₀]
    exact div_mem_of_valuation_le A ((map_ne_zero i).2 hxc) (hcmax c')
  obtain ⟨U, hUaff, hUmem⟩ := hc.affine c hxc
  have hq : q ∈ U := (hUmem q).2 ⟨hg q, inChart_of_domAt_of_div_mem hdom hxc hA hc₁⟩
  obtain ⟨c₂, hc₂⟩ := hc.cover ⟨(l ≫ f) (IsLocalRing.closedPoint A), hg _⟩
  have hq' : (l ≫ f) (IsLocalRing.closedPoint A) ∈ U :=
    (hUmem _).2 ⟨hg _, inChart_of_domAt_of_div_mem hdom' hxc hA hc₂⟩
  have e := DomAt.eq_of_mem_affine hdom hdom' hUaff hq hq'
  exact ⟨l (IsLocalRing.closedPoint A), e.symm⟩

end Surj
end GlobalTheory.CompanionTheory.Ar.FlagBun
