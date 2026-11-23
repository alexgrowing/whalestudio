import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOfTest

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

theorem factor {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : IsCptGen ξ) (ξ' : Spec (CommRingCat.of Ω') ⟶ X) (e : genPt ξ' = genPt ξ) :
    ∃ i : Ω →+* Ω', ξ' = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
  have key : ∀ (x x' : X) (_ : x' = x) (φ : X.presheaf.stalk x ⟶ CommRingCat.of Ω) [IsIso φ]
      (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of Ω'), ∃ i : Ω →+* Ω',
      Spec.map φ' ≫ X.fromSpecStalk x' = Spec.map (CommRingCat.ofHom i) ≫ Spec.map φ ≫ X.fromSpecStalk x := by
    intro x x' e φ _ φ'
    subst e
    refine ⟨(inv φ ≫ φ').hom, ?_⟩
    rw [CommRingCat.ofHom_hom, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id_assoc]
  haveI : IsIso (Scheme.stalkClosedPointTo ξ) := (ConcreteCategory.isIso_iff_bijective _).2 h.bij
  obtain ⟨i, hi⟩ := @key _ _ e (Scheme.stalkClosedPointTo ξ) this (Scheme.stalkClosedPointTo ξ')
  refine ⟨i, ?_⟩
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ').symm.trans (hi.trans
    (congrArg (Spec.map (CommRingCat.ofHom i) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))

theorem spec_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

def SplitOver {O F : Type} [CommRing O] [Field F] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of O))
    (β : O →+* F) : Prop :=
  ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (cst : F →+* Ω), IsCptGen ξ →
    ξ ≫ s = Spec.map (CommRingCat.ofHom (cst.comp β)) → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ cst.range

theorem isCptGen_id (K : Type) [Field K] : IsCptGen (𝟙 (Spec (CommRingCat.of K))) := by
  have hb : Function.Bijective (Scheme.stalkClosedPointTo (𝟙 (Spec (CommRingCat.of K)))).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 (by
      unfold Scheme.stalkClosedPointTo
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (by erw [Scheme.Hom.stalkMap_id]; exact IsIso.id _) inferInstance)
  exact ⟨hb, fun p => hb.1.comp (CptInh.spec_inj _ p.2)⟩

theorem splitOver_field (F K : Type) [Field F] [Field K] (j : F →+* K) :
    SplitOver (Spec.map (CommRingCat.ofHom j)) (RingHom.id F) ↔ ∀ a : K, IsAlgebraic ℤ a → a ∈ j.range := by
  constructor
  · intro h a ha
    exact h K (𝟙 _) j (isCptGen_id K) (by simp) a ha
  · intro h Ω _ ξ cst hξ hs a ha
    obtain ⟨i, hi⟩ := factor ξ hξ (𝟙 _) (Subsingleton.elim (α := PrimeSpectrum K) _ _)
    have e : i.comp cst = j := by
      apply spec_inj
      have : Spec.map (CommRingCat.ofHom j) = Spec.map (CommRingCat.ofHom i) ≫ ξ ≫ Spec.map (CommRingCat.ofHom j) := by
        rw [← Category.assoc, ← hi, Category.id_comp]
      rw [this, hs, ← Spec.map_comp]
      rfl
    obtain ⟨b, hb⟩ := h (i a) (ha.algHom i.toIntAlgHom)
    refine ⟨b, i.injective ?_⟩
    rw [← hb, ← e]; rfl

theorem splitOver_self (F : Type) [Field F] :
    SplitOver (Spec.map (CommRingCat.ofHom (RingHom.id F))) (RingHom.id F) :=
  (splitOver_field F F _).2 fun a _ => ⟨a, rfl⟩

theorem not_splitOver_complex : ¬ SplitOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) (RingHom.id ℚ) := by
  rw [splitOver_field]
  intro h
  have hI : IsAlgebraic ℤ Complex.I := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_, by simp⟩
    exact (Polynomial.monic_X_pow_add_C (1 : ℤ) two_ne_zero).ne_zero
  obtain ⟨b, hb⟩ := h _ hI
  have := congrArg Complex.im hb
  simp at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem splitComps_iff {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    SplitComps Y ↔ SplitOver Y.s β := Iff.rfl

theorem splitComps_of_isTowerOf {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {T : Top.RootTower (CMType H) (D.p + D.q)} (h : IsTowerOf Y T) : SplitComps Y := by
  obtain ⟨o, -⟩ := h
  haveI := c.fin
  haveI : NumberField c.F := {}
  intro Ω _ ξ cst hξ hs a ha
  obtain ⟨k, hk⟩ := o.comp_onto (genPt ξ) (CptInh.nogen ξ hξ)
  obtain ⟨i, hi⟩ := factor ξ hξ (o.Fx k).ξf hk
  let R := o.Or 0 k
  have e0 : ((R.g.comp i).comp cst).comp (algebraMap (𝓞 c.F) c.F) = R.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    apply spec_inj
    have h1 := R.𝔐.cst_over
    rw [← Category.assoc, R.g_over, hi, Category.assoc, Category.assoc, hs] at h1
    refine Eq.trans ?_ h1
    change _ = Spec.map (CommRingCat.ofHom R.g) ≫ Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom _)
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e : (R.g.comp i).comp cst = R.𝔐.cst := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  obtain ⟨b, hb⟩ := R.g_const (i a) (ha.algHom i.toIntAlgHom)
  refine ⟨b, (R.g.comp i).injective ?_⟩
  rw [← e] at hb
  exact hb

theorem sign_pos_of_isTowerOf {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {T : Top.RootTower (CMType H) (D.p + D.q)} (h : IsTowerOf Y T) : 1 ≤ D.p ∧ 1 ≤ D.q ∧ Nonempty Y.X := by
  obtain ⟨o, -⟩ := h
  have h1 := T.j_pos
  have h2 := T.j_lt
  rw [o.j_eq] at h1 h2
  obtain ⟨k⟩ := T.neC
  exact ⟨h1, by omega, ⟨genPt (o.Fx k).ξf⟩⟩

section
variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem finrank_dual_Vgen (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H) :
    Module.finrank Ω (Module.Dual Ω (𝔐.Vgen s)) = labelRk D s := by
  obtain ⟨U, hU, b, hb, hf⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
  have hl := (hf _ trivial hU).1
  rw [Subspace.dual_finrank_eq]
  have : 𝔐.Vgen s = Submodule.span Ω (Set.range b) := hb.symm
  rw [this, finrank_span_eq_card hl, Fintype.card_fin]

theorem htOm_le (𝔐 : HodgeCpt Y S y) (n : ℕ) (q : Cpt 𝔐.ξ) : 𝔐.M.htOm 𝔐.t.PP.L n q ≤ 𝔐.M.omLat q :=
  Submodule.span_le.2 fun _ ⟨_, _, h⟩ => h.1

theorem omVB_empty (𝔐 : HodgeCpt Y ∅ y) : 𝔐.OmVB := fun _ hp => absurd hp (Finset.notMem_empty _)

end

theorem two_mem_S {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {T : Top.RootTower (CMType H) (D.p + D.q)}
    (o : TowerOrigin Y T) (B : ℕ) : 2 ∈ o.S B := (o.S_iff B 2).2 ⟨Nat.prime_two, Or.inr T.two_mem⟩

end GlobalTheory.CompanionTheory.Ar.TowerOfTest
