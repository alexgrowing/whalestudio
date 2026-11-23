import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompat

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChartSmooth

open GlobalTheory.CompanionTheory.Ar.ChartFin

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem mem_adjoin_iff {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q) (T : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {U : X.Opens}
    (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (h : genPt ξ ∈ U) (a : Ω) :
    a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ ∃ s : Γ(X, U), secVal ξ U h s = a := by
  rw [T.ring c hc a]
  constructor
  · intro H
    refine exists_secVal hall T.gen.inj U h a fun q hq => ?_
    obtain ⟨h', hi⟩ := (hU q).1 hq
    exact H _ hi
  · rintro ⟨s, rfl⟩ p hp
    have hq : p.1 ∈ U := (hU p.1).2 ⟨p.2, hp⟩
    exact ⟨_, genMap_germ ξ h hq p.2 s⟩

theorem exists_secEquiv {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q) (T : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {U : X.Opens}
    (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (h : genPt ξ ∈ U) :
    ∃ E : Γ(X, U) ≃+* Algebra.adjoin o (Set.range fun j => x j / x c),
      ∀ s, ((E s : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) = secVal ξ U h s := by
  have hm : ∀ s, secVal ξ U h s ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := fun s =>
    (mem_adjoin_iff hall T hc hU h _).2 ⟨s, rfl⟩
  refine ⟨RingEquiv.ofBijective ((secVal ξ U h).codRestrict _ hm) ⟨fun a b e => ?_, fun r => ?_⟩, fun _ => rfl⟩
  · exact secVal_injective hall T.gen.inj U h (congrArg Subtype.val e)
  · obtain ⟨s, hs⟩ := (mem_adjoin_iff hall T hc hU h r).1 r.2
    exact ⟨s, Subtype.ext hs⟩

variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω']

theorem inChart_map {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} {κ κ' : Type} {x : κ → Ω} {x' : κ' → Ω'} (hall : ∀ q : X, genPt ξ ⤳ q)
    (T : CoordTie ℤ ξ x) (T' : CoordTie ℤ ξ' x') (hd : Dominates ξ' ξ f i) {c : κ} {c' : κ'} (hc : x c ≠ 0)
    (hc' : x' c' ≠ 0) (hi : ∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'))
    (p' : Cpt ξ') (hp' : InChart ξ' x' c' p') : InChart ξ x c ⟨f p'.1, hall _⟩ := by
  obtain ⟨h, hreg, hunit⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd p'
  obtain ⟨d, hd0, hdr⟩ := T.cover ⟨f p'.1, h⟩
  have ha0 : x c / x d ≠ 0 := div_ne_zero hc hd0
  have hinv : (i (x c / x d))⁻¹ ∈ regAt ξ' p' := by
    rw [← map_inv₀, inv_div]
    exact (T'.ring c' hc' _).1 (hi d) p' hp'
  have hu := hunit T'.gen _ (hdr c) ⟨(map_ne_zero i).2 ha0, hreg _ (hdr c), hinv⟩
  refine ⟨hc, fun j => ?_⟩
  have e : x j / x c = x j / x d * (x c / x d)⁻¹ := by
    field_simp
  rw [e]
  exact mul_mem (hdr j) hu.2.2

theorem smooth_chartRing (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (i : Ω₀ →+* Ω) (κ κ' : Type) (x : κ → Ω₀) (x' : κ' → Ω) :
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → CoordTie ℤ ξ x → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → Smooth f → ∀ (c : κ) (c' : κ'), x c ≠ 0 → x' c' ≠ 0 →
    (∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) →
    ∃ φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'),
      (∀ a, ((φ a : Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) : Ω) = i a) ∧ φ.Smooth := by
  intro hall hall' T T' hd hsm c c' hc hc' hi
  obtain ⟨U, hUa, hUm⟩ := T.affine c hc
  obtain ⟨U', hU'a, hU'm⟩ := T'.affine c' hc'
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, inChart_genPt T.gen hc⟩
  have hg' : genPt ξ' ∈ U' := (hU'm _).2 ⟨specializes_rfl, inChart_genPt T'.gen hc'⟩
  have hle : U' ≤ f ⁻¹ᵁ U := by
    intro q hq
    obtain ⟨h, hin⟩ := (hU'm q).1 hq
    exact (hUm (f q)).2 ⟨hall _, inChart_map hall T T' hd hc hc' hi ⟨q, h⟩ hin⟩
  obtain ⟨E, hE⟩ := exists_secEquiv hall T hc hUm hg
  obtain ⟨E', hE'⟩ := exists_secEquiv hall' T' hc' hU'm hg'
  have hs : (f.appLE U U' hle).hom.Smooth := Smooth.smooth_appLE (f := f) hUa hU'a hle
  have hval : ∀ s, secVal ξ' U' hg' ((f.appLE U U' hle).hom s) = i (secVal ξ U hg s) := by
    intro s
    have h2 : genPt ξ' ∈ f ⁻¹ᵁ U := hle hg'
    rw [← secVal_app hd U hg h2 s, ← secVal_res ξ' (homOfLE hle) hg' h2 ((f.app U).hom s)]
    rfl
  refine ⟨(E'.toRingHom.comp (f.appLE U U' hle).hom).comp E.symm.toRingHom, fun a => ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := E.surjective a
    simp only [RingHom.comp_apply]
    have : E.symm.toRingHom (E s) = s := E.symm_apply_apply s
    rw [this]
    exact (hE' _).trans ((hval s).trans (congrArg i (hE s).symm))
  · have hr := RingHom.Smooth.propertyIsLocal.respectsIso
    exact hr.2 _ E.symm (hr.1 _ E' hs)

end GlobalTheory.CompanionTheory.Ar.ChartSmooth
