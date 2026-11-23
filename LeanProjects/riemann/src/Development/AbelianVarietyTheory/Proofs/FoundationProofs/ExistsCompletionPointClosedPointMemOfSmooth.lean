import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

section Lift

variable {X S : Scheme.{u}} (f : X ⟶ S)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
variable {X S : Scheme.{u}} (f : X ⟶ S) in

theorem _root_.GlobalTheory.range_subset_opens_of_isLocalRing {B : CommRingCat.{u}} [IsLocalRing B] (s : Spec B ⟶ S)
    {U : S.Opens} (h : s (closedPoint B) ∈ U) : Set.range s ⊆ U := by
  rintro _ ⟨y, rfl⟩
  exact ((specializes_closedPoint y).map s.base.hom.continuous).mem_open U.isOpen h

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
variable {X S : Scheme.{u}} (f : X ⟶ S) in

theorem _root_.GlobalTheory.exists_isAffineOpen_pair (x : X) {O : X.Opens} (hx : x ∈ O) :
    ∃ (U : S.Opens) (V : X.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ V ≤ f ⁻¹ᵁ U ∧ V ≤ O ∧
      x ∈ V := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((O ⊓ f ⁻¹ᵁ U : X.Opens) : Set X) from ⟨hx, hxU⟩) (O ⊓ f ⁻¹ᵁ U).isOpen
  exact ⟨U, V, hU, hV, fun y hy => (hVle hy).2, fun y hy => (hVle hy).1, hxV⟩

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
variable {X S : Scheme.{u}} (f : X ⟶ S) in

theorem _root_.GlobalTheory.exists_lift_of_smooth_of_isAffineOpen [Smooth f] {U : S.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {B C : CommRingCat.{u}}
    (π : B ⟶ C) (s : Spec B ⟶ S) (x₀ : Spec C ⟶ X) (h : x₀ ≫ f = Spec.map π ≫ s)
    (hs : Set.range s ⊆ U) (hx : Set.range x₀ ⊆ V)
    (H : ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A]
      [Algebra R B] [Algebra R C] (π' : B →ₐ[R] C), (∀ b, π' b = π b) →
      ∀ φ : A →ₐ[R] C, ∃ ψ : A →ₐ[R] B, π'.comp ψ = φ) :
    ∃ x : Spec B ⟶ X, Spec.map π ≫ x = x₀ ∧ x ≫ f = s := by
  have hsm : (f.appLE U V hVU).hom.Smooth := HasRingHomProperty.appLE @Smooth f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  have hxV : Set.range x₀.base ⊆ Set.range hV.fromSpec.base := by rw [hV.range_fromSpec]; exact hx
  have hsU : Set.range s.base ⊆ Set.range hU.fromSpec.base := by rw [hU.range_fromSpec]; exact hs
  set a : Γ(X, V) ⟶ C := Spec.preimage (IsOpenImmersion.lift hV.fromSpec x₀ hxV) with ha_def
  set b : Γ(S, U) ⟶ B := Spec.preimage (IsOpenImmersion.lift hU.fromSpec s hsU) with hb_def
  have ha : Spec.map a ≫ hV.fromSpec = x₀ := by
    rw [ha_def, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hb : Spec.map b ≫ hU.fromSpec = s := by
    rw [hb_def, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hab : f.appLE U V hVU ≫ a = b ≫ π := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, hb, reassoc_of% ha, h]
  letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(S, U) B := b.hom.toAlgebra
  letI : Algebra Γ(S, U) C := (b ≫ π).hom.toAlgebra
  haveI : Algebra.Smooth Γ(S, U) Γ(X, V) := hsm
  let π' : B →ₐ[Γ(S, U)] C := { π.hom with commutes' := fun _ => rfl }
  let φ : Γ(X, V) →ₐ[Γ(S, U)] C :=
    { a.hom with commutes' := fun r => congrArg (fun k => k.hom r) hab }
  obtain ⟨ψ, hψ⟩ := H Γ(S, U) Γ(X, V) π' (fun _ => rfl) φ
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← ha]
    congr 2
    ext y
    exact congrArg (fun k => k y) hψ
  · rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, ← Category.assoc,
      ← Spec.map_comp, ← hb]
    congr 2
    ext r
    exact ψ.commutes r

theorem exists_lift_of_smooth_of_henselian [Smooth f] {B C : CommRingCat.{u}} [IsLocalRing B]
    (π : B ⟶ C) (hπ : Function.Surjective π) [HenselianRing B (RingHom.ker π.hom)]
    (s : Spec B ⟶ S) (x₀ : Spec C ⟶ X) (h : x₀ ≫ f = Spec.map π ≫ s) :
    ∃ x : Spec B ⟶ X, Spec.map π ≫ x = x₀ ∧ x ≫ f = s := by
  have : IsLocalRing C :=
    isLocalRing_of_surjective_of_henselian (RingHom.ker π.hom) π.hom hπ fun _ => Iff.rfl
  have : IsLocalHom π.hom := ⟨fun b hb =>
    isUnit_of_isUnit_map_of_henselian (RingHom.ker π.hom) π.hom hπ (fun _ => Iff.rfl) hb⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair f (x₀ (closedPoint C)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (range_subset_opens_of_isLocalRing s ?_) (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (closedPoint C)) = s (Spec.map π (closedPoint C)) :=
      congr($h (closedPoint C))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R A _ _ _ _ _ _ π' hπ' φ
    exact exists_algHom_lift_of_smooth (RingHom.ker π.hom) π'
      (fun c => (hπ c).imp fun b hb => (hπ' b).trans hb) (fun b => by rw [hπ']; rfl) φ

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
variable {X S : Scheme.{u}} (f : X ⟶ S) in

theorem _root_.GlobalTheory.lift_ext_of_unramified [FormallyUnramified f] [LocallyOfFiniteType f]
    {B C : CommRingCat.{u}} (π : B ⟶ C) (hπ : Function.Surjective π)
    (hj : RingHom.ker π.hom ≤ Ideal.jacobson ⊥) {x₁ x₂ : Spec B ⟶ X}
    (h₀ : Spec.map π ≫ x₁ = Spec.map π ≫ x₂) (h : x₁ ≫ f = x₂ ≫ f) : x₁ = x₂ := by
  let g : Spec B ⟶ pullback f f := pullback.lift x₁ x₂ h
  have hg : Spec.map π ≫ g = (Spec.map π ≫ x₁) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp only [g, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [g, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, h₀]
  have hrange : Set.range g.base ⊆ Set.range (pullback.diagonal f).base := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨m, hm, hym⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
    have hkm : RingHom.ker π.hom ≤ m := hj.trans (sInf_le ⟨bot_le, hm⟩)
    haveI := hm.isPrime
    let z : PrimeSpectrum C := ⟨m.map π.hom, Ideal.map_isPrime_of_surjective hπ hkm⟩
    have hz : PrimeSpectrum.comap π.hom z = ⟨m, hm.isPrime⟩ := by
      ext1
      show Ideal.comap π.hom (m.map π.hom) = m
      rw [Ideal.comap_map_of_surjective' _ hπ, sup_eq_left.mpr hkm]
    have hgp : g.base ⟨m, hm.isPrime⟩ ∈ (pullback.diagonal f).opensRange := by
      rw [← hz]
      show (Spec.map π ≫ g).base z ∈ _
      rw [hg]
      exact ⟨_, rfl⟩
    have hsp : y ⤳ ⟨m, hm.isPrime⟩ := (PrimeSpectrum.le_iff_specializes y ⟨m, hm.isPrime⟩).mp hym
    exact (hsp.map g.base.hom.continuous).mem_open (pullback.diagonal f).opensRange.isOpen hgp
  obtain ⟨l, hl⟩ : ∃ l, l ≫ pullback.diagonal f = g :=
    ⟨IsOpenImmersion.lift (pullback.diagonal f) g hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have e₁ : x₁ = l := by
    rw [← pullback.lift_fst x₁ x₂ h]; change g ≫ _ = _; rw [← hl]; simp
  have e₂ : x₂ = l := by
    rw [← pullback.lift_snd x₁ x₂ h]; change g ≫ _ = _; rw [← hl]; simp
  rw [e₁, e₂]

noncomputable def reducePoint {B C : CommRingCat.{u}} (π : B ⟶ C) (s : Spec B ⟶ S)
    (x : {x : Spec B ⟶ X // x ≫ f = s}) : {x₀ : Spec C ⟶ X // x₀ ≫ f = Spec.map π ≫ s} :=
  ⟨Spec.map π ≫ x.1, by rw [Category.assoc, x.2]⟩

section Quotient

variable (B : Type u) [CommRing B] [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
  (s : Spec (.of B) ⟶ S)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
variable {X S : Scheme.{u}} (f : X ⟶ S) in
variable (B : Type u) [CommRing B] [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
  (s : Spec (.of B) ⟶ S) in

theorem _root_.GlobalTheory.reducePoint_quotient_surjective [Smooth f] :
    Function.Surjective (_root_.GlobalTheory.reducePoint f (CommRingCat.ofHom (Ideal.Quotient.mk I)) s) := by
  rintro ⟨x₀, hx₀⟩
  have hker : ∀ b : B, b ∈ I ↔ Ideal.Quotient.mk I b = 0 := fun b =>
    Ideal.Quotient.eq_zero_iff_mem.symm
  haveI : IsLocalRing (B ⧸ I) := _root_.GlobalTheory.isLocalRing_of_surjective_of_henselian I
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hker
  haveI : IsLocalRing (CommRingCat.of (B ⧸ I)) := ‹IsLocalRing (B ⧸ I)›
  have hclosed : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base
      (closedPoint (CommRingCat.of (B ⧸ I))) = closedPoint B := by
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (B ⧸ I)) = maximalIdeal B
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    _root_.GlobalTheory.exists_isAffineOpen_pair f (x₀ (closedPoint (CommRingCat.of (B ⧸ I)))) (O := ⊤) trivial
  have hfx : f (x₀ (closedPoint (CommRingCat.of (B ⧸ I)))) = s (closedPoint B) := by
    change (x₀ ≫ f).base _ = _
    rw [hx₀]
    exact congrArg s.base hclosed
  have hs : Set.range s ⊆ U := _root_.GlobalTheory.range_subset_opens_of_isLocalRing s (hfx ▸ hVU hxV)
  have hx : Set.range x₀ ⊆ V := _root_.GlobalTheory.range_subset_opens_of_isLocalRing x₀ hxV
  obtain ⟨x, hπx, hxf⟩ := _root_.GlobalTheory.exists_lift_of_smooth_of_isAffineOpen f hU hV hVU _ s x₀ hx₀ hs hx
    (fun R A _ _ _ _ _ _ π' hπ' φ =>
      _root_.GlobalTheory.exists_algHom_lift_of_smooth I π'
        (fun c => by
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
          exact ⟨b, hπ' b⟩)
        (fun b => by rw [hπ']; exact hker b) φ)
  exact ⟨⟨x, hxf⟩, Subtype.ext hπx⟩

end Quotient

section Residue

variable (B : Type u) [CommRing B] [HenselianLocalRing B] (s : Spec (.of B) ⟶ S)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
variable {X S : Scheme.{u}} (f : X ⟶ S) in
variable (B : Type u) [CommRing B] [HenselianLocalRing B] (s : Spec (.of B) ⟶ S) in

theorem _root_.GlobalTheory.reducePoint_residue_surjective [Smooth f] :
    Function.Surjective (_root_.GlobalTheory.reducePoint f (CommRingCat.ofHom (residue B)) s) :=
  _root_.GlobalTheory.reducePoint_quotient_surjective f B (maximalIdeal B) s

end Residue

end Lift

section QuasiSection

variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] in

theorem _root_.GlobalTheory.exists_etale_point_of_smooth (B : Type u) [CommRing B] [IsLocalRing B]
    (K : Type*) [Field K] [Algebra B K] [Algebra (ResidueField B) K]
    [IsScalarTower B (ResidueField B) K] [Algebra.IsSeparable (ResidueField B) K] [IsSepClosed K]
    (s : Spec (.of B) ⟶ S) (O : X.Opens) (hO : ∃ x ∈ O, f x = s (closedPoint B)) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra B W) (_ : Algebra.Etale B W) (_ : W →ₐ[B] K)
      (y : Spec (.of W) ⟶ X),
      y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B W)) ≫ s ∧ Set.range y ⊆ O := by
  obtain ⟨x, hxO, hfx⟩ := hO
  obtain ⟨U, V, hU, hV, hVU, hVO, hxV⟩ := _root_.GlobalTheory.exists_isAffineOpen_pair f x hxO
  have hsm := HasRingHomProperty.appLE @Smooth f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  have hsU : Set.range s.base ⊆ Set.range hU.fromSpec.base := by
    rw [hU.range_fromSpec]; exact _root_.GlobalTheory.range_subset_opens_of_isLocalRing s (hfx ▸ hVU hxV)
  set b : Γ(S, U) ⟶ CommRingCat.of B :=
    Spec.preimage (IsOpenImmersion.lift hU.fromSpec s hsU) with hb_def
  have hb : Spec.map b ≫ hU.fromSpec = s := by
    rw [hb_def, Spec.map_preimage, IsOpenImmersion.lift_fac]
  obtain ⟨P, hP⟩ : x ∈ Set.range hV.fromSpec.base := by rw [hV.range_fromSpec]; exact hxV
  have hPm : Ideal.comap (f.appLE U V hVU).hom P.asIdeal = Ideal.comap b.hom (maximalIdeal B) := by
    have e : hU.fromSpec.base ((Spec.map (f.appLE U V hVU)).base P) =
        hU.fromSpec.base ((Spec.map b).base (closedPoint B)) := by
      change (Spec.map (f.appLE U V hVU) ≫ hU.fromSpec).base P = (Spec.map b ≫ hU.fromSpec).base _
      rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, hb]
      change f.base (hV.fromSpec.base P) = _
      rw [hP, hfx]
    exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective e)
  letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(S, U) B := b.hom.toAlgebra
  letI : Algebra Γ(S, U) K := ((algebraMap B K).comp b.hom).toAlgebra
  haveI : IsScalarTower Γ(S, U) B K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Smooth Γ(S, U) Γ(X, V) := hsm
  haveI := P.isPrime
  obtain ⟨φ⟩ := _root_.GlobalTheory.nonempty_algHom_of_smooth_of_isSepClosed (K := K) P.asIdeal (by
    change Ideal.comap (f.appLE U V hVU).hom P.asIdeal = _
    rw [hPm]
    ext r
    change b.hom r ∈ maximalIdeal B ↔ algebraMap B K (b.hom r) = 0
    exact (_root_.GlobalTheory.algebraMap_eq_zero_iff_mem_maximalIdeal (b.hom r)).symm)
  obtain ⟨W, iW, iBW, hE, ψ, ε, hψ, -⟩ := _root_.GlobalTheory.exists_etale_algHom_lift_of_smooth (B := B) (K := K) φ
  refine ⟨W, iW, iBW, hE, ε, Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, ?_, ?_⟩
  · have e : f.appLE U V hVU ≫ CommRingCat.ofHom ψ = b ≫ CommRingCat.ofHom (algebraMap B W) := by
      ext r
      exact congrArg (fun k => k r) hψ
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, ← hb,
      ← Spec.map_comp_assoc, e, Spec.map_comp_assoc]
  · rintro _ ⟨z, rfl⟩
    apply hVO
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact ⟨(Spec.map (CommRingCat.ofHom ψ)).base z, rfl⟩

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] in

theorem _root_.GlobalTheory.range_fst_residue {B : Type u} [CommRing B] [IsLocalRing B] (g : X ⟶ Spec (.of B)) :
    Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (residue B)))) =
      g ⁻¹' {closedPoint B} := by
  rw [Scheme.Pullback.range_fst]
  congr 1
  have key : ∀ z : Spec (.of (ResidueField B)),
      (Spec.map (CommRingCat.ofHom (residue B))).base z = closedPoint B := by
    intro z
    apply PrimeSpectrum.ext
    show Ideal.comap (residue B) z.asIdeal = maximalIdeal B
    haveI := z.isPrime
    rw [Ideal.eq_bot_of_prime z.asIdeal, ← RingHom.ker_eq_comap_bot, ker_residue]
  ext y
  constructor
  · rintro ⟨z, rfl⟩; exact key z
  · rintro rfl; exact ⟨⟨⊥, Ideal.isPrime_bot⟩, key _⟩

end QuasiSection

section Field

end Field

section DiscreteValuation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in

theorem _root_.GlobalTheory.isDiscreteValuationRing_of_etale_of_isLocalHom (V V' : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing V'] [IsLocalRing V'] [Algebra V V']
    [IsLocalHom (algebraMap V V')] [Algebra.Etale V V'] :
    ∃ (_ : IsDomain V') (_ : IsDiscreteValuationRing V'),
      (maximalIdeal V).map (algebraMap V V') = maximalIdeal V' ∧
      Module.FaithfullyFlat V V' ∧
      Module.Finite (ResidueField V) (ResidueField V') ∧
      Algebra.IsSeparable (ResidueField V) (ResidueField V') ∧
      ∃ (_ : Algebra (FractionRing V) (FractionRing V'))
        (_ : IsScalarTower V (FractionRing V) (FractionRing V')),
        Module.Finite (FractionRing V) (FractionRing V') ∧
        Algebra.IsSeparable (FractionRing V) (FractionRing V') := by
  obtain ⟨hD, hR⟩ := _root_.GlobalTheory.exists_isDiscreteValuationRing_of_unramified V V'
  have hF : Module.FaithfullyFlat V V' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap V V') := FaithfulSMul.algebraMap_injective V V'
  haveI : FaithfulSMul V (FractionRing V') := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq V V' (FractionRing V')]
    exact (IsFractionRing.injective V' (FractionRing V')).comp hinj
  letI := FractionRing.liftAlgebra V (FractionRing V')
  haveI := FractionRing.isScalarTower_liftAlgebra V (FractionRing V')
  obtain ⟨hfin, hsep⟩ :=
    _root_.GlobalTheory.finite_and_isSeparable_fractionRing_of_unramified V V' (FractionRing V) (FractionRing V')
  exact ⟨hD, hR, Algebra.FormallyUnramified.map_maximalIdeal, hF, inferInstance, inferInstance,
    _, inferInstance, hfin, hsep⟩

variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]

end DiscreteValuation

section SpecialFibre

variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of V)) [Smooth f]
  (U : (pullback f (Spec.map (CommRingCat.ofHom (residue V)))).Opens)

end SpecialFibre

section Main

end Main

end GlobalTheory
