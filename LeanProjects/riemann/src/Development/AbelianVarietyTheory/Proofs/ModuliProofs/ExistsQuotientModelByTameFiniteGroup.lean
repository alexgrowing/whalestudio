import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianDescentTameQuotientStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotientStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsOpenImmersionQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.QuotModel

theorem injective_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Function.Injective β := by
  obtain ⟨-, -, hfr⟩ := h
  let _ := β.toAlgebra
  exact IsFractionRing.injective O F

theorem mono_spMap {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) : Mono (spMap β) := by
  obtain ⟨-, -, hfr⟩ := h
  let _ := β.toAlgebra
  have : Epi (CommRingCat.ofHom β) := ⟨fun {Z} g₁ g₂ hg => by
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (j := g₁.hom) (k := g₂.hom) ?_
    have e := congrArg CommRingCat.Hom.hom hg
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    exact e⟩
  exact Functor.map_mono Scheme.Spec (CommRingCat.ofHom β).op

theorem mem_range_spMap {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : Function.Injective β) (p : Sp O) :
    p ∈ Set.range (spMap β) ↔ p.asIdeal = ⊥ := by
  have hk : RingHom.ker β = ⊥ := (RingHom.injective_iff_ker_eq_bot β).mp h
  constructor
  · rintro ⟨q, rfl⟩
    have := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    show Ideal.comap β q.asIdeal = ⊥
    rw [hq, ← RingHom.ker_eq_comap_bot, hk]
  · intro hp
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap β ⊥ = p.asIdeal
    rw [hp, ← RingHom.ker_eq_comap_bot, hk]

theorem densePart {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) {X U : Scheme.{0}}
    (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (h₁ : Flat s) (h₂ : IsProjOver s) (h₃ : IsOpenImmersion jQ)
    (h₄ : Dense (Set.range jQ)) :
    IsLocallyNoetherian X ∧ genericPoints X ⊆ Set.range (jQ ≫ pullback.fst _ _ : U ⟶ X) ∧
      ∀ u : U, IsIso ((jQ ≫ pullback.fst _ _ : U ⟶ X).stalkMap u) := by
  obtain ⟨⟨hdom, hded⟩, -, hfr⟩ := h
  let _ := β.toAlgebra
  obtain ⟨hN, -, -, hpre, hfl, hdo, hqc⟩ := GlobalTheory.genericPart_dense_proOpen O F X U s jQ h₁ h₂ h₃ h₄
  obtain ⟨hg, hst, -⟩ := GlobalTheory.densePart_basic X U _ hpre hfl hdo hqc
  exact ⟨hN, hg, hst⟩

private theorem isReduced_of_isNormalScheme' (X : Scheme.{0}) (h : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

end GlobalTheory.QuotModel

open GlobalTheory.QuotModel in

theorem GlobalTheory.Models.exists_quotient_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ν : SABMap t t' r) (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).hom), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsProper t.G.hom → (∀ g, (mu g).φ = (τ g).hom ∧ C.j ≫ (ρ g).hom = (ρ₀ g).hom ≫ C.j ∧ C.m.φ ≫ (τ g).hom = (τ₀ g).hom ≫ C.m.φ ∧ (τ₀ g).hom ≫ ν.φ = ν.φ) → IsQProjOver (C.t.G.hom ≫ C.s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X) g, x ≫ (ρ g).hom = x → pullback.fst C.t.G.hom x ≫ (τ g).hom = pullback.fst C.t.G.hom x) → Good C.t → PushInvertible C.t.G C.t.PP.L → ∃ C' : Cpt c' t' β', Good C'.t ∧ Nonempty (C.Above C' b r ν) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' Γ _ _ C b k r ν ρ₀ τ₀ ρ τ mu hβ hβ' hcomp hfin hrc hr hprop hmu hqp
    htame hin hgood hpush

  have sq : ∀ {S S' : Scheme.{0}} {ta : SAB H S} {tb : SAB H S'} {f : S ⟶ S'} (m : SABMap ta tb f),
      m.φ ≫ tb.G.hom = ta.G.hom ≫ f := fun m => m.cart.1.w
  have sqm : C.m.φ ≫ C.t.G.hom = t.G.hom ≫ C.j := sq C.m

  obtain ⟨X', π, s', jQ, hπ, hπfin, hπs, hnorm, hproj, hflat, hjover, hjopen, hjdense, hjc, hgen⟩ :=
    GlobalTheory.exists_quotient_model_scheme E H U F O c t β Γ C U' F' O' c' β' b k r ρ₀ ρ hβ hβ' hcomp hfin hrc hr
      (fun g => (hmu g).2.1)
  obtain ⟨hN', -, -⟩ := densePart hβ' s' jQ hflat hproj hjopen hjdense
  obtain ⟨-, hgenC, hstC⟩ := densePart hβ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hredX : IsReduced C.X := isReduced_of_isNormalScheme' _ C.normal
  have hgab : genericPoints C.X ⊆ abLocus C.t.G := by
    intro x hx
    obtain ⟨u, rfl⟩ := hgenC hx
    have hu : C.jQ u ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := by
      rw [C.ab_gen]; exact ⟨u, rfl⟩
    exact hu

  obtain ⟨t₁, ν', hν'τ, hgood'⟩ :=
    GlobalTheory.T.exists_semiAbelian_descent_tame_quotient E H Γ O C.X X' ρ π C.t C.s τ mu hπ hπfin hqp ⟨hredX, hgab⟩ (fun g => (hmu g).1) htame hin
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' C.m
  have key : ∀ (f : U ⟶ X') (n : SABMap t t₁ f), f = r ≫ jQ ≫ pullback.fst _ _ →
      ∃ n' : SABMap t t₁ (r ≫ jQ ≫ pullback.fst _ _), n'.φ = n.φ := by
    rintro f n rfl; exact ⟨n, rfl⟩
  obtain ⟨n₂, hn₂⟩ := key _ n hjc.symm

  have hredU : IsReduced U := by
    have : ∀ u : U, _root_.IsReduced (U.presheaf.stalk u) := by
      intro u
      have hI : IsIso ((C.jQ ≫ pullback.fst C.s (spMap β)).stalkMap u) := hstC u
      exact isReduced_of_injective (inv ((C.jQ ≫ pullback.fst C.s (spMap β)).stalkMap u)).hom
        (ConcreteCategory.bijective_of_isIso _).1
    exact isReduced_of_isReduced_stalk U
  have hmono : Mono C.j := by
    have := mono_spMap hβ
    have := C.jQ_open
    dsimp only [Cpt.j]; infer_instance
  have hτ : ∀ g, (τ₀ g).hom ≫ t.G.hom = t.G.hom ≫ (ρ₀ g).hom ∧ (τ₀ g).hom ≫ ν.φ = ν.φ ∧
      (τ₀ g).hom ≫ n₂.φ = n₂.φ := by
    intro g
    obtain ⟨h1, h2, h3, h4⟩ := hmu g
    refine ⟨(cancel_mono C.j).mp ?_, h4, ?_⟩
    · calc ((τ₀ g).hom ≫ t.G.hom) ≫ C.j = ((τ₀ g).hom ≫ C.m.φ) ≫ C.t.G.hom := by
            simp only [Category.assoc]; rw [← sqm]
        _ = (C.m.φ ≫ (mu g).φ) ≫ C.t.G.hom := by rw [← h3, h1]
        _ = C.m.φ ≫ C.t.G.hom ≫ (ρ g).hom := by simp only [Category.assoc]; rw [sq (mu g)]
        _ = t.G.hom ≫ C.j ≫ (ρ g).hom := by rw [← Category.assoc, sqm, Category.assoc]
        _ = (t.G.hom ≫ (ρ₀ g).hom) ≫ C.j := by rw [h2, Category.assoc]
    · rw [hn₂, hn, ← Category.assoc, ← h3, Category.assoc, hν'τ g]
  obtain ⟨m', hm'⟩ := GlobalTheory.T.exists_cmTripleMap_descend_groupQuotient E H Γ U U' X' ρ₀ r t t' t₁ τ₀ ν _ n₂ hr hredU hprop hτ

  have hπsurj : Function.Surjective π := (GlobalTheory.quotient_isIntegral_surjective_orbits Γ C.X X' ρ π hπ).2.1.surj
  have hrsurj : Function.Surjective r := (GlobalTheory.quotient_isIntegral_surjective_orbits Γ U U' ρ₀ r hr).2.1.surj
  have habπ : ∀ x, π x ∈ abLocus t₁.G ↔ x ∈ abLocus C.t.G := fun x =>
    abLocus_pullback abLocusOne t₁.semi ν'.cart.1 x

  have hbint : ∀ p : Sp O, (spMap b p).asIdeal = ⊥ → p.asIdeal = ⊥ := by
    intro p hp
    obtain ⟨⟨hdO, -⟩, -, -⟩ := hβ
    obtain ⟨⟨hdO', -⟩, -, -⟩ := hβ'
    let _ := b.toAlgebra
    have h2 : IsFinite (Spec.map (CommRingCat.ofHom b)) := hfin
    rw [IsFinite.SpecMap_iff] at h2
    have : Module.Finite O' O := h2
    have : Algebra.IsIntegral O' O := inferInstance
    exact Ideal.eq_bot_of_comap_eq_bot (R := O') hp
  have hpre : Function.Injective (pullback.fst s' (spMap β')) := by
    obtain ⟨-, -, hfr'⟩ := hβ'
    let _ := β'.toAlgebra
    have : IsPreimmersion (spMap β') := IsPreimmersion.of_isLocalization (nonZeroDivisors O')
    exact (pullback.fst s' (spMap β')).isEmbedding.injective
  have hab : pullback.fst s' (spMap β') ⁻¹' abLocus t₁.G = Set.range jQ := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, hx⟩ := hπsurj (pullback.fst s' (spMap β') w)
      have hxab : x ∈ abLocus C.t.G := (habπ x).1 (by rw [hx]; exact hw)
      have hs' : (s' (pullback.fst s' (spMap β') w)).asIdeal = ⊥ := by
        have e : s' (pullback.fst s' (spMap β') w) = spMap β' (pullback.snd s' (spMap β') w) := by
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        rw [e]
        exact (mem_range_spMap (injective_of_isDedFrac hβ') _).1 ⟨_, rfl⟩
      have hsx : (C.s x).asIdeal = ⊥ := by
        apply hbint
        have e : spMap b (C.s x) = s' (π x) := by
          rw [← Scheme.Hom.comp_apply, ← hπs, Scheme.Hom.comp_apply]
        rw [e, hx]
        exact hs'
      obtain ⟨q, hq⟩ := (mem_range_spMap (injective_of_isDedFrac hβ) (C.s x)).2 hsx
      obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.s) (g := spMap β) x q hq.symm
      have hz : z ∈ Set.range C.jQ := by
        rw [← C.ab_gen]
        show pullback.fst C.s (spMap β) z ∈ abLocus C.t.G
        rw [hz1]
        exact hxab
      obtain ⟨u, rfl⟩ := hz
      obtain ⟨u', hu'⟩ := (hgen x).2 ⟨u, hz1⟩
      exact ⟨u', hpre (hu'.trans hx)⟩
    · rintro ⟨u', rfl⟩
      obtain ⟨u, rfl⟩ := hrsurj u'
      have e : pullback.fst s' (spMap β') (jQ (r u)) = π (C.j u) := by
        have h5 := congrArg (fun f : U ⟶ X' => f u) hjc
        simpa only [Scheme.Hom.comp_apply] using h5
      show pullback.fst s' (spMap β') (jQ (r u)) ∈ abLocus t₁.G
      rw [e, habπ]
      have hu : C.jQ u ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := by
        rw [C.ab_gen]; exact ⟨u, rfl⟩
      exact hu
  refine ⟨⟨X', s', hnorm, hproj, hflat, jQ, hjover, hjopen, hjdense, t₁, m', hab⟩, hgood' hgood hpush,
    ⟨⟨π, hπs, ?_, ν', hjc.symm, ?_⟩⟩⟩
  · refine MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) _ (pullback.fst s' (spMap b))
      inferInstance ?_
    rw [pullback.lift_fst]
    exact hπfin
  · rw [hm', hn₂, hn]

end
