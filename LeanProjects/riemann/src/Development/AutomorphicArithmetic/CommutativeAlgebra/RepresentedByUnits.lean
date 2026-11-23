import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory

private theorem specOf_prime {B : Type} [CommRing B] {T : Scheme.{0}} (ξ : B →+* Γ(T, ⊤)) (t : T) :
    (show PrimeSpectrum B from specOf ξ t).asIdeal =
      ((show PrimeSpectrum Γ(T, ⊤) from T.toSpecΓ t).asIdeal).comap ξ := by
  rfl

private theorem specOf_mem {B : Type} [CommRing B] (J : Ideal B) (U : (Spec (CommRingCat.of B)).Opens)
    (hU : IsCompl' J U) {T : Scheme.{0}} (ξ : B →+* Γ(T, ⊤)) (hξ : J.map ξ = ⊤) (t : T) : specOf ξ t ∈ U := by
  rw [hU, specOf_prime]
  intro h
  have h1 : J.map ξ ≤ (show PrimeSpectrum Γ(T, ⊤) from T.toSpecΓ t).asIdeal := Ideal.map_le_iff_le_comap.2 h
  rw [hξ] at h1
  exact (show PrimeSpectrum Γ(T, ⊤) from T.toSpecΓ t).isPrime.ne_top (top_le_iff.1 h1)

private theorem specOf_inj {B : Type} [CommRing B] {T : Scheme.{0}} [IsAffine T] {ξ ξ' : B →+* Γ(T, ⊤)}
    (h : specOf ξ = specOf ξ') : ξ = ξ' := by
  have h1 := (cancel_epi T.toSpecΓ).1 h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

private theorem exists_specOf {B : Type} [CommRing B] {T : Scheme.{0}} (f : T ⟶ Spec (CommRingCat.of B)) :
    ∃ ξ : B →+* Γ(T, ⊤), specOf ξ = f := by
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f.appTop).hom, ?_⟩
  rw [specOf, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private theorem map_eq_top {B : Type} [CommRing B] (J : Ideal B) (U : (Spec (CommRingCat.of B)).Opens)
    (hU : IsCompl' J U) {T : Scheme.{0}} [IsAffine T] (ξ : B →+* Γ(T, ⊤)) (h : ∀ t : T, specOf ξ t ∈ U) :
    J.map ξ = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hne
  have hbij : Function.Surjective T.toSpecΓ :=
    (T.toSpecΓ.homeomorph).surjective
  obtain ⟨t, ht⟩ := hbij (show Spec Γ(T, ⊤) from (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(T, ⊤)))
  have h1 := (hU _).1 (h t)
  apply h1
  rw [specOf_prime, ht]
  exact Ideal.map_le_iff_le_comap.1 hJm

private noncomputable def pointsMap {B : Type} [CommRing B] (J : Ideal B) (U : (Spec (CommRingCat.of B)).Opens) (hU : IsCompl' J U)
    (P : PSh) (ψ : ∀ T : Scheme.{0}, P.obj (op T) → (B →+* Γ(T, ⊤)))
    (hnat : ∀ {T T' : Scheme.{0}} (f : T' ⟶ T) (x : P.obj (op T)), ψ T' (P.map f.op x) = f.appTop.hom.comp (ψ T x))
    (htop : ∀ (T : Scheme.{0}) (x : P.obj (op T)), J.map (ψ T x) = ⊤) : P ⟶ yoneda.obj (U : Scheme.{0}) where
  app T := TypeCat.ofHom fun x => IsOpenImmersion.lift U.ι (specOf (ψ T.unop x)) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact specOf_mem J U hU _ (htop T.unop x) t)
  naturality T T' g := by
    ext x
    change IsOpenImmersion.lift U.ι _ _ = g.unop ≫ IsOpenImmersion.lift U.ι _ _
    apply (cancel_mono U.ι).1
    rw [Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, comp_specOf]
    exact congrArg specOf (hnat g.unop x)

theorem represented_by_units :
    ∀ {B : Type} [CommRing B] (J : Ideal B) (U : (Spec (CommRingCat.of B)).Opens), IsCompl' J U → ∀ (P : PSh) (ψ : ∀ T : Scheme.{0}, P.obj (op T) → (B →+* Γ(T, ⊤))), (∀ {T T' : Scheme.{0}} (f : T' ⟶ T) (x : P.obj (op T)), ψ T' (P.map f.op x) = f.appTop.hom.comp (ψ T x)) → (∀ (T : Scheme.{0}) (x : P.obj (op T)), J.map (ψ T x) = ⊤) → (∀ (T : Scheme.{0}) (ξ : B →+* Γ(T, ⊤)), J.map ξ = ⊤ → ∃! x, ψ T x = ξ) → ∃ φ : P ⟶ yoneda.obj (U : Scheme.{0}), (∀ (T : Scheme.{0}) (x : P.obj (op T)), φ.app (op T) x ≫ U.ι = specOf (ψ T x)) ∧ ∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ.app (op T)) := by
  intro B _ J U hU P ψ hnat htop huniq
  have hfac : ∀ (T : Scheme.{0}) (x : P.obj (op T)),
      (pointsMap J U hU P ψ hnat htop).app (op T) x ≫ U.ι = specOf (ψ T x) := fun T x =>
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨pointsMap J U hU P ψ hnat htop, hfac, fun T hT => ⟨fun x y hxy => ?_, fun g => ?_⟩⟩
  · have h1 : specOf (ψ T x) = specOf (ψ T y) := by
      rw [← hfac, ← hfac, hxy]
    exact (huniq T _ (htop T x)).unique rfl (specOf_inj h1).symm
  · obtain ⟨ξ, hξ⟩ := exists_specOf (g ≫ U.ι)
    have hmem : ∀ t : T, specOf ξ t ∈ U := fun t => by
      rw [hξ]
      have h2 : (g ≫ U.ι) t ∈ Set.range U.ι := ⟨(show T ⟶ (U : Scheme.{0}) from g) t, rfl⟩
      rwa [Scheme.Opens.range_ι] at h2
    obtain ⟨x, hx, -⟩ := huniq T ξ (map_eq_top J U hU ξ hmem)
    refine ⟨x, (cancel_mono U.ι).1 ?_⟩
    rw [hfac, hx, hξ]

end UpperTheory
