import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFiniteTorsionSplittingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsAlgClosedFractionFieldStatement
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.IsFractionRingIntO

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.CharUniq

attribute [local instance] Over.cartesianMonoidalCategory

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem exists_restr {T T' : Scheme.{0}} (g : T' ⟶ T) (p : T ⟶ X) (p' : T' ⟶ X) (h : g ≫ p = p') :
    ∃ r : (Over.mk p ⟶ t.G) →* (Over.mk p' ⟶ t.G), ∀ w, (r w).left = g ≫ w.left := by
  let δ : Over.mk p' ⟶ Over.mk p := Over.homMk g h
  exact ⟨{ toFun := fun w => δ ≫ w, map_one' := by simp, map_mul' := fun a b => comp_mul _ _ _ }, fun w => rfl⟩

theorem isFinPart_of_equiv {R L B : Type} [CommRing R] [CommRing L] [CommRing B] [Algebra R B] [Algebra L B]
    (e : R ≃+* L) (he : (algebraMap L B).comp e.toRingHom = algebraMap R B) (x : Sp R ⟶ X) (q : ℕ)
    (u : Over.mk (spMap (algebraMap L B) ≫ spMap e.toRingHom ≫ x) ⟶ t.G)
    (u' : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G) (hu : u'.left = u.left)
    (h : IsFinPart t (spMap e.toRingHom ≫ x) q u) : IsFinPart t x q u' := by
  have he' : (algebraMap R B).comp e.symm.toRingHom = algebraMap L B := by
    rw [← he]; ext a; simp
  have th : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Sp S ⟶ t.G.left),
      Thru t u'.left φ w ↔ Thru t u.left (φ.comp e.symm.toRingHom) w := by
    intro S _ φ w
    rw [hu]
    refine exists_congr fun β => and_congr_left fun _ => ⟨fun a => ?_, fun a => ?_⟩
    · rw [← a, RingHom.comp_assoc, he']
    · rw [← he, ← RingHom.comp_assoc, a]; ext b; simp
  have tr : ∀ (S : Type) [CommRing S] (φ : R →+* S),
      ∃ r : (Over.mk (spMap φ ≫ x) ⟶ t.G) →* (Over.mk (spMap (φ.comp e.symm.toRingHom) ≫ spMap e.toRingHom ≫ x) ⟶ t.G),
        ∀ w, (r w).left = w.left := by
    intro S _ φ
    obtain ⟨r, hr⟩ := exists_restr t (𝟙 _) (spMap φ ≫ x)
      (spMap (φ.comp e.symm.toRingHom) ≫ spMap e.toRingHom ≫ x) (by
        rw [Category.id_comp, ← Category.assoc, spc]
        congr 2; ext b; simp)
    exact ⟨r, fun w => (hr w).trans (Category.id_comp _)⟩
  letI : Algebra R L := e.toRingHom.toAlgebra
  haveI : IsScalarTower R L B := IsScalarTower.of_algebraMap_eq' he.symm
  let e' : R ≃ₐ[R] L := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  haveI := h.finite
  haveI := h.free
  haveI : Module.Finite R L := Module.Finite.equiv e'.toLinearEquiv
  haveI : Module.Free R L := Module.Free.of_equiv e'.toLinearEquiv
  refine ⟨Module.Finite.trans L B, Module.Free.trans (S := L), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := exists_restr t (𝟙 _) (spMap (algebraMap L B) ≫ spMap e.toRingHom ≫ x)
      (spMap (algebraMap R B) ≫ x) (by rw [Category.id_comp, ← Category.assoc, spc, he])
    have : u' = r u := Over.OverMorphism.ext (by rw [hr, hu]; exact (Category.id_comp _).symm)
    rw [this, ← map_pow, h.tors, map_one]
  · intro S _ β β' h1 h2
    refine h.mono S β β' (by rw [← he', ← RingHom.comp_assoc, h1, RingHom.comp_assoc]) (by rw [← hu]; exact h2)
  · intro S _ φ w hw hm
    obtain ⟨r, hr⟩ := tr S φ
    rw [th, ← hr]
    refine h.isOpen S _ (r w) (by rw [← map_pow, hw, map_one]) fun 𝔪 h𝔪 => ?_
    rw [hr]
    exact (th _ _ _).1 (hm 𝔪 h𝔪)
  · intro S _ φ
    obtain ⟨r, hr⟩ := tr S φ
    rw [th, ← hr, map_one]
    exact h.one S _
  · intro S _ φ w w' h1 h2
    obtain ⟨r, hr⟩ := tr S φ
    rw [th, ← hr] at h1 h2 ⊢
    rw [map_mul]
    exact h.mul S _ _ _ h1 h2
  · intro k _ β
    obtain ⟨σ, hσ⟩ := h.sect k β
    refine ⟨e'.symm.toAlgHom.comp (σ.restrictScalars R), hσ.trans ?_⟩
    rw [← he']
    rfl
  · intro b hb
    refine h.inj b fun σ => ?_
    have := hb (e'.symm.toAlgHom.comp (σ.restrictScalars R))
    exact e'.symm.injective (this.trans (map_zero _).symm)

theorem exists_finPart_local [IsLocallyNoetherian X] (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [IsLocalRing R] (x : Sp R ⟶ X) (q : ℕ) (hq : q ≠ 0) (hs : SplitTors t x q) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : Algebra R B₀) (u : Over.mk (spMap (algebraMap R B₀) ≫ x) ⟶ t.G),
      IsFinPart t x q u ∧ ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B]
        (w : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G), w ^ q = 1 → Thru t u.left (algebraMap R B) w.left := by
  obtain ⟨f, B₀, _, _, u, hf, hu, hk⟩ := GlobalTheory.T.exists_local_finite_torsion_splitting E H X t R x q hq hs (IsLocalRing.maximalIdeal R) inferInstance
  have hfu : IsUnit f := by
    by_contra hn
    exact hf hn
  let e : R ≃+* Localization.Away f :=
    (IsLocalization.atUnits R (Submonoid.powers f) (S := Localization.Away f)
      ((Submonoid.powers_le).2 hfu)).toRingEquiv
  have hee : e.toRingHom = algebraMap R (Localization.Away f) := by
    ext a
    exact (IsLocalization.atUnits R (Submonoid.powers f) (S := Localization.Away f)
      ((Submonoid.powers_le).2 hfu)).commutes a
  letI : Algebra R B₀ := ((algebraMap (Localization.Away f) B₀).comp e.toRingHom).toAlgebra
  revert u
  rw [← hee]
  intro u hu hk
  obtain ⟨r, hr⟩ := exists_restr t (𝟙 _) (spMap (algebraMap (Localization.Away f) B₀) ≫ spMap e.toRingHom ≫ x)
    (spMap (algebraMap R B₀) ≫ x) (by rw [Category.id_comp, ← Category.assoc, spc])
  have hr' : (r u).left = u.left := (hr u).trans (Category.id_comp _)
  have hu' := isFinPart_of_equiv t e rfl x q u (r u) hr' hu
  refine ⟨B₀, inferInstance, inferInstance, r u, hu', fun B _ _ _ w hw => hu'.isOpen B _ w hw fun 𝔪 h𝔪 => ?_⟩
  letI := Ideal.Quotient.field 𝔪
  let φ : R →+* B ⧸ 𝔪 := (Ideal.Quotient.mk 𝔪).comp (algebraMap R B)
  have hφ : (φ.comp e.symm.toRingHom).comp e.toRingHom = φ := by ext a; simp
  obtain ⟨s, hs⟩ := exists_restr t (spMap (Ideal.Quotient.mk 𝔪)) (spMap (algebraMap R B) ≫ x)
    (spMap (φ.comp e.symm.toRingHom) ≫ spMap e.toRingHom ≫ x) (by
      rw [← Category.assoc, ← Category.assoc, spc, spc, hφ])
  obtain ⟨β, h1, h2⟩ := hk (B ⧸ 𝔪) (φ.comp e.symm.toRingHom) (by
    rw [hφ]
    have : (𝔪.comap (algebraMap R B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔪
    rw [← IsLocalRing.eq_maximalIdeal this, ← RingHom.comap_ker, Ideal.mk_ker]) (s w)
    (by rw [← map_pow, hw, map_one])
  refine ⟨β, ?_, by rw [hr', h2, hs]⟩
  exact (congrArg (fun z => z.comp e.toRingHom) h1).trans hφ

theorem exists_finPart_int [IsLocallyNoetherian X] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q : ℕ) (hq : q ≠ 0) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : Algebra ↥(intO C) B₀)
      (u : Over.mk (spMap (algebraMap ↥(intO C) B₀) ≫ x) ⟶ t.G),
      IsFinPart t x q u ∧ ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B]
        (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 →
          Thru t u.left (algebraMap ↥(intO C) B) w.left := by
  haveI := GlobalTheory.IntegralPointCheck.valuationRing_intO C
  haveI := GlobalTheory.IntegralPointCheck.isFractionRing_intO C
  haveI : IsAlgClosed (FractionRing ↥(intO C)) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv ↥(intO C) C).symm.toRingEquiv
  exact exists_finPart_local t _ x q hq (GlobalTheory.T.splitTors_algClosed_fraction_field E H X t _ x q hq)

theorem char_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q : ℕ), q ≠ 0 → ∀ c c' : TorsChar t x q, (∀ w : Over.mk (spMap (algebraMap ↥(intO C) ↥(intO C)) ≫ x) ⟶ t.G, w ^ q = 1 → c.χ ↥(intO C) w = c'.χ ↥(intO C) w) → ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c.χ B w = c'.χ B w := by
  intro E _ _ _ H X _ t C _ _ _ _ x q hq c c' h B _ _ _ w hw
  obtain ⟨B₀, _, _, u, hu, hth⟩ := exists_finPart_int t C x q hq
  haveI := hu.finite
  have key : (c.χ B₀ u : B₀) = c'.χ B₀ u := by
    refine sub_eq_zero.1 (hu.inj _ fun σ => ?_)
    obtain ⟨r, hr⟩ := exists_restr t (spMap σ.toRingHom) (spMap (algebraMap ↥(intO C) B₀) ≫ x)
      (spMap (algebraMap ↥(intO C) ↥(intO C)) ≫ x) (by
        rw [← Category.assoc, spc]
        congr 2
        exact RingHom.ext fun a => σ.commutes a)
    rw [map_sub, ← c.nat B₀ _ σ u (r u) hu.tors (hr u), ← c'.nat B₀ _ σ u (r u) hu.tors (hr u),
      h (r u) (by rw [← map_pow, hu.tors, map_one]), sub_self]
  obtain ⟨β, h1, h2⟩ := hth B w hw
  let β' : B₀ →ₐ[↥(intO C)] B := { β with commutes' := fun a => RingHom.congr_fun h1 a }
  refine Units.ext ?_
  rw [c.nat B₀ B β' u w hu.tors h2.symm, c'.nat B₀ B β' u w hu.tors h2.symm, key]

end GlobalTheory.CharUniq
