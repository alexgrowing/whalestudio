import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharEqOfEqOnTorsionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFiniteTorsionSplittingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharacterCocycleDescentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsAlgClosedFractionFieldStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsCharExt

theorem exists_hom_extend {G A : Type} [CommGroup G] [CommGroup A]
    (hA : ∀ n : ℕ, n ≠ 0 → ∀ a : A, ∃ b : A, b ^ n = a) (q : ℕ) (χ : G → A)
    (hχ : ∀ g g', g ^ q = 1 → g' ^ q = 1 → χ (g * g') = χ g * χ g') :
    ∃ κ : G →* A, ∀ g, g ^ q = 1 → κ g = χ g := by
  let T : Subgroup G := (powMonoidHom q : G →* G).ker
  let f : T →* A := MonoidHom.mk' (fun g => χ g) fun g g' => hχ g g' g.2 g'.2
  letI : DivisibleBy (Additive A) ℕ := divisibleByOfSMulRightSurj (Additive A) ℕ fun {n} hn a => by
    obtain ⟨b, hb⟩ := hA n hn a.toMul
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  letI : DivisibleBy (Additive A) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨k, hk⟩ := (Module.Baer.of_divisible (Additive A)).extension_property_addMonoidHom
    (MonoidHom.toAdditive T.subtype) (fun a b h => Subtype.ext h) (MonoidHom.toAdditive f)
  refine ⟨MonoidHom.toAdditive.symm k, fun g hg => ?_⟩
  exact DFunLike.congr_fun hk (Additive.ofMul (⟨g, hg⟩ : T))

section Ring

variable (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]

def intV : ValuationSubring C where
  toSubring := intO C
  mem_or_inv_mem' := fun x => by
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      change ‖x⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h

theorem intO_valuationRing : ValuationRing ↥(intO C) := inferInstanceAs (ValuationRing ↥(intV C))

theorem intO_isFractionRing : IsFractionRing ↥(intO C) C := inferInstanceAs (IsFractionRing ↥(intV C) C)

theorem intO_units_root [IsAlgClosed C] (n : ℕ) (hn : n ≠ 0) (a : (↥(intO C))ˣ) : ∃ b : (↥(intO C))ˣ, b ^ n = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ↥(intO C)) : C) (Nat.pos_of_ne_zero hn)
  have h1 : ‖z‖ ≤ 1 := by
    have h : ‖((a : ↥(intO C)) : C)‖ ≤ 1 := (a : ↥(intO C)).2
    rw [← hz, norm_pow] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hn).1 h
  have h2 : (⟨z, h1⟩ : ↥(intO C)) ^ n = a := Subtype.ext hz
  have h3 : IsUnit (⟨z, h1⟩ : ↥(intO C)) := (isUnit_pow_iff hn).1 (h2 ▸ a.isUnit)
  exact ⟨h3.unit, Units.ext h2⟩

end Ring

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem sp_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def pull {S S' : Scheme.{0}} {a : S ⟶ X} {a' : S' ⟶ X} (g : S' ⟶ S) (h : g ≫ a = a') :
    (Over.mk a ⟶ t.G) →* (Over.mk a' ⟶ t.G) where
  toFun w := (Over.homMk g h : Over.mk a' ⟶ Over.mk a) ≫ w
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

theorem pull_left {S S' : Scheme.{0}} {a : S ⟶ X} {a' : S' ⟶ X} (g : S' ⟶ S) (h : g ≫ a = a')
    (w : Over.mk a ⟶ t.G) : (pull t g h w).left = g ≫ w.left := rfl

theorem exists_char_of_finPart {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    (e : R ≃+* R') (x : Sp R ⟶ X) (q : ℕ) {B : Type} [CommRing B] [Algebra R' B]
    (u : Over.mk (spMap (algebraMap R' B) ≫ spMap (e : R →+* R') ≫ x) ⟶ t.G)
    (hu : IsFinPart t (spMap (e : R →+* R') ≫ x) q u)
    (hall : ∀ (S : Type) [CommRing S] [Algebra R S] [Module.Finite R S]
      (w : Over.mk (spMap (algebraMap R S) ≫ x) ⟶ t.G), w ^ q = 1 →
        Thru t u.left ((algebraMap R S).comp (e.symm : R' →+* R)) w.left)
    (κ : (Over.mk (spMap (algebraMap R R) ≫ x) ⟶ t.G) →* Rˣ) :
    ∃ c : TorsChar t x q, ∀ w, w ^ q = 1 → c.χ R w = κ w := by
  classical
  have he : ∀ (S : Type) [CommRing S] (φ : R →+* S),
      spMap (φ.comp (e.symm : R' →+* R)) ≫ spMap (e : R →+* R') ≫ x = spMap φ ≫ x := fun S _ φ => by
    rw [← Category.assoc, ← sp_comp]
    congr 2
    ext r; simp
  let pt : (B →ₐ[R'] R') → (Over.mk (spMap (algebraMap R R) ≫ x) ⟶ t.G) := fun σ =>
    pull t (spMap ((e.symm : R' →+* R).comp σ.toRingHom)) (by
      rw [← he R, ← Category.assoc, ← sp_comp]
      congr 2
      ext r; simp) u
  have hP : spMap (e.symm : R' →+* R) ≫ spMap (RingHom.id R') ≫ spMap (e : R →+* R') ≫ x =
      spMap (algebraMap R R) ≫ x := by
    rw [← he R, ← Category.assoc, ← sp_comp]
  have hpt : ∀ (σ : B →ₐ[R'] R') (w : Over.mk (spMap (RingHom.id R') ≫ spMap (e : R →+* R') ≫ x) ⟶ t.G),
      spMap σ.toRingHom ≫ u.left = w.left → pt σ = pull t _ hP w := fun σ w h => by
    ext1
    rw [pull_left, pull_left, ← h, sp_comp, Category.assoc]
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.T.torsion_character_cocycle_descent E H X t R' (spMap (e : R →+* R') ≫ x) q B u hu
    (fun σ => Units.map (e : R →* R') (κ (pt σ))) (fun σ σ' σ'' w w' h h' h'' => by
      rw [hpt _ _ h, hpt _ _ h', hpt _ _ h'', map_mul, map_mul, map_mul])
  let χ : ∀ (S : Type) [CommRing S] [Algebra R S] [Module.Finite R S],
      (Over.mk (spMap (algebraMap R S) ≫ x) ⟶ t.G) → Sˣ := fun S _ _ _ w =>
    if h : Thru t u.left ((algebraMap R S).comp (e.symm : R' →+* R)) w.left then
      Units.map (h.choose : B →* S) b else 1
  have hχ : ∀ (S : Type) [CommRing S] [Algebra R S] [Module.Finite R S]
      (w : Over.mk (spMap (algebraMap R S) ≫ x) ⟶ t.G) (β : B →+* S),
      β.comp (algebraMap R' B) = (algebraMap R S).comp (e.symm : R' →+* R) → spMap β ≫ u.left = w.left →
      (χ S w : S) = β b := fun S _ _ _ w β h₁ h₂ => by
    have h : Thru t u.left ((algebraMap R S).comp (e.symm : R' →+* R)) w.left := ⟨β, h₁, h₂⟩
    have h₃ : h.choose = β := hu.mono S _ _ (h.choose_spec.1.trans h₁.symm) (h.choose_spec.2.trans h₂.symm)
    simp only [χ, dif_pos h, h₃]
    rfl
  refine ⟨⟨χ, ?_, ?_⟩, ?_⟩
  · intro S _ _ _ w w' hw hw'
    obtain ⟨β, h₁, h₂⟩ := hall S w hw
    obtain ⟨β', h₁', h₂'⟩ := hall S w' hw'
    obtain ⟨β'', h₁'', h₂''⟩ := hall S (w * w') (by rw [mul_pow, hw, hw', _root_.one_mul])
    have hc : 𝟙 _ ≫ spMap (algebraMap R S) ≫ x =
        spMap ((algebraMap R S).comp (e.symm : R' →+* R)) ≫ spMap (e : R →+* R') ≫ x := by
      rw [he, Category.id_comp]
    ext
    rw [Units.val_mul, hχ S _ β h₁ h₂, hχ S _ β' h₁' h₂', hχ S _ β'' h₁'' h₂'']
    refine hb₂ S _ (pull t _ hc w) (pull t _ hc w') β β' β'' h₁ h₁' h₁'' ?_ ?_ ?_
    · rw [pull_left, Category.id_comp, h₂]
    · rw [pull_left, Category.id_comp, h₂']
    · rw [← map_mul, pull_left, Category.id_comp, h₂'']
  · intro S S' _ _ _ _ _ _ φ w w' hw h
    obtain ⟨β, h₁, h₂⟩ := hall S w hw
    rw [hχ S _ β h₁ h₂, hχ S' w' (φ.toRingHom.comp β) ?_ ?_]
    · rfl
    · rw [RingHom.comp_assoc, h₁]
      ext r; simp
    · rw [sp_comp, Category.assoc, h₂, h]
  · intro w hw
    obtain ⟨β, h₁, h₂⟩ := hall R w hw
    let σ : B →ₐ[R'] R' :=
      { (e : R →+* R').comp β with
        commutes' := fun r => by
          have := RingHom.congr_fun h₁ r
          simp only [RingHom.comp_apply] at this
          simp [this] }
    have h₃ : pt σ = w := by
      ext1
      rw [pull_left, ← h₂]
      congr 2
      ext r; simp [σ]
    ext
    apply e.injective
    refine (congrArg e (hχ R w β h₁ h₂)).trans ((hb₁ σ).trans ?_)
    rw [h₃]; rfl

theorem exists_char [IsLocallyNoetherian X] {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R]
    [IsLocalRing R] [IsAlgClosed (FractionRing R)] (x : Sp R ⟶ X) (q : ℕ) (hq : q ≠ 0)
    (κ : (Over.mk (spMap (algebraMap R R) ≫ x) ⟶ t.G) →* Rˣ) :
    ∃ c : TorsChar t x q, ∀ w, w ^ q = 1 → c.χ R w = κ w := by
  obtain ⟨f, B, _, _, u, hf, hu, hfib⟩ := GlobalTheory.T.exists_local_finite_torsion_splitting E H X t R x q hq (GlobalTheory.T.splitTors_algClosed_fraction_field E H X t R x q hq)
    (IsLocalRing.maximalIdeal R) inferInstance
  have hf' : IsUnit f := by simpa using hf
  let e : R ≃+* Localization.Away f :=
    (IsLocalization.atUnits R (Submonoid.powers f) (S := Localization.Away f)
      (Submonoid.powers_le.2 hf')).toRingEquiv
  have hee : (e : R →+* Localization.Away f) = algebraMap R _ := rfl
  haveI : IsDomain (Localization.Away f) := e.symm.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed (Localization.Away f) := IsIntegrallyClosed.of_equiv e
  refine exists_char_of_finPart t e x q u hu ?_ κ
  intro S _ _ _ w hw
  have hc : 𝟙 _ ≫ spMap (algebraMap R S) ≫ x =
      spMap ((algebraMap R S).comp (e.symm : Localization.Away f →+* R)) ≫
        spMap (algebraMap R (Localization.Away f)) ≫ x := by
    rw [Category.id_comp, ← Category.assoc, ← sp_comp, ← hee]
    congr 2
    ext r; simp
  have h := hu.isOpen S _ (pull t _ hc w) (by rw [← map_pow, hw, map_one]) fun 𝔪 h𝔪 => by
    letI := Ideal.Quotient.field 𝔪
    have hd : spMap (Ideal.Quotient.mk 𝔪) ≫ spMap ((algebraMap R S).comp (e.symm : Localization.Away f →+* R)) ≫
        spMap (algebraMap R (Localization.Away f)) ≫ x =
        spMap ((Ideal.Quotient.mk 𝔪).comp ((algebraMap R S).comp (e.symm : Localization.Away f →+* R))) ≫
        spMap (algebraMap R (Localization.Away f)) ≫ x := by
      rw [sp_comp _ (Ideal.Quotient.mk 𝔪), Category.assoc]
    refine hfib (S ⧸ 𝔪) _ ?_ (pull t _ hd (pull t _ hc w)) (by rw [← map_pow, ← map_pow, hw, map_one, map_one])
    rw [← IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) 𝔪), ← hee]
    ext r
    rw [RingHom.mem_ker, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  rwa [pull_left, Category.id_comp] at h

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q q' : ℕ), q' ≠ 0 → q ∣ q' → ∀ c : TorsChar t x q, ∃ c' : TorsChar t x q', ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c'.χ B w = c.χ B w := by
  intro E _ _ _ H X _ t C _ _ _ _ x q q' hq' hd c
  haveI := intO_valuationRing C
  haveI := intO_isFractionRing C
  haveI : IsIntegrallyClosed ↥(intO C) := inferInstanceAs (IsIntegrallyClosed ↥(intV C))
  haveI : IsAlgClosed (FractionRing ↥(intO C)) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv ↥(intO C) C).symm.toRingEquiv
  obtain ⟨κ, hκ⟩ := exists_hom_extend (intO_units_root C) q (c.χ ↥(intO C)) (c.mul ↥(intO C))
  obtain ⟨c', hc'⟩ := exists_char t x q' hq' κ
  obtain ⟨m, rfl⟩ := hd
  have up : ∀ {M : Type} [Monoid M] (g : M), g ^ q = 1 → g ^ (q * m) = 1 := fun g h => by
    rw [pow_mul, h, one_pow]
  let c'' : TorsChar t x q :=
    ⟨c'.χ, fun B _ _ _ g g' h h' => c'.mul B g g' (up g h) (up g' h'),
      fun B B' _ _ _ _ _ _ φ g g' h h' => c'.nat B B' φ g g' (up g h) h'⟩
  exact ⟨c', GlobalTheory.T.torsionChar_eq_of_eq_on_torsion E H X t C x q (left_ne_zero_of_mul hq') c'' c fun w hw =>
    (hc' w (up w hw)).trans (hκ w hw)⟩

end GlobalTheory.TorsCharExt
