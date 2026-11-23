import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacteristicPolynomialFreeGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RepresentationBasisLinearIndependentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightCharFreeGeometricStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Xgn.HodgeFreeStalk

abbrev eqv (R : Type) [CommRing R] (d : ℕ) : ((Fin d ⊕ Fin d) → R) ≃ₗ[R] (Fin d → R) × (Fin d → R) :=
  LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin d) R R

noncomputable def hm {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : Germ.FB R d O)
    (a : O) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R :=
  Matrix.fromBlocks (rho B a) 0 (-(bil (B.ad a) 1 1).transpose) (rho B (star a)).transpose

section
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem rhoH_eqv (B : Germ.FB R d O) (a : O) (v : (Fin d ⊕ Fin d) → R) :
    rhoH B a (eqv R d v) = eqv R d ((hm B a).mulVec v) := by
  rw [rhoH_apply, hm, Matrix.fromBlocks_mulVec]
  refine Prod.ext ?_ ?_
  · funext i
    simp [Function.comp_def, LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow]
  · funext i
    simp [Function.comp_def, LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
      Matrix.neg_mulVec, sub_eq_neg_add]

theorem conj_eq (B : Germ.FB R d O) (a : O) :
    (eqv R d).conj (Matrix.toLin' (hm B a)) = rhoH B a := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨v, rfl⟩ := (eqv R d).surjective y
  rw [rhoH_eqv, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply]

theorem charpoly_eq [Nontrivial R] (B : Germ.FB R d O) (a : O) : (rhoH B a).charpoly = (hm B a).charpoly := by
  rw [← conj_eq, LinearEquiv.charpoly_conj, Matrix.charpoly_toLin']

theorem hm_map {R₂ : Type} [CommRing R₂] {f : R →+* R₂} {B : Germ.FB R d O} {B₂ : Germ.FB R₂ d O}
    (h : IsMapOf f B B₂) (a : O) : hm B₂ a = (hm B a).map f := by
  ext (i | i) (j | j) <;> simp [hm, rho, lin, bil, h.act, h.ad, MvPowerSeries.coeff_map]

theorem exists_hom (B : Germ.FB R d O) :
    ∃ ρ : O →+* Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R, ∀ a, ρ a = hm B a := by
  obtain ⟨ρH, hρ⟩ := (GlobalTheory.T.formal_hermitian_action_pairing R d O B).1
  have key : ∀ a, hm B a = LinearMap.toMatrix' ((eqv R d).symm.conj (ρH a)) := fun a => by
    rw [hρ, ← conj_eq, LinearEquiv.conj_symm_conj, LinearMap.toMatrix'_toLin']
  refine ⟨⟨⟨⟨hm B, ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, fun _ => rfl⟩
  · rw [key, map_one, Module.End.one_eq_id, LinearEquiv.conj_id, LinearMap.toMatrix'_id]
  · simp only [key]
    rw [map_mul, Module.End.mul_eq_comp, LinearEquiv.conj_comp, LinearMap.toMatrix'_comp]
  · simp only [key, map_zero]
  · simp only [key, map_add]

end

section
variable {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] {R : Type} [CommRing R] {d : ℕ}

theorem hfree_iff (B : Germ.FB R d (𝓞 E)) (r : ℕ) : HFree B r ↔ ∃ x : Fin r → (Fin d ⊕ Fin d) → R,
    LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      (hm B (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧
    Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      (hm B (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤ := by
  have key : ∀ x : Fin r → (Fin d ⊕ Fin d) → R,
      (LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rhoH B (RingOfIntegers.basis E q.2) (eqv R d (x q.1))) ∧
      Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rhoH B (RingOfIntegers.basis E q.2) (eqv R d (x q.1))) = ⊤) ↔
      (LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        (hm B (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧
      Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        (hm B (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤) := by
    intro x
    have e : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rhoH B (RingOfIntegers.basis E q.2) (eqv R d (x q.1))) = (eqv R d).toLinearMap ∘
        (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
          (hm B (RingOfIntegers.basis E q.2)).mulVec (x q.1)) := by
      funext q
      exact rhoH_eqv _ _ _
    rw [e, LinearMap.linearIndependent_iff _ (eqv R d).ker, Set.range_comp, ← Submodule.map_span,
      Submodule.map_eq_top_iff]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ : ∃ y : Fin r → (Fin d ⊕ Fin d) → R, (fun i => eqv R d (y i)) = x :=
      ⟨fun i => (eqv R d).symm (x i), funext fun i => (eqv R d).apply_symm_apply _⟩
    exact ⟨y, (key y).1 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨fun i => eqv R d (x i), (key x).2 hx⟩

theorem hchar_map [Nontrivial R] {R₂ : Type} [CommRing R₂] [Nontrivial R₂] {f : R →+* R₂} {B : Germ.FB R d (𝓞 E)}
    {B₂ : Germ.FB R₂ d (𝓞 E)} (h : IsMapOf f B B₂) {r : ℕ} (hB : HChar B r) : HChar B₂ r := by
  intro a
  rw [charpoly_eq, hm_map h, Matrix.charpoly_map, ← charpoly_eq, hB a, Polynomial.map_pow, Polynomial.map_map,
    Subsingleton.elim (f.comp (Int.castRingHom R)) (Int.castRingHom R₂)]

theorem hchar_of_map [Nontrivial R] {R₂ : Type} [CommRing R₂] [Nontrivial R₂] {f : R →+* R₂}
    (hf : Function.Injective f) {B : Germ.FB R d (𝓞 E)}
    {B₂ : Germ.FB R₂ d (𝓞 E)} (h : IsMapOf f B B₂) {r : ℕ} (hB : HChar B₂ r) : HChar B r := by
  intro a
  apply Polynomial.map_injective f hf
  rw [charpoly_eq, ← Matrix.charpoly_map, ← hm_map h, ← charpoly_eq, hB a, Polynomial.map_pow, Polynomial.map_map,
    Subsingleton.elim (f.comp (Int.castRingHom R)) (Int.castRingHom R₂)]

theorem hchar_iso [Nontrivial R] {B B₂ : Germ.FB R d (𝓞 E)} {φ ψ : Germ.Pt R 1 d} {lam : Germ.PS R 2 d}
    (h : GlobalTheory.CompanionTheory.Ar.Conj.IsIso B B₂ φ ψ lam) {r : ℕ} (hB : HChar B r) : HChar B₂ r := by
  intro a
  obtain ⟨-, -, hb, -, hc, -⟩ := GlobalTheory.T.formal_isomorphism_transport R d (𝓞 E) B B₂ φ ψ lam h
  have e : (LinearEquiv.ofBijective (transH φ ψ lam) hb).conj (rhoH B₂ a) = rhoH B a := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := (LinearEquiv.ofBijective (transH φ ψ lam) hb).surjective y
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact (LinearMap.congr_fun (hc a) v).symm
  rw [← hB a, ← e, LinearEquiv.charpoly_conj]

theorem hfree_of_map [IsLocalRing R] {k : Type} [Field k] {f : R →+* k} [IsLocalHom f] {B : Germ.FB R d (𝓞 E)}
    {B₂ : Germ.FB k d (𝓞 E)} (h : IsMapOf f B B₂) {r : ℕ} (hB : HFree B₂ r) : HFree B r := by
  obtain ⟨ρ, hρ⟩ := exists_hom B
  have := GlobalTheory.T.representation_basis_linear_independent E R k f (Fin d ⊕ Fin d) r ρ
  simp only [hρ, ← hm_map h] at this
  exact (hfree_iff B r).2 (this ((hfree_iff B₂ r).1 hB))

theorem hfree_char0 [IsLocalRing R] {k : Type} [Field k] [CharZero k] (f : R →+* k) [IsLocalHom f]
    {B : Germ.FB R d (𝓞 E)} {r : ℕ} (hB : HChar B r) : HFree B r := by
  obtain ⟨ρ, hρ⟩ := exists_hom B
  have h1 := GlobalTheory.T.representation_basis_linear_independent E R k f (Fin d ⊕ Fin d) r ρ
  let ρk : 𝓞 E →+* Module.End k ((Fin d ⊕ Fin d) → k) :=
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin d ⊕ Fin d)).toRingEquiv.toRingHom.comp f.mapMatrix).comp ρ
  have hk : ∀ a, ρk a = Matrix.toLin' ((ρ a).map f) := fun a => rfl
  have h2 := GlobalTheory.T.characteristic_polynomial_free_generators E k ((Fin d ⊕ Fin d) → k) r ρk (fun a => by
    rw [hk, Matrix.charpoly_toLin', Matrix.charpoly_map, hρ, ← charpoly_eq, hB a, Polynomial.map_pow,
      Polynomial.map_map, Subsingleton.elim (f.comp (Int.castRingHom R)) (Int.castRingHom k)])
  simp only [hk, Matrix.toLin'_apply] at h2
  have h3 := h1 h2
  simp only [hρ] at h3
  exact (hfree_iff B r).2 h3

end

theorem at_point (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]
    (hs : ∀ a : 𝓞 E, star a = H.bar a) (X : Scheme.{0}) (t : SAB H X) (d r : ℕ) (hP : PowFns t) (z : X)
    (g : GermAt t (S := X.presheaf.stalk z) (X.fromSpecStalk z) d) (hc : HChar g.B r)
    (hF : ∀ p : ℕ, p.Prime → (p : X.residueField z) = 0 → FibPF t z) : HFree g.B r := by
  obtain ⟨p, hp⟩ := CharP.exists (IsLocalRing.ResidueField (X.presheaf.stalk z))
  rcases CharP.char_is_prime_or_zero (IsLocalRing.ResidueField (X.presheaf.stalk z)) p with hpp | rfl
  · have h0 : (p : IsLocalRing.ResidueField (X.presheaf.stalk z)) = 0 := CharP.cast_eq_zero _ p
    obtain ⟨k, _, _, x, rfl, hx⟩ := hF p hpp h0
    let f : X.presheaf.stalk (x (IsLocalRing.closedPoint k)) →+* k := (Scheme.stalkClosedPointTo x).hom
    have : IsLocalHom f := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo x).hom)
    have hpk : (p : k) = 0 := by
      by_contra hne
      have hu : IsUnit (f p) := by rw [map_natCast]; exact Ne.isUnit hne
      have hu' := (isUnit_of_map_unit f _ hu).map (IsLocalRing.residue _)
      rw [map_natCast, h0] at hu'
      exact not_isUnit_zero hu'
    have : Fact p.Prime := ⟨hpp⟩
    have : CharP k p := (CharP.charP_iff_prime_eq_zero hpp).2 hpk
    obtain ⟨g₂, hm₂, -⟩ := GlobalTheory.T.formal_germ_base_change E H hs X t _ k f _ d g
    have e : spMap f ≫ X.fromSpecStalk (x (IsLocalRing.closedPoint k)) = x :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
    have hx' : GeomPF t (spMap f ≫ X.fromSpecStalk (x (IsLocalRing.closedPoint k))) := by
      rw [e]; exact hx
    exact hfree_of_map hm₂ (GlobalTheory.T.height_char_free_geometric E H hs X t hP k p _ hx' d r g₂ (hchar_map hm₂ hc))
  · have := CharP.charP_to_charZero (IsLocalRing.ResidueField (X.presheaf.stalk z))
    exact hfree_char0 (IsLocalRing.residue (X.presheaf.stalk z)) hc

end PositivityTheory.Xgn.HodgeFreeStalk

open PositivityTheory.Xgn.HodgeFreeStalk in
theorem PositivityTheory.Xgn.hodge_free_every_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M), PowFns t → IsCptGen ξ → HChar S.g₀.B r → (∀ (q : Cpt ξ) (p : ℕ), p.Prime → (p : X.residueField q.1) = 0 → FibPF t q.1) → ∀ q : Cpt ξ, HFree (S.g q).B r := by
  intro E _ _ _ H _ hs X t Ω _ _ ξ d r M S hP hξ hc hF q
  exact at_point E H hs X t d r hP q.1 (S.g q)
    (hchar_of_map (hξ.inj q) (S.mapK q) (hchar_iso (S.iso q) hc)) (hF q)
